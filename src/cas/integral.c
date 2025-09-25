/* integral.c
 * PineappleCAS — Antiderivative (indefinite integral) routines
 * - ln/log support: unary OP_LOG(arg) = ln(arg); binary OP_LOG(base,arg) = log_base(arg)
 * - Trig set via sin/cos/tan + quotient/power recognition (tan, sec, csc, cot; sec^2, csc^2; sec*tan, csc*cot)
 * - Direct rule for ∫ sin x cos x dx = 1/2 sin^2 x and avoidance of IBP on pure trig×trig
 * - Robust poly×(sin|cos) IBP with constants factored and bare x as degree 1
 */

#include "integral.h"
#include "cas.h"
#include "identities.h"

/* Provided elsewhere */
void replace_node(pcas_ast_t *dst, pcas_ast_t *src);

/* ---------------- IBP controls ---------------- */
static bool s_ibp_enabled = true;
void integral_set_ibp_enabled(bool on) { s_ibp_enabled = on; }

/* Forward decls so helpers are known before use in expo_linear_coeff */
static bool depends_on_var(pcas_ast_t *e, pcas_ast_t *var);
static inline bool is_const_wrt(pcas_ast_t *e, pcas_ast_t *var);


static int s_ibp_depth = 0;
static const int S_IBP_MAX_DEPTH = 8;

/* ---------------- Helpers --------------------- */

static inline pcas_ast_t *N(int v) { return ast_MakeNumber(num_FromInt(v)); }

static void simp(pcas_ast_t *e) {
    simplify(e, SIMP_NORMALIZE | SIMP_RATIONAL | SIMP_COMMUTATIVE |
                SIMP_EVAL | SIMP_LIKE_TERMS);
}

static bool depends_on_var(pcas_ast_t *e, pcas_ast_t *var) {
    if (!e) return false;
    if (e->type == NODE_SYMBOL) return ast_Compare(e, var);
    if (e->type != NODE_OPERATOR) return false;
    for (pcas_ast_t *ch = ast_ChildGet(e, 0); ch; ch = ch->next) {
        if (depends_on_var(ch, var)) return true;
    }
    return false;
}

/* Try to read expo as linear in `var`.
   - var                => a = 1
   - (num...)*var       => a = product of numeric factors
   - var*(num... )      => same
   - a*var + (numeric)  => same a (affine shift allowed)
   Returns true and sets *a_out to a NUMBER node if successful. */
static bool expo_linear_coeff(pcas_ast_t *expo, pcas_ast_t *var, pcas_ast_t **a_out) {
    if (!expo || !var || !a_out) return false;

    /* direct: expo == var */
    if (expo->type == NODE_SYMBOL && ast_Compare(expo, var)) {
        *a_out = ast_MakeNumber(num_FromInt(1));
        return true;
    }

    /* product case: (num ...)*var (order-insensitive), ONLY numbers and var allowed */
    if (expo->type == NODE_OPERATOR && optype(expo) == OP_MULT) {
        mp_rat acc = num_FromInt(1);
        bool saw_var = false;

        for (pcas_ast_t *ch = ast_ChildGet(expo, 0); ch; ch = ch->next) {
            if (ch->type == NODE_SYMBOL && ast_Compare(ch, var)) {
                if (saw_var) { num_Cleanup(acc); return false; }  /* var must appear once */
                saw_var = true;
            } else if (ch->type == NODE_NUMBER) {
                mp_rat_mul(acc, ch->op.num, acc);
            } else {
                /* some other non-numeric/non-var node => not linear */
                num_Cleanup(acc);
                return false;
            }
        }

        if (saw_var) {
            *a_out = ast_MakeNumber(num_Copy(acc));
            num_Cleanup(acc);
            return true;
        }
        num_Cleanup(acc);
        return false;
    }

    /* sum (affine) case: a*var + b, where b is numeric-only (or absent) */
    if (expo->type == NODE_OPERATOR && optype(expo) == OP_ADD) {
        pcas_ast_t *term_with_var = NULL;

        /* Find exactly one addend containing var (as var or product of numbers*var) */
        for (pcas_ast_t *t = ast_ChildGet(expo, 0); t; t = t->next) {
            bool depends = depends_on_var(t, var);
            if (depends) {
                if (term_with_var) return false; /* more than one linear term => not strictly linear */
                term_with_var = t;
            } else {
                /* require other addends to be numeric-only (constants) */
                if (!is_const_wrt(t, var)) return false;
            }
        }
        if (!term_with_var) return false;

        /* Recurse: extract coefficient from the term-with-var (must be var or numbers*var) */
        return expo_linear_coeff(term_with_var, var, a_out);
    }

    return false;
}


static inline bool is_const_wrt(pcas_ast_t *e, pcas_ast_t *var) {
    return !depends_on_var(e, var);
}

static inline bool is_var_deg1(pcas_ast_t *e, pcas_ast_t *var) {
    return e && e->type == NODE_SYMBOL && ast_Compare(e, var);
}

static bool is_one(pcas_ast_t *e) {
    if (!e || e->type != NODE_NUMBER) return false;
    return mp_rat_compare_value(e->op.num, 1, 1) == 0;
}

static bool is_op(pcas_ast_t *e, OperatorType k) {
    return e && e->type == NODE_OPERATOR && optype(e) == k;
}

/* Exact sin(var) or cos(var)? return child if matches */
static pcas_ast_t *is_sin_of_var(pcas_ast_t *e, pcas_ast_t *var) {
    if (!is_op(e, OP_SIN)) return NULL;
    pcas_ast_t *a = ast_ChildGet(e, 0);
    return (a && a->type == NODE_SYMBOL && ast_Compare(a, var)) ? a : NULL;
}
static pcas_ast_t *is_cos_of_var(pcas_ast_t *e, pcas_ast_t *var) {
    if (!is_op(e, OP_COS)) return NULL;
    pcas_ast_t *a = ast_ChildGet(e, 0);
    return (a && a->type == NODE_SYMBOL && ast_Compare(a, var)) ? a : NULL;
}

/* Detect tan(x) with arg==var (assuming OP_TAN exists) */
static bool is_tan_of_var(pcas_ast_t *e, pcas_ast_t *var) {
    if (!is_op(e, OP_TAN)) return false;
    pcas_ast_t *a = ast_ChildGet(e, 0);
    return a && a->type == NODE_SYMBOL && ast_Compare(a, var);
}

/* Recognize sec/csc/cot using only sin/cos/div/pow:
   sec(x): 1/cos(x)  or  cos(x)^(-1)
   csc(x): 1/sin(x)  or  sin(x)^(-1)
   cot(x): cos(x)/sin(x)
*/
static bool is_sec_of_var(pcas_ast_t *e, pcas_ast_t *var) {
    if (!e) return false;
    if (is_op(e, OP_DIV)) {
        pcas_ast_t *num = ast_ChildGet(e, 0), *den = ast_ChildGet(e, 1);
        if (is_one(num) && is_cos_of_var(den, var)) return true;
    }
    if (is_op(e, OP_POW)) {
        pcas_ast_t *b = ast_ChildGet(e, 0), *p = ast_ChildGet(e, 1);
        if (is_cos_of_var(b, var) && p && p->type == NODE_NUMBER &&
            mp_rat_compare_value(p->op.num, -1, 1) == 0) return true;
    }
    return false;
}
static bool is_csc_of_var(pcas_ast_t *e, pcas_ast_t *var) {
    if (!e) return false;
    if (is_op(e, OP_DIV)) {
        pcas_ast_t *num = ast_ChildGet(e, 0), *den = ast_ChildGet(e, 1);
        if (is_one(num) && is_sin_of_var(den, var)) return true;
    }
    if (is_op(e, OP_POW)) {
        pcas_ast_t *b = ast_ChildGet(e, 0), *p = ast_ChildGet(e, 1);
        if (is_sin_of_var(b, var) && p && p->type == NODE_NUMBER &&
            mp_rat_compare_value(p->op.num, -1, 1) == 0) return true;
    }
    return false;
}
static bool is_cot_of_var(pcas_ast_t *e, pcas_ast_t *var) {
    if (!e || !is_op(e, OP_DIV)) return false;
    pcas_ast_t *num = ast_ChildGet(e, 0), *den = ast_ChildGet(e, 1);
    return is_cos_of_var(num, var) && is_sin_of_var(den, var);
}

/* sec^2 / csc^2 via cos/sin powers or reciprocals */
static bool is_sec2_of_var(pcas_ast_t *e, pcas_ast_t *var) {
    if (!e) return false;
    if (is_op(e, OP_POW)) {
        pcas_ast_t *b = ast_ChildGet(e, 0), *p = ast_ChildGet(e, 1);
        if (is_cos_of_var(b, var) && p && p->type == NODE_NUMBER &&
            mp_rat_compare_value(p->op.num, -2, 1) == 0) return true;
    }
    if (is_op(e, OP_DIV)) {
        pcas_ast_t *num = ast_ChildGet(e, 0), *den = ast_ChildGet(e, 1);
        if (is_one(num) && is_op(den, OP_POW)) {
            pcas_ast_t *db = ast_ChildGet(den, 0), *dp = ast_ChildGet(den,1);
            if (is_cos_of_var(db, var) && dp && dp->type==NODE_NUMBER &&
                mp_rat_compare_value(dp->op.num, 2, 1) == 0) return true;
        }
    }
    return false;
}
static bool is_csc2_of_var(pcas_ast_t *e, pcas_ast_t *var) {
    if (!e) return false;
    if (is_op(e, OP_POW)) {
        pcas_ast_t *b = ast_ChildGet(e, 0), *p = ast_ChildGet(e, 1);
        if (is_sin_of_var(b, var) && p && p->type == NODE_NUMBER &&
            mp_rat_compare_value(p->op.num, -2, 1) == 0) return true;
    }
    if (is_op(e, OP_DIV)) {
        pcas_ast_t *num = ast_ChildGet(e, 0), *den = ast_ChildGet(e, 1);
        if (is_one(num) && is_op(den, OP_POW)) {
            pcas_ast_t *db = ast_ChildGet(den, 0), *dp = ast_ChildGet(den,1);
            if (is_sin_of_var(db, var) && dp && dp->type==NODE_NUMBER &&
                mp_rat_compare_value(dp->op.num, 2, 1) == 0) return true;
        }
    }
    return false;
}

/* Elementary trig antiderivatives (arg expected to be var) */
static pcas_ast_t *int_sin_of(pcas_ast_t *arg) { /* ∫ sin(x) dx = -cos(x) */
    return ast_MakeBinary(OP_MULT, N(-1), ast_MakeUnary(OP_COS, arg));
}
static pcas_ast_t *int_cos_of(pcas_ast_t *arg) { /* ∫ cos(x) dx =  sin(x) */
    return ast_MakeUnary(OP_SIN, arg);
}

/* Return 1 if node is unary natural log ln(arg) with arg==var.
   Return 2 if node is binary log_base(arg) with arg==var and set *base_out=base.
   Return 0 otherwise.
   NOTE: repo convention is child0=base, child1=arg for binary LOG; unary has child0=arg, child1=NULL. */
static int match_log_of_var(pcas_ast_t *e, pcas_ast_t *var, pcas_ast_t **base_out) {
    if (!e || e->type != NODE_OPERATOR || optype(e) != OP_LOG) return 0;

    pcas_ast_t *c0 = ast_ChildGet(e, 0);
    pcas_ast_t *c1 = ast_ChildGet(e, 1);

    if (c1 == NULL) {
        /* unary: LOG(arg) -> ln(arg) */
        pcas_ast_t *arg = c0;
        if (arg && arg->type == NODE_SYMBOL && ast_Compare(arg, var)) {
            if (base_out) *base_out = NULL;
            return 1;
        }
        return 0;
    } else {
        /* binary: LOG(base, arg) */
        pcas_ast_t *base = c0;
        pcas_ast_t *arg  = c1;
        if (arg && arg->type == NODE_SYMBOL && ast_Compare(arg, var)) {
            if (base_out) *base_out = base;
            return 2;
        }
        return 0;
    }
}

/* ∫ ln(x) dx = x ln(x) - x */
static pcas_ast_t *int_ln_of_x(pcas_ast_t *var) {
    pcas_ast_t *lnx  = ast_MakeUnary(OP_LOG, ast_Copy(var));        /* ln(x) */
    pcas_ast_t *xlnx = ast_MakeBinary(OP_MULT, ast_Copy(var), lnx); /* x*ln(x) */
    pcas_ast_t *res  = ast_MakeBinary(OP_ADD, xlnx,
                         ast_MakeBinary(OP_MULT, N(-1), ast_Copy(var)));
    simp(res);
    return res;
}

/* Forward decl of the integrator core. */
static pcas_ast_t *integrate_node(pcas_ast_t *expr, pcas_ast_t *var);

/* ---------------- Targeted IBP: poly(x) * (sin|cos)(x) ---------------- */
static pcas_ast_t *ibp_poly_trig_once(pcas_ast_t *expr, pcas_ast_t *var) {
    if (!expr || !is_op(expr, OP_MULT)) return NULL;

    pcas_ast_t *poly = NULL, *poly_pow = NULL, *trig = NULL;
    pcas_ast_t *const_factor = N(1);

    for (pcas_ast_t *ch = ast_ChildGet(expr, 0); ch; ch = ch->next) {
        bool picked = false;

        if (!poly && is_op(ch, OP_POW)) {
            pcas_ast_t *base = ast_ChildGet(ch, 0);
            pcas_ast_t *expo = ast_ChildGet(ch, 1);
            if (base && expo && base->type == NODE_SYMBOL &&
                ast_Compare(base, var) && expo->type == NODE_NUMBER) {
                poly = ch; poly_pow = expo; picked = true;
            }
        }
        if (!picked && !poly && is_var_deg1(ch, var)) {
            poly = ch; poly_pow = NULL; picked = true;
        }

        if (!picked && !trig && (is_op(ch, OP_SIN) || is_op(ch, OP_COS))) {
            pcas_ast_t *arg = ast_ChildGet(ch, 0);
            if (arg && arg->type == NODE_SYMBOL && ast_Compare(arg, var)) {
                trig = ch; picked = true;
            }
        }

        if (!picked) {
            if (!is_const_wrt(ch, var)) { ast_Cleanup(const_factor); return NULL; }
            const_factor = ast_MakeBinary(OP_MULT, const_factor, ast_Copy(ch));
        }
    }

    if (!poly || !trig) { ast_Cleanup(const_factor); return NULL; }

    int n = 1;
    if (poly_pow) {
        char *nstr = num_ToString(poly_pow->op.num, 24);
        n = (int)strtol(nstr, NULL, 10);
        free(nstr);
        if (n < 1) { ast_Cleanup(const_factor); return NULL; }
    }

    pcas_ast_t *u = ast_Copy(poly);
    pcas_ast_t *v = is_op(trig, OP_SIN)
                    ? int_sin_of(ast_Copy(ast_ChildGet(trig, 0)))
                    : int_cos_of(ast_Copy(ast_ChildGet(trig, 0)));

    pcas_ast_t *du = (n == 1) ? N(1)
                              : ast_MakeBinary(OP_MULT, N(n),
                                  ast_MakeBinary(OP_POW, ast_Copy(var), N(n-1)) );

    pcas_ast_t *uv  = ast_MakeBinary(OP_MULT, ast_Copy(const_factor),
                                     ast_MakeBinary(OP_MULT, u, ast_Copy(v)));
    pcas_ast_t *vdu = ast_MakeBinary(OP_MULT, v, du);

    if (s_ibp_depth >= S_IBP_MAX_DEPTH) {
        simp(uv); ast_Cleanup(vdu); ast_Cleanup(const_factor); return uv;
    }

    s_ibp_depth++;
    pcas_ast_t *rest = integrate_node(ast_MakeBinary(OP_MULT, ast_Copy(const_factor), vdu), var);
    s_ibp_depth--;

    ast_Cleanup(const_factor);

    if (!rest) { ast_Cleanup(uv); return NULL; }

    pcas_ast_t *res = ast_MakeBinary(OP_ADD, uv, ast_MakeBinary(OP_MULT, N(-1), rest));
    simp(res);
    return res;
}

/* ---------------- Special trig handling ---------------- */

/* EXACT product sin(x)*cos(x) (same var) → 1/2 sin^2 x */
static pcas_ast_t *integrate_sin_cos_simple(pcas_ast_t *expr, pcas_ast_t *var) {
    if (!expr || !is_op(expr, OP_MULT)) return NULL;
    pcas_ast_t *a = ast_ChildGet(expr, 0), *b = ast_ChildGet(expr, 1);
    if (!a || !b || a->next) return NULL; /* only two factors */
    if ((is_sin_of_var(a,var) && is_cos_of_var(b,var)) ||
        (is_sin_of_var(b,var) && is_cos_of_var(a,var))) {
        pcas_ast_t *s  = ast_MakeUnary(OP_SIN, ast_Copy(var));
        pcas_ast_t *s2 = ast_MakeBinary(OP_POW, s, N(2));
        pcas_ast_t *res = ast_MakeBinary(OP_DIV, s2, N(2)); /* 1/2 * sin^2(x) */
        simp(res);
        return res;
    }
    return NULL;
}

/* sec*tan and csc*cot in quotient form */
static bool is_sec_times_tan(pcas_ast_t *e, pcas_ast_t *var) {
    if (!e || !is_op(e, OP_MULT)) return false;
    pcas_ast_t *a = ast_ChildGet(e,0), *b = ast_ChildGet(e,1);
    return (is_sec_of_var(a,var) && is_tan_of_var(b,var)) ||
           (is_sec_of_var(b,var) && is_tan_of_var(a,var));
}
static bool is_csc_times_cot(pcas_ast_t *e, pcas_ast_t *var) {
    if (!e || !is_op(e, OP_MULT)) return false;
    pcas_ast_t *a = ast_ChildGet(e,0), *b = ast_ChildGet(e,1);
    return (is_csc_of_var(a,var) && is_cot_of_var(b,var)) ||
           (is_csc_of_var(b,var) && is_cot_of_var(a,var));
}
static pcas_ast_t *integrate_special_trig_product(pcas_ast_t *expr, pcas_ast_t *var) {
    if (!expr || !is_op(expr, OP_MULT)) return NULL;

    /* sin·cos first to avoid recursion crashes */
    pcas_ast_t *sc = integrate_sin_cos_simple(expr, var);
    if (sc) return sc;

    if (is_sec_times_tan(expr, var)) {
        pcas_ast_t *res = ast_MakeBinary(OP_DIV, N(1), ast_MakeUnary(OP_COS, ast_Copy(var))); /* sec */
        simp(res);
        return res;
    }
    if (is_csc_times_cot(expr, var)) {
        pcas_ast_t *csc = ast_MakeBinary(OP_DIV, N(1), ast_MakeUnary(OP_SIN, ast_Copy(var)));
        pcas_ast_t *res = ast_MakeBinary(OP_MULT, N(-1), csc); /* -csc */
        simp(res);
        return res;
    }
    return NULL;
}

/* ---------------- Pieces for common node types --------------------------- */

static pcas_ast_t *integrate_sum(pcas_ast_t *expr, pcas_ast_t *var) {
    pcas_ast_t *sum = ast_MakeOperator(OP_ADD);
    for (pcas_ast_t *ch = ast_ChildGet(expr, 0); ch; ch = ch->next) {
        pcas_ast_t *i = integrate_node(ast_Copy(ch), var);
        if (!i) { ast_Cleanup(sum); return NULL; }
        ast_ChildAppend(sum, i);
    }
    simp(sum);
    return sum;
}
static pcas_ast_t *integrate_power(pcas_ast_t *expr, pcas_ast_t *var) {
    pcas_ast_t *base = ast_ChildGet(expr, 0);
    pcas_ast_t *expo = ast_ChildGet(expr, 1);
    if (!base || !expo) return NULL;

    /* --- e^(a*x [+ b]) : ∫ e^(a x) dx = (1/a) e^(a x) --- */
    if (base->type == NODE_SYMBOL && base->op.symbol == SYM_EULER) {
        pcas_ast_t *a_num = NULL;
        if (expo_linear_coeff(expo, var, &a_num)) {
            /* a_num is number (which may be negative) */
            /* Build coefficient c = 1 / a_num (will be negative if a_num negative) */
            mp_rat c = num_FromInt(1);
            mp_rat_div(c, a_num->op.num, c);

            pcas_ast_t *coef = ast_MakeNumber(c);
            pcas_ast_t *pow  = ast_MakeBinary(OP_POW, ast_Copy(base), ast_Copy(expo));
            pcas_ast_t *res  = ast_MakeBinary(OP_MULT, coef, pow);

            ast_Cleanup(a_num);
            simp(res);
            return res;
        }
    }

    /* fallback: original power-handling (x^n, sec², csc² etc) */
    if (expo->type == NODE_NUMBER && base->type == NODE_SYMBOL && ast_Compare(base, var)) {
        char *nstr = num_ToString(expo->op.num, 24);
        long n = strtol(nstr, NULL, 10);
        free(nstr);
        if (n == -1) return NULL;
        pcas_ast_t *res = ast_MakeBinary(
            OP_DIV,
            ast_MakeBinary(OP_POW, ast_Copy(var), N((int)(n + 1))),
            N((int)(n + 1))
        );
        simp(res);
        return res;
    }
    if (is_sec2_of_var(expr, var)) {
        pcas_ast_t *res = ast_MakeUnary(OP_TAN, ast_Copy(var));
        simp(res);
        return res;
    }
    if (is_csc2_of_var(expr, var)) {
        pcas_ast_t *cot = ast_MakeBinary(OP_DIV, ast_MakeUnary(OP_COS, ast_Copy(var)),
                                         ast_MakeUnary(OP_SIN, ast_Copy(var)));
        pcas_ast_t *res = ast_MakeBinary(OP_MULT, N(-1), cot);
        simp(res);
        return res;
    }

    return NULL;
}


static pcas_ast_t *integrate_product(pcas_ast_t *expr, pcas_ast_t *var) {
    /* Short-circuit common trig×trig to avoid recursion crashes */
    pcas_ast_t *sp = integrate_special_trig_product(expr, var);
    if (sp) return sp;

    /* Targeted poly×(sin|cos) IBP */
    if (s_ibp_enabled) {
        pcas_ast_t *t = ibp_poly_trig_once(expr, var);
        if (t) return t;
    }

    /* If remaining non-constant factors are all trig and >1, skip (avoid loops) */
    int nonconst_count = 0, trig_like_count = 0;
    for (pcas_ast_t *ch = ast_ChildGet(expr,0); ch; ch=ch->next) {
        if (!is_const_wrt(ch, var)) {
            nonconst_count++;
            if (is_op(ch, OP_SIN) || is_op(ch, OP_COS) || is_tan_of_var(ch,var) ||
                is_sec_of_var(ch,var) || is_csc_of_var(ch,var) || is_cot_of_var(ch,var)) {
                trig_like_count++;
            }
        }
    }
    if (nonconst_count >= 2 && trig_like_count == nonconst_count) {
        return NULL; /* let higher-level trig identities handle */
    }

    /* Constant factor extraction (c * f(x) -> c * ∫ f(x) dx) */
    pcas_ast_t *const_factor = N(1);
    pcas_ast_t *rest_factor  = N(1);
    for (pcas_ast_t *ch = ast_ChildGet(expr, 0); ch; ch = ch->next) {
        if (is_const_wrt(ch, var)) {
            const_factor = ast_MakeBinary(OP_MULT, const_factor, ast_Copy(ch));
        } else {
            rest_factor  = ast_MakeBinary(OP_MULT, rest_factor,  ast_Copy(ch));
        }
    }
    simp(const_factor); simp(rest_factor);

    if (is_one(rest_factor)) {
        pcas_ast_t *res = ast_MakeBinary(OP_MULT, const_factor, ast_Copy(var));
        simp(res);
        ast_Cleanup(rest_factor);
        return res;
    }

    pcas_ast_t *inner = integrate_node(rest_factor, var);
    if (inner) {
        pcas_ast_t *res = ast_MakeBinary(OP_MULT, const_factor, inner);
        simp(res);
        return res;
    }

    ast_Cleanup(const_factor);
    return NULL;
}

/* ---------------- Main integrator ---------------- */
static pcas_ast_t *integrate_node(pcas_ast_t *expr, pcas_ast_t *var) {
    if (!expr) return NULL;

    /* Numbers: ∫ c dx = c*x */
    if (expr->type == NODE_NUMBER) {
        pcas_ast_t *res = ast_MakeBinary(OP_MULT, ast_Copy(expr), ast_Copy(var));
        simp(res);
        return res;
    }

    /* Symbols */
    if (expr->type == NODE_SYMBOL) {
        if (ast_Compare(expr, var)) {
            pcas_ast_t *res = ast_MakeBinary(OP_DIV,
                ast_MakeBinary(OP_POW, ast_Copy(var), N(2)), N(2));
            simp(res);
            return res;
        } else {
            pcas_ast_t *res = ast_MakeBinary(OP_MULT, ast_Copy(expr), ast_Copy(var));
            simp(res);
            return res;
        }
    }

    if (expr->type != NODE_OPERATOR) return NULL;

    OperatorType op = optype(expr);

    if (op == OP_ADD)  {
        return integrate_sum(expr, var);
    }
    if (op == OP_MULT) {
        return integrate_product(expr, var);
    }
    if (op == OP_POW)  {
        pcas_ast_t *r = integrate_power(expr, var);
        if (r) return r;
    }

    /* Trig singletons with arg==var */
    if (op == OP_SIN || op == OP_COS || op == OP_TAN) {
        pcas_ast_t *arg = ast_ChildGet(expr, 0);
        if (arg && arg->type == NODE_SYMBOL && ast_Compare(arg, var)) {
            pcas_ast_t *res = NULL;
            switch (op) {
                case OP_SIN: res = int_sin_of(ast_Copy(arg)); break;  /* -cos x */
                case OP_COS: res = int_cos_of(ast_Copy(arg)); break;  /*  sin x */
                case OP_TAN:
                    /* ∫ tan x dx = -ln|cos x|  (represent as -ln(cos x)) */
                    res = ast_MakeBinary(OP_MULT, N(-1),
                          ast_MakeUnary(OP_LOG, ast_MakeUnary(OP_COS, ast_Copy(arg))));
                    break;
                default: break;
            }
            if (res) { simp(res); return res; }
        }
    }

    /* ln/log of the variable x (unary ln or base-log) */
    {
        pcas_ast_t *base = NULL;
        int kind = match_log_of_var(expr, var, &base);
        if (kind == 1) {
            /* unary ln(x) */
            return int_ln_of_x(var);
        } else if (kind == 2) {
            /* If base == e, it's ln(x): avoid dividing by ln(e) */
            if (base && base->type == NODE_SYMBOL && base->op.symbol == SYM_EULER) {
                return int_ln_of_x(var);
            }
            /* General base: (x ln x - x) / ln(a) */
            pcas_ast_t *numer = int_ln_of_x(var);
            pcas_ast_t *den   = ast_MakeUnary(OP_LOG, ast_Copy(base)); /* ln(a) */
            pcas_ast_t *res   = ast_MakeBinary(OP_DIV, numer, den);
            simp(res);
            return res;
        }
    }

    /* sec, csc, cot singletons by pattern */
    if (is_sec_of_var(expr, var)) {
        /* ∫ sec x dx = ln(sec x + tan x) */
        pcas_ast_t *sec = ast_MakeBinary(OP_DIV, N(1), ast_MakeUnary(OP_COS, ast_Copy(var)));
        pcas_ast_t *tan = ast_MakeUnary(OP_TAN, ast_Copy(var));
        pcas_ast_t *sum = ast_MakeBinary(OP_ADD, sec, tan);
        pcas_ast_t *res = ast_MakeUnary(OP_LOG, sum);
        simp(res);
        return res;
    }
    if (is_csc_of_var(expr, var)) {
        /* ∫ csc x dx = ln(csc x - cot x) = ln( 1/sin - cos/sin ) */
        pcas_ast_t *csc = ast_MakeBinary(OP_DIV, N(1), ast_MakeUnary(OP_SIN, ast_Copy(var)));
        pcas_ast_t *cot = ast_MakeBinary(OP_DIV, ast_MakeUnary(OP_COS, ast_Copy(var)),
                                         ast_MakeUnary(OP_SIN, ast_Copy(var)));
        pcas_ast_t *diff = ast_MakeBinary(OP_ADD, csc, ast_MakeBinary(OP_MULT, N(-1), cot));
        pcas_ast_t *res  = ast_MakeUnary(OP_LOG, diff);
        simp(res);
        return res;
    }
    if (is_cot_of_var(expr, var)) {
        /* ∫ cot x dx = ln|sin x| (build ln(sin x)) */
        pcas_ast_t *res = ast_MakeUnary(OP_LOG, ast_MakeUnary(OP_SIN, ast_Copy(var)));
        simp(res);
        return res;
    }

    return NULL;
}

/* Public entry */
void antiderivative(pcas_ast_t *e, pcas_ast_t *respect_to) {
    if (!e || !respect_to) return;
    pcas_ast_t *copy = ast_Copy(e);
    pcas_ast_t *res  = integrate_node(copy, respect_to);
    if (!res) { ast_Cleanup(copy); return; }
    replace_node(e, res);
}
