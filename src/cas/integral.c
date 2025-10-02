#include "integral.h"
#include "cas.h"
#include "identities.h"

/* Provided elsewhere */
void replace_node(pcas_ast_t *dst, pcas_ast_t *src);

/* Forward declaration so callers compile before the definition appears. */
static pcas_ast_t *integrate_node(pcas_ast_t *expr, pcas_ast_t *var);
/* needed because we call it before its definition */
static bool expo_linear_coeff(pcas_ast_t *expo, pcas_ast_t *var, pcas_ast_t **a_out);

/* ---------------- IBP controls ---------------- */
static bool s_ibp_enabled = true;
void integral_set_ibp_enabled(bool on) { s_ibp_enabled = on; }

static int  s_ibp_depth = 0;
static const int S_IBP_MAX_DEPTH = 8;


/* ---------------- Small helpers ---------------- */
static pcas_ast_t *integrate_poly_log_times_trig_linear(pcas_ast_t *expr, pcas_ast_t *var);

/* forward decls */
static pcas_ast_t *integrate_product(pcas_ast_t *expr, pcas_ast_t *var);
static pcas_ast_t *integrate(pcas_ast_t *expr, pcas_ast_t *var);

static bool is_op(pcas_ast_t *e, OperatorType k);

static bool is_ln_of_var_either_node(pcas_ast_t *node, pcas_ast_t *var);

/* ---------------- LOG matching ---------------- */

static bool is_ln_of_var_either_node(pcas_ast_t *node, pcas_ast_t *var) {
    if (!node || !is_op(node, OP_LOG)) return false;
    pcas_ast_t *c0 = ast_ChildGet(node, 0);
    pcas_ast_t *c1 = ast_ChildGet(node, 1);

    if (c1 == NULL) {
        return c0 && c0->type == NODE_SYMBOL && ast_Compare(c0, var);
    } else {
        pcas_ast_t *base = c0;
        pcas_ast_t *arg  = c1;
        if (!(arg && arg->type == NODE_SYMBOL && ast_Compare(arg, var))) return false;
        return base && base->type == NODE_SYMBOL && base->op.symbol == SYM_EULER; /* base == e */
    }
}
static inline pcas_ast_t *N(int v) { return ast_MakeNumber(num_FromInt(v)); }

static void simp(pcas_ast_t *e) {
    simplify(e, SIMP_NORMALIZE | SIMP_RATIONAL | SIMP_COMMUTATIVE |
                SIMP_EVAL | SIMP_LIKE_TERMS);
}

/* Prototypes for helpers used before their definitions */
static bool read_poly_power_of_var(pcas_ast_t *node, pcas_ast_t *var, int *deg_out);
static bool trig_is_linear_arg_of_var(pcas_ast_t *t, pcas_ast_t *var, mp_rat *a_out, OperatorType *which);
static bool expo_linear_coeff(pcas_ast_t *expo, pcas_ast_t *var, pcas_ast_t **a_out);


/* ---------- Small trig helpers ---------- */

/* Integer exponent?  If yes, write it into *out and return true.  */
static bool get_int_exponent(pcas_ast_t *e, int *out) {
    if (!e || e->type != NODE_NUMBER) return false;
    if (!mp_rat_is_integer(e->op.num)) return false;
    mp_small num, den;
    if (mp_rat_to_ints(e->op.num, &num, &den) != MP_OK) return false;
    if (den != 1) return false;
    *out = (int)num;
    return true;
}

/* Make sin^k(x) or cos^k(x) for k>=0 */
static pcas_ast_t *pow_sin(pcas_ast_t *var, int k) {
    if (k == 0) return N(1);
    pcas_ast_t *b = ast_MakeUnary(OP_SIN, ast_Copy(var));
    if (k == 1) return b;
    return ast_MakeBinary(OP_POW, b, N(k));
}
static pcas_ast_t *pow_cos(pcas_ast_t *var, int k) {
    if (k == 0) return N(1);
    pcas_ast_t *b = ast_MakeUnary(OP_COS, ast_Copy(var));
    if (k == 1) return b;
    return ast_MakeBinary(OP_POW, b, N(k));
}

/* C(n,k) as mp_rat */
static mp_rat mp_binom_int(int n, int k) {
    if (k < 0 || k > n) return num_FromInt(0);
    if (k == 0 || k == n) return num_FromInt(1);
    if (k > n - k) k = n - k;

    mp_rat r = num_FromInt(1);
    for (int i = 1; i <= k; ++i) {
        mp_rat mul = num_FromInt(n - k + i);
        mp_rat di  = num_FromInt(i);
        /* r *= (n - k + i) / i */
        mp_rat_div(mul, di, mul);
        mp_rat_mul(r, mul, r);
        num_Cleanup(mul);
        num_Cleanup(di);
    }
    return r;
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

static inline bool is_const_wrt(pcas_ast_t *e, pcas_ast_t *var) {
    return !depends_on_var(e, var);
}

static inline bool is_var_deg1(pcas_ast_t *e, pcas_ast_t *var) {
    return e && e->type == NODE_SYMBOL && ast_Compare(e, var);
}

static bool is_op(pcas_ast_t *e, OperatorType k) {
    return e && e->type == NODE_OPERATOR && optype(e) == k;
}


/* ∫ x^n (ln x)^m dx, with n >= 0 integer, m >= 1 integer.
   Matches products like (const...) * x^n * (ln(x))^m in any order.
   Supports ln(x) represented either as:
     - unary LOG(arg) with arg==var, or
     - binary LOG(base,arg) with base==e (SYM_EULER) and arg==var.
   Finite, non-recursive reduction in m:
     I_{n,0} = x^{n+1}/(n+1),
     I_{n,m} = (x^{n+1}/(n+1)) (ln x)^m - (m/(n+1)) I_{n,m-1}.
   Returns NULL if pattern not matched. */
static pcas_ast_t *integrate_poly_times_log(pcas_ast_t *expr, pcas_ast_t *var) {
    if (!expr || !is_op(expr, OP_MULT)) return NULL;

    /* Collect numeric constant c, polynomial degree n, and log power m. */
    mp_rat c = num_FromInt(1);
    int n = -1;  /* degree of x^n */
    int m = 0;   /* total power of ln(x) */

    for (pcas_ast_t *ch = ast_ChildGet(expr, 0); ch; ch = ch->next) {
        /* numeric factor */
        if (ch->type == NODE_NUMBER) { mp_rat_mul(c, ch->op.num, c); continue; }

        /* x or x^k */
        if (n < 0) {
            int deg;
            if (read_poly_power_of_var(ch, var, &deg)) { n = deg; continue; }
        }

        /* ln(x) or (ln(x))^k; ln can be unary LOG(x) or binary LOG(e,x) */
        if (is_op(ch, OP_LOG)) {
            if (is_ln_of_var_either_node(ch, var)) { m += 1; continue; }
        } else if (is_op(ch, OP_POW)) {
            pcas_ast_t *b = ast_ChildGet(ch, 0), *e = ast_ChildGet(ch, 1);
            if (e && e->type == NODE_NUMBER) {
                int k;
                if (is_op(b, OP_LOG) && is_ln_of_var_either_node(b, var) && get_int_exponent(e, &k) && k >= 1) {
                    m += k;
                    continue;
                }
            }
        }

        /* anything else must be constant wrt var; otherwise we don't match */
        if (!is_const_wrt(ch, var)) { num_Cleanup(c); return NULL; }
    }

    /* need x^n (n >= 0) and (ln x)^m (m >= 1) */
    if (n < 0 || m < 1) { num_Cleanup(c); return NULL; }

    /* n+1 as rational */
    int np1i = n + 1;
    if (np1i == 0) { num_Cleanup(c); return NULL; }
    mp_rat np1 = num_FromInt(np1i);

    /* base_xpow = x^{n+1} (reused) */
    pcas_ast_t *base_xpow = ast_MakeBinary(OP_POW, ast_Copy(var), ast_MakeNumber(num_Copy(np1)));

    /* L = ln(x) (use unary form in the result) */
    pcas_ast_t *L = ast_MakeUnary(OP_LOG, ast_Copy(var));

    /* I_{n,0} = x^{n+1}/(n+1) */
    pcas_ast_t *I_nm = ast_MakeBinary(OP_DIV, ast_Copy(base_xpow), ast_MakeNumber(num_Copy(np1)));

    /* Build up to I_{n,m} iteratively (no recursion) */
    for (int k = 1; k <= m; ++k) {
        pcas_ast_t *Lk = (k == 1) ? ast_Copy(L) : ast_MakeBinary(OP_POW, ast_Copy(L), N(k));

        /* term1 = (x^{n+1}/(n+1)) * L^k */
        pcas_ast_t *term1 = ast_MakeBinary(
            OP_MULT,
            ast_MakeBinary(OP_DIV, ast_Copy(base_xpow), ast_MakeNumber(num_Copy(np1))),
            Lk
        );

        /* term2 = (k/(n+1)) * I_{n,k-1} */
        mp_rat k_over_np1 = num_FromInt(k);
        mp_rat_div(k_over_np1, np1, k_over_np1);
        pcas_ast_t *term2 = ast_MakeBinary(OP_MULT, ast_MakeNumber(k_over_np1), I_nm);

        /* I_{n,k} = term1 - term2 */
        I_nm = ast_MakeBinary(OP_ADD, term1, ast_MakeBinary(OP_MULT, N(-1), term2));
        simp(I_nm);
    }

    /* scale by numeric factor c if needed */
    pcas_ast_t *res = (mp_rat_compare_value(c, 1, 1) != 0)
                        ? ast_MakeBinary(OP_MULT, ast_MakeNumber(c), I_nm)
                        : I_nm;
    simp(res);

    /* cleanup */
    ast_Cleanup(L);
    num_Cleanup(np1);
    return res;
}



/* For t = sin(ax [+ b]) or cos(ax [+ b]), return true and:
   - *a_out = mp_rat copy of 'a' (caller must num_Cleanup),
   - *which = OP_SIN or OP_COS.
   Accept arg of the form a*x, a*x + const, or const + a*x. */
static bool trig_is_linear_arg_of_var(pcas_ast_t *t, pcas_ast_t *var, mp_rat *a_out, OperatorType *which) {
    if (!t || (!is_op(t, OP_SIN) && !is_op(t, OP_COS))) return false;  /* <- parentheses fix */
    pcas_ast_t *arg = ast_ChildGet(t,0);
    if (!arg) return false;

    /* arg == x */
    if (arg->type == NODE_SYMBOL && ast_Compare(arg, var)) {
        if (which) *which = optype(t);
        if (a_out) *a_out = num_FromInt(1);
        return true;
    }

    /* arg == k*x */
    if (is_op(arg, OP_MULT)) {
        mp_rat a = num_FromInt(1);
        bool saw_x = false, ok = true;
        for (pcas_ast_t *ch = ast_ChildGet(arg,0); ch && ok; ch = ch->next) {
            if (ch->type == NODE_SYMBOL && ast_Compare(ch, var)) {
                if (saw_x) ok = false; else saw_x = true;
            } else if (ch->type == NODE_NUMBER) {
                mp_rat_mul(a, ch->op.num, a);
            } else {
                ok = false;
            }
        }
        if (ok && saw_x) {
            if (which) *which = optype(t);
            if (a_out) *a_out = a; else num_Cleanup(a);
            return true;
        }
        num_Cleanup(a);
    }

    /* arg == k*x + c  (or c + k*x) */
    if (is_op(arg, OP_ADD)) {
        pcas_ast_t *term_with_x = NULL;
        for (pcas_ast_t *ch = ast_ChildGet(arg,0); ch; ch = ch->next) {
            if (depends_on_var(ch, var)) {
                if (term_with_x) return false;
                term_with_x = ch;
            } else if (!is_const_wrt(ch, var)) {
                return false;
            }
        }
        if (!term_with_x) return false;

        /* re-check only the linear-in-x term */
        return trig_is_linear_arg_of_var(
            is_op(t, OP_SIN) ? ast_MakeUnary(OP_SIN, ast_Copy(term_with_x))
                             : ast_MakeUnary(OP_COS, ast_Copy(term_with_x)),
            var, a_out, which);
    }

    return false;
}


/* Recognize sqrt-like nodes: sqrt(expr) or expr^(1/2) */
static bool is_sqrt_like(pcas_ast_t *e) {
    if (!e) return false;
    if (is_op(e, OP_ROOT)) {
        pcas_ast_t *deg = ast_ChildGet(e, 0);
        return deg && deg->type==NODE_NUMBER && mp_rat_compare_value(deg->op.num, 2, 1)==0;
    }
    if (is_op(e, OP_POW)) {
        pcas_ast_t *exp = ast_ChildGet(e, 1);
        return exp && exp->type==NODE_NUMBER && mp_rat_compare_value(exp->op.num, 1, 2)==0; /* 1/2 */
    }
    return false;
}

/* From a product denominator, find exactly one x and exactly one sqrt(Q(x)).
   Collect all numeric constants into k_out (defaults to 1).
   Reject any other var-dependent factor. */
static bool split_x_times_root(pcas_ast_t *den, pcas_ast_t *var,
                               pcas_ast_t **root_like_out, mp_rat *k_out) {
    if (!den || !is_op(den, OP_MULT)) return false;

    pcas_ast_t *xnode = NULL, *root_like = NULL;
    mp_rat k = num_FromInt(1);

    for (pcas_ast_t *ch = ast_ChildGet(den, 0); ch; ch = ch->next) {
        if (!xnode && is_var_deg1(ch, var)) { xnode = ch; continue; }
        if (!root_like && is_sqrt_like(ch)) { root_like = ch; continue; }
        if (ch->type == NODE_NUMBER) { mp_rat_mul(k, ch->op.num, k); continue; }
        /* any other var-dependent factor → not our pattern */
        if (!is_const_wrt(ch, var)) { num_Cleanup(k); return false; }
    }

    if (xnode && root_like) {
        if (root_like_out) *root_like_out = root_like;
        if (k_out) *k_out = k; else num_Cleanup(k);
        return true;
    }
    num_Cleanup(k);
    return false;
}


static bool is_one(pcas_ast_t *e) {
    if (!e || e->type != NODE_NUMBER) return false;
    return mp_rat_compare_value(e->op.num, 1, 1) == 0;
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

/* ---------------- sin/cos recognizers ---------------- */

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

/* Detect tan(x) with arg==var */
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

/* sec^2 x recognizer: cos^(-2), 1/(cos^2), or (1/cos)^2 */
static bool is_sec2_of_var(pcas_ast_t *e, pcas_ast_t *var) {
    if (!e) return false;

    /* cos(x)^(-2) */
    if (is_op(e, OP_POW)) {
        pcas_ast_t *b = ast_ChildGet(e, 0), *p = ast_ChildGet(e, 1);
        if (is_cos_of_var(b, var) && p && p->type == NODE_NUMBER &&
            mp_rat_compare_value(p->op.num, -2, 1) == 0) return true;

        /* (1/cos x)^2 */
        if (is_op(b, OP_DIV) && p && p->type == NODE_NUMBER &&
            mp_rat_compare_value(p->op.num, 2, 1) == 0) {
            pcas_ast_t *num = ast_ChildGet(b,0), *den = ast_ChildGet(b,1);
            if (is_one(num) && is_cos_of_var(den, var)) return true;
        }
    }

    /* 1 / (cos x)^2 */
    if (is_op(e, OP_DIV)) {
        pcas_ast_t *num = ast_ChildGet(e, 0), *den = ast_ChildGet(e, 1);
        if (is_one(num) && is_op(den, OP_POW)) {
            pcas_ast_t *db = ast_ChildGet(den, 0), *dp = ast_ChildGet(den, 1);
            if (is_cos_of_var(db, var) && dp && dp->type==NODE_NUMBER &&
                mp_rat_compare_value(dp->op.num, 2, 1) == 0) return true;
        }
    }

    return false;
}

/* csc^2 x recognizer: sin^(-2), 1/(sin^2), or (1/sin)^2 */
static bool is_csc2_of_var(pcas_ast_t *e, pcas_ast_t *var) {
    if (!e) return false;

    /* sin(x)^(-2) */
    if (is_op(e, OP_POW)) {
        pcas_ast_t *b = ast_ChildGet(e, 0), *p = ast_ChildGet(e, 1);
        if (is_sin_of_var(b, var) && p && p->type == NODE_NUMBER &&
            mp_rat_compare_value(p->op.num, -2, 1) == 0) return true;

        /* (1/sin x)^2 */
        if (is_op(b, OP_DIV) && p && p->type == NODE_NUMBER &&
            mp_rat_compare_value(p->op.num, 2, 1) == 0) {
            pcas_ast_t *num = ast_ChildGet(b,0), *den = ast_ChildGet(b,1);
            if (is_one(num) && is_sin_of_var(den, var)) return true;
        }
    }

    /* 1 / (sin x)^2 */
    if (is_op(e, OP_DIV)) {
        pcas_ast_t *num = ast_ChildGet(e, 0), *den = ast_ChildGet(e, 1);
        if (is_one(num) && is_op(den, OP_POW)) {
            pcas_ast_t *db = ast_ChildGet(den, 0), *dp = ast_ChildGet(den, 1);
            if (is_sin_of_var(db, var) && dp && dp->type==NODE_NUMBER &&
                mp_rat_compare_value(dp->op.num, 2, 1) == 0) return true;
        }
    }

    return false;
}

/* ---------------- Elementary trig antiderivatives (arg expected to be var) ---------------- */

static pcas_ast_t *int_sin_of(pcas_ast_t *arg) { /* ∫ sin(x) dx = -cos(x) */
    return ast_MakeBinary(OP_MULT, N(-1), ast_MakeUnary(OP_COS, arg));
}
static pcas_ast_t *int_cos_of(pcas_ast_t *arg) { /* ∫ cos(x) dx =  sin(x) */
    return ast_MakeUnary(OP_SIN, arg);
}

/* ---------------- Trig power helpers ---------------- */

/* EXACT product sin(x)*cos(x) (same var) → 1/2 sin^2 x */
static pcas_ast_t *integrate_sin_cos_simple(pcas_ast_t *expr, pcas_ast_t *var) {
    if (!expr || !is_op(expr, OP_MULT)) return NULL;
    /* only two factors? */
    if (ast_ChildGet(expr, 0) && ast_ChildGet(expr, 0)->next && ast_ChildGet(expr, 0)->next->next)
        return NULL;

    pcas_ast_t *a = ast_ChildGet(expr, 0), *b = ast_ChildGet(expr, 1);
    if (!a || !b) return NULL;

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

/* ∫ sin^n x dx = -(1/n) sin^(n-1)x cos x + (n-1)/n ∫ sin^(n-2) x dx,  n>=2 */
static pcas_ast_t *integrate_sin_power_node(pcas_ast_t *pow, pcas_ast_t *var) {
    if (!is_op(pow, OP_POW)) return NULL;
    pcas_ast_t *base = ast_ChildGet(pow, 0), *exp = ast_ChildGet(pow, 1);
    if (!base || !exp || !is_op(base, OP_SIN)) return NULL;

    pcas_ast_t *arg = ast_ChildGet(base, 0);
    if (!arg || arg->type != NODE_SYMBOL || !ast_Compare(arg, var)) return NULL;

    int n = 0; if (!get_int_exponent(exp, &n) || n < 2) return NULL;

    /* invn = 1/n */
    mp_rat invn = num_FromInt(1), nrat = num_FromInt(n);
    mp_rat_div(invn, nrat, invn);

    mp_rat coef1 = num_FromInt(0);         /* -1/n */
    mp_rat_sub(num_FromInt(0), invn, coef1);

    mp_rat coef2 = num_FromInt(n-1);       /* (n-1)/n */
    mp_rat_div(coef2, nrat, coef2);

    pcas_ast_t *term1 = ast_MakeBinary(OP_MULT,
                       ast_MakeNumber(coef1),
                       ast_MakeBinary(OP_MULT, pow_sin(var, n-1),
                                      ast_MakeUnary(OP_COS, ast_Copy(var))));

    pcas_ast_t *reduced = pow_sin(var, n-2);
    pcas_ast_t *Ired = integrate_node(reduced, var);
    if (!Ired) { num_Cleanup(invn); num_Cleanup(nrat); return NULL; }

    pcas_ast_t *term2 = ast_MakeBinary(OP_MULT, ast_MakeNumber(coef2), Ired);
    pcas_ast_t *res = ast_MakeBinary(OP_ADD, term1, term2);
    simp(res);
    num_Cleanup(nrat);
    return res;
}
/* ∫ cos^n x dx =  (1/n) cos^(n-1)x sin x + (n-1)/n ∫ cos^(n-2) x dx,  n>=2 */
static pcas_ast_t *integrate_cos_power_node(pcas_ast_t *pow, pcas_ast_t *var) {
    if (!is_op(pow, OP_POW)) return NULL;
    pcas_ast_t *base = ast_ChildGet(pow, 0), *exp = ast_ChildGet(pow, 1);
    if (!base || !exp || !is_op(base, OP_COS)) return NULL;

    pcas_ast_t *arg = ast_ChildGet(base, 0);
    if (!arg || arg->type != NODE_SYMBOL || !ast_Compare(arg, var)) return NULL;

    int n = 0; if (!get_int_exponent(exp, &n) || n < 2) return NULL;

    /* invn = 1/n */
    mp_rat invn = num_FromInt(1), nrat = num_FromInt(n);
    mp_rat_div(invn, nrat, invn);

    mp_rat coef1 = num_FromInt(0);         /*  1/n  */
    mp_rat_copy(invn, coef1);

    mp_rat coef2 = num_FromInt(n-1);       /* (n-1)/n */
    mp_rat_div(coef2, nrat, coef2);

    pcas_ast_t *term1 = ast_MakeBinary(OP_MULT,
                       ast_MakeNumber(coef1),
                       ast_MakeBinary(OP_MULT, pow_cos(var, n-1),
                                      ast_MakeUnary(OP_SIN, ast_Copy(var))));

    pcas_ast_t *reduced = pow_cos(var, n-2);
    pcas_ast_t *Ired = integrate_node(reduced, var);
    if (!Ired) { num_Cleanup(nrat); return NULL; }

    pcas_ast_t *term2 = ast_MakeBinary(OP_MULT, ast_MakeNumber(coef2), Ired);
    pcas_ast_t *res = ast_MakeBinary(OP_ADD, term1, term2);
    simp(res);
    num_Cleanup(nrat);
    return res;
}

/* Build F(u) = Σ c_j * u^{p_j}, return its antiderivative Σ c_j/(p_j+1) * u^{p_j+1}.
   u_sym is a *callable* that returns cos(x) or sin(x) AST when passed var. */
static pcas_ast_t *poly_u_antiderivative_and_substitute(
        pcas_ast_t *(*u_of_x)(pcas_ast_t *), pcas_ast_t *var,
        int base_pow, /* >=0 power multiplying the binomial expansion */
        int k,        /* nonnegative integer: (1 ± u^2)^k */
        bool plus,    /* true for (1+u^2)^k, false for (1-u^2)^k */
        bool negate   /* overall minus sign (for du = -sin x dx cases) */) {

    /* Expand (1 ± u^2)^k = Σ C(k,j) (±1)^j u^{2j} */
    pcas_ast_t *sum = N(0);
    for (int j = 0; j <= k; ++j) {
        mp_rat C = mp_binom_int(k, j);
        if (!plus && (j & 1)) { mp_rat_neg(C, C); }           /* (−1)^j */
        int p = base_pow + 2*j;                                /* u^{base_pow} * u^{2j} */
        mp_rat inv = num_FromInt(p+1); mp_rat_recip(inv, inv); /* 1/(p+1) */
        mp_rat coeff = num_FromInt(0); mp_rat_mul(C, inv, coeff);

        pcas_ast_t *u = u_of_x(var);
        /* FIX: when p==0, antiderivative must be u^(p+1) = u (not 1) */
        pcas_ast_t *u_pow = (p == 0)
            ? u
            : ast_MakeBinary(OP_POW, u, N(p+1));

        pcas_ast_t *term = ast_MakeBinary(OP_MULT, ast_MakeNumber(coeff), u_pow);
        sum = ast_MakeBinary(OP_ADD, sum, term);
        num_Cleanup(C); num_Cleanup(inv);
    }
    if (negate) sum = ast_MakeBinary(OP_MULT, N(-1), sum);
    simp(sum);
    return sum;
}

/* Build sec^k(x) as cos(x)^(-k); k>=0 */
static pcas_ast_t *sec_pow_of_var(pcas_ast_t *var, int k) {
    if (k <= 0) return N(1);
    pcas_ast_t *cosx = ast_MakeUnary(OP_COS, ast_Copy(var));
    return ast_MakeBinary(OP_POW, cosx, N(-k));
}

/* ∫ sec^n x dx by reduction:
   I_n = (1/(n-1)) sec^{n-2} x tan x + ((n-2)/(n-1)) I_{n-2},  n>=2
   Base: I_1 = ln|sec x + tan x|, I_0 = x
*/
static pcas_ast_t *integrate_sec_power_reduction(int n, pcas_ast_t *var) {
    if (n <= 0) {
        pcas_ast_t *res = ast_Copy(var); simp(res); return res;                  /* ∫1 dx = x */
    }
    if (n == 1) {
        pcas_ast_t *sec = ast_MakeBinary(OP_DIV, N(1), ast_MakeUnary(OP_COS, ast_Copy(var)));
        pcas_ast_t *tan = ast_MakeUnary(OP_TAN, ast_Copy(var));
        pcas_ast_t *sum = ast_MakeBinary(OP_ADD, sec, tan);
        pcas_ast_t *res = ast_MakeUnary(OP_LOG, sum); simp(res); return res;    /* ln(sec+tan) */
    }

    mp_rat denom = num_FromInt(n-1);
    mp_rat c1 = num_FromInt(1); mp_rat_div(c1, denom, c1);                      /* 1/(n-1) */
    mp_rat c2 = num_FromInt(n-2); mp_rat_div(c2, denom, c2);                    /* (n-2)/(n-1) */

    pcas_ast_t *term1 = ast_MakeBinary(OP_MULT,
        ast_MakeNumber(c1),
        ast_MakeBinary(OP_MULT, sec_pow_of_var(var, n-2), ast_MakeUnary(OP_TAN, ast_Copy(var))));

    pcas_ast_t *Iprev = integrate_sec_power_reduction(n-2, var);
    pcas_ast_t *term2 = ast_MakeBinary(OP_MULT, ast_MakeNumber(c2), Iprev);

    pcas_ast_t *res = ast_MakeBinary(OP_ADD, term1, term2);
    simp(res);
    return res;
}


static pcas_ast_t *make_cos_of_var(pcas_ast_t *v) { return ast_MakeUnary(OP_COS, ast_Copy(v)); }
static pcas_ast_t *make_sin_of_var(pcas_ast_t *v) { return ast_MakeUnary(OP_SIN, ast_Copy(v)); }

/* Handle ∫ sin^m x cos^n x dx with integer m,n >=0, for (m odd) OR (n odd).
   - If m odd:  write sin^m = sin * (sin^2)^((m-1)/2) = sin * (1 - cos^2)^((m-1)/2), u=cos x, du = -sin x dx
   - If n odd:  write cos^n = cos * (cos^2)^((n-1)/2) = cos * (1 - sin^2)^((n-1)/2), u=sin x, du =  cos x dx
*/
static pcas_ast_t *integrate_sin_cos_product(pcas_ast_t *expr, pcas_ast_t *var) {
    if (!is_op(expr, OP_MULT)) return NULL;

    /* detect exact shape sin^m * cos^n (order-insensitive, only integer powers) */
    int m = 0, n = 0;
    pcas_ast_t *sin_pow = NULL, *cos_pow = NULL;

    for (pcas_ast_t *ch = ast_ChildGet(expr,0); ch; ch = ch->next) {
        if (is_op(ch, OP_POW)) {
            pcas_ast_t *b = ast_ChildGet(ch,0), *e = ast_ChildGet(ch,1);
            int k;
            if (is_op(b, OP_SIN)) {
                pcas_ast_t *a = ast_ChildGet(b,0);
                if (a && a->type==NODE_SYMBOL && ast_Compare(a,var) && get_int_exponent(e, &k) && k>=0) {
                    m += k; sin_pow = ch; continue;
                }
            } else if (is_op(b, OP_COS)) {
                pcas_ast_t *a = ast_ChildGet(b,0);
                if (a && a->type==NODE_SYMBOL && ast_Compare(a,var) && get_int_exponent(e, &k) && k>=0) {
                    n += k; cos_pow = ch; continue;
                }
            }
        } else if (is_op(ch, OP_SIN)) {
            pcas_ast_t *a = ast_ChildGet(ch,0);
            if (a && a->type==NODE_SYMBOL && ast_Compare(a,var)) { m += 1; continue; }
        } else if (is_op(ch, OP_COS)) {
            pcas_ast_t *a = ast_ChildGet(ch,0);
            if (a && a->type==NODE_SYMBOL && ast_Compare(a,var)) { n += 1; continue; }
        } else if (ch->type == NODE_NUMBER) {
            /* numeric factor ok */
            continue;
        } else {
            return NULL; /* other stuff present -> not this pattern */
        }
    }

    /* silence “set but not used” (kept for potential future use) */
    (void)sin_pow;
    (void)cos_pow;

    if (m<0 || n<0) return NULL;
    if ((m & 1) == 1) {
        /* m odd: peel one sin, expand (1 - cos^2)^k * cos^n and integrate in u=cos, add minus sign */
        int k = (m-1)/2;
        return poly_u_antiderivative_and_substitute(make_cos_of_var, var, /*base_pow=*/n, k, /*plus=*/false, /*negate=*/true);
    }
    if ((n & 1) == 1) {
        /* n odd: peel one cos, expand (1 - sin^2)^k * sin^m and integrate in u=sin */
        int k = (n-1)/2;
        return poly_u_antiderivative_and_substitute(make_sin_of_var, var, /*base_pow=*/m, k, /*plus=*/false, /*negate=*/false);
    }

    return NULL; /* even-even not handled here (leave to other logic/IBP) */
}
/* tan^m x * sec^n x:
   - if n even (>=2): u = tan x, du = sec^2 x dx  → polynomial in u
   - if n odd  and m even: expand tan^m = (sec^2-1)^{m/2}, integrate each sec^P by reduction
*/
static pcas_ast_t *integrate_tan_sec_product(pcas_ast_t *expr, pcas_ast_t *var) {
    if (!is_op(expr, OP_MULT)) return NULL;

    int m = 0, n = 0;
    mp_rat const_fac = num_FromInt(1);

    /* Parse and count m (tan power) and n (sec power) allowing:
       tan, tan^k, 1/cos, (cos)^(-k), and numeric constants. */
    for (pcas_ast_t *ch = ast_ChildGet(expr,0); ch; ch = ch->next) {
        if (is_op(ch, OP_POW)) {
            pcas_ast_t *b = ast_ChildGet(ch,0), *e = ast_ChildGet(ch,1);
            int k;
            if (is_op(b, OP_TAN)) {
                pcas_ast_t *a = ast_ChildGet(b,0);
                if (!(a && a->type==NODE_SYMBOL && ast_Compare(a,var) && get_int_exponent(e,&k) && k>=0)) return NULL;
                m += k; continue;
            }
            if (is_op(b, OP_COS)) { /* cos^p => sec^{-p} when p negative */
                pcas_ast_t *a = ast_ChildGet(b,0);
                if (!(a && a->type==NODE_SYMBOL && ast_Compare(a,var) && e && e->type==NODE_NUMBER && mp_rat_is_integer(e->op.num))) return NULL;
                mp_small num, den;
                if (mp_rat_to_ints(e->op.num, &num, &den) != MP_OK || den != 1) return NULL;
                if (num < 0) { n += (int)(-num); continue; }     /* cos^{-q} = sec^q */
                if (num == 0) { /* cos^0 = 1 */ continue; }
                /* positive cos power present => not tan^m sec^n canonical; bail */
                return NULL;
            }
            if (is_const_wrt(ch, var) && ch->type==NODE_NUMBER) { mp_rat_mul(const_fac, ch->op.num, const_fac); continue; }
            return NULL;
        } else if (is_op(ch, OP_TAN)) {
            pcas_ast_t *a = ast_ChildGet(ch,0);
            if (!(a && a->type==NODE_SYMBOL && ast_Compare(a,var))) return NULL;
            m += 1; continue;
        } else if (is_sec_of_var(ch, var)) {
            n += 1; continue; /* 1/cos */
        } else if (is_op(ch, OP_DIV)) {
            /* 1 / (cos x)^k */
            pcas_ast_t *num = ast_ChildGet(ch,0), *den = ast_ChildGet(ch,1);
            if (is_one(num) && is_op(den, OP_POW)) {
                pcas_ast_t *db = ast_ChildGet(den,0), *dp = ast_ChildGet(den,1);
                int k;
                if (is_op(db, OP_COS)) {
                    pcas_ast_t *a = ast_ChildGet(db,0);
                    if (a && a->type==NODE_SYMBOL && ast_Compare(a,var) && get_int_exponent(dp,&k) && k>=1) { n += k; continue; }
                }
            }
            if (is_const_wrt(ch, var) && ch->type==NODE_NUMBER) { mp_rat_mul(const_fac, ch->op.num, const_fac); continue; }
            return NULL;
        } else if (ch->type == NODE_NUMBER) {
            mp_rat_mul(const_fac, ch->op.num, const_fac); continue;
        } else {
            return NULL;
        }
    }

    if (n >= 2 && (n % 2) == 0) {
        /* === n even path (existing): u = tan x; sec^{n-2} becomes (1+u^2)^{k} === */
        int k = n/2 - 1;
        pcas_ast_t *sum = N(0);
        for (int j = 0; j <= k; ++j) {
            mp_rat C = mp_binom_int(k, j);            /* C(k,j) */
            int p = m + 2*j;
            mp_rat inv = num_FromInt(p+1); mp_rat_recip(inv, inv); /* 1/(p+1) */
            mp_rat coeff = num_FromInt(0); mp_rat_mul(C, inv, coeff);

            pcas_ast_t *u = ast_MakeUnary(OP_TAN, ast_Copy(var));
            pcas_ast_t *u_pow = (p==0) ? u : ast_MakeBinary(OP_POW, u, N(p+1));
            pcas_ast_t *term = ast_MakeBinary(OP_MULT, ast_MakeNumber(coeff), u_pow);
            sum = ast_MakeBinary(OP_ADD, sum, term);
            num_Cleanup(C); num_Cleanup(inv);
        }
        if (mp_rat_compare_value(const_fac,1,1)!=0)
            sum = ast_MakeBinary(OP_MULT, ast_MakeNumber(const_fac), sum);
        simp(sum);
        return sum;
    }

    /* === NEW: n odd & m even path: expand tan^m = (sec^2 - 1)^{m/2}; integrate sec^P via reduction === */
    if ((n % 2) == 1 && (m % 2) == 0) {
        int s = m/2;
        pcas_ast_t *sum = N(0);
        for (int j = 0; j <= s; ++j) {
            mp_rat C = mp_binom_int(s, j);            /* C(s,j) */
            /* (sec^2 - 1)^s = Σ_j C(s,j) * sec^{2j} * (-1)^{s-j} */
            if (((s - j) & 1) == 1) { mp_rat_neg(C, C); }
            int power = n + 2*j;                      /* sec^{n + 2j} */
            pcas_ast_t *Ij = integrate_sec_power_reduction(power, var);
            if (!Ij) { num_Cleanup(C); ast_Cleanup(sum); return NULL; }
            pcas_ast_t *term = ast_MakeBinary(OP_MULT, ast_MakeNumber(C), Ij);
            sum = ast_MakeBinary(OP_ADD, sum, term);
        }
        if (mp_rat_compare_value(const_fac,1,1)!=0)
            sum = ast_MakeBinary(OP_MULT, ast_MakeNumber(const_fac), sum);
        simp(sum);
        return sum;
    }

    return NULL; /* other (rarer) cases not handled here */
}



/* ---------------- Power helpers ---------------- */

/* x^n (n could be fractional but ≠ -1): (x^(n+1))/(n+1) */
static pcas_ast_t *integrate_x_power_any(pcas_ast_t *expr, pcas_ast_t *var) {
    if (!expr || !is_op(expr, OP_POW)) return NULL;
    pcas_ast_t *base = ast_ChildGet(expr,0), *expo = ast_ChildGet(expr,1);
    if (!base || !expo) return NULL;
    if (!(base->type == NODE_SYMBOL && ast_Compare(base, var))) return NULL;
    if (expo->type != NODE_NUMBER) return NULL;

    if (mp_rat_compare_value(expo->op.num, -1, 1) == 0) return NULL;

    /* n+1 */
    mp_rat np1 = num_Copy(expo->op.num);
    mp_rat_add(np1, num_FromInt(1), np1);

    pcas_ast_t *res = ast_MakeBinary(OP_DIV,
                     ast_MakeBinary(OP_POW, ast_Copy(var), ast_MakeNumber(num_Copy(np1))),
                     ast_MakeNumber(np1));
    simp(res);
    return res;
}

/* ∫ e^{a x} sin(b x) dx  and  ∫ e^{a x} cos(b x) dx  with linear args.
   Closed forms that avoid cyclic IBP:
     ∫ e^{ax} sin(bx) dx = e^{ax}(a sin(bx) - b cos(bx)) / (a^2 + b^2)
     ∫ e^{ax} cos(bx) dx = e^{ax}(a cos(bx) + b sin(bx)) / (a^2 + b^2)
   Accepts exponent a*x[+c] and trig b*x[+d]. */
static pcas_ast_t *integrate_exp_times_trig_linear(pcas_ast_t *expr, pcas_ast_t *var) {
    if (!expr || !is_op(expr, OP_MULT)) return NULL;

    pcas_ast_t *exp = NULL, *tr = NULL;
    mp_rat c = num_FromInt(1);

    /* find e^(...) and sin/cos(...); gather numeric constants */
    for (pcas_ast_t *ch = ast_ChildGet(expr,0); ch; ch = ch->next) {
        if (!exp && is_op(ch, OP_POW)) {
            pcas_ast_t *b = ast_ChildGet(ch,0), *e = ast_ChildGet(ch,1);
            if (b && b->type==NODE_SYMBOL && b->op.symbol==SYM_EULER && e) { exp = ch; continue; }
        }
        if (!tr && (is_op(ch, OP_SIN) || is_op(ch, OP_COS))) { tr = ch; continue; }
        if (ch->type == NODE_NUMBER) { mp_rat_mul(c, ch->op.num, c); continue; }
        if (!is_const_wrt(ch, var)) { num_Cleanup(c); return NULL; }
    }
    if (!exp || !tr) { num_Cleanup(c); return NULL; }

    /* read 'a' from exponent */
    pcas_ast_t *expo = ast_ChildGet(exp,1);
    pcas_ast_t *a_node = NULL;
    if (!expo_linear_coeff(expo, var, &a_node)) { num_Cleanup(c); return NULL; }
    mp_rat a = num_Copy(a_node->op.num); ast_Cleanup(a_node);
    if (mp_rat_compare_zero(a) == 0) { num_Cleanup(c); num_Cleanup(a); return NULL; }

    /* read 'b' and OP_SIN/OP_COS from trig */
    mp_rat b = NULL; OperatorType which;
    if (!trig_is_linear_arg_of_var(tr, var, &b, &which)) { num_Cleanup(c); num_Cleanup(a); return NULL; }

    /* denom = a^2 + b^2 */
    mp_rat a2 = num_FromInt(0); mp_rat_mul(a, a, a2);
    mp_rat b2 = num_FromInt(0); mp_rat_mul(b, b, b2);
    mp_rat denom = num_FromInt(0); mp_rat_add(a2, b2, denom);
    if (mp_rat_compare_zero(denom) == 0) {
        /* degenerate a=b=0 → integrand constant */
        pcas_ast_t *res = ast_MakeBinary(OP_MULT, ast_MakeNumber(c), ast_Copy(var));
        simp(res);
        num_Cleanup(a); num_Cleanup(b); num_Cleanup(a2); num_Cleanup(b2); num_Cleanup(denom);
        return res;
    }

    /* rebuild e^{exponent} exactly as given, and sin(bx)/cos(bx) with same slope b */
    pcas_ast_t *ea = ast_MakeBinary(OP_POW, ast_MakeSymbol(SYM_EULER), ast_Copy(expo));
    pcas_ast_t *bx = ast_MakeBinary(OP_MULT, ast_MakeNumber(num_Copy(b)), ast_Copy(var));
    pcas_ast_t *sinbx = ast_MakeUnary(OP_SIN, ast_Copy(bx));
    pcas_ast_t *cosbx = ast_MakeUnary(OP_COS, bx);

    pcas_ast_t *comb = NULL;
    if (which == OP_SIN) {
        /* a*sin - b*cos */
        pcas_ast_t *t1 = ast_MakeBinary(OP_MULT, ast_MakeNumber(num_Copy(a)), sinbx);
        mp_rat negb = num_Copy(b); mp_rat_neg(negb, negb);
        pcas_ast_t *t2 = ast_MakeBinary(OP_MULT, ast_MakeNumber(negb), cosbx);
        comb = ast_MakeBinary(OP_ADD, t1, t2);
    } else { /* OP_COS */
        /* a*cos + b*sin */
        pcas_ast_t *t1 = ast_MakeBinary(OP_MULT, ast_MakeNumber(num_Copy(a)), cosbx);
        pcas_ast_t *t2 = ast_MakeBinary(OP_MULT, ast_MakeNumber(num_Copy(b)), sinbx);
        comb = ast_MakeBinary(OP_ADD, t1, t2);
    }

    pcas_ast_t *nume = ast_MakeBinary(OP_MULT, ea, comb);
    pcas_ast_t *core = ast_MakeBinary(OP_DIV, nume, ast_MakeNumber(num_Copy(denom)));
    pcas_ast_t *res  = (mp_rat_compare_value(c,1,1)!=0)
                        ? ast_MakeBinary(OP_MULT, ast_MakeNumber(c), core)
                        : core;
    simp(res);

    num_Cleanup(a); num_Cleanup(b); num_Cleanup(a2); num_Cleanup(b2); num_Cleanup(denom);
    return res;
}

/* ---------------- Exponential e^(a x) helper ---------------- */

/* Expo linear coefficient: try to read exponent as a*var (+ const).
   Returns true and stores NUMBER node in *a_out when succeeds. */
static bool expo_linear_coeff(pcas_ast_t *expo, pcas_ast_t *var, pcas_ast_t **a_out) {
    if (!expo || !var || !a_out) return false;

    /* direct: expo == var */
    if (expo->type == NODE_SYMBOL && ast_Compare(expo, var)) {
        *a_out = ast_MakeNumber(num_FromInt(1));
        return true;
    }

    /* product of numbers and var */
    if (expo->type == NODE_OPERATOR && optype(expo) == OP_MULT) {
        mp_rat acc = num_FromInt(1);
        bool saw_var = false;

        for (pcas_ast_t *ch = ast_ChildGet(expo, 0); ch; ch = ch->next) {
            if (ch->type == NODE_SYMBOL && ast_Compare(ch, var)) {
                if (saw_var) { num_Cleanup(acc); return false; }
                saw_var = true;
            } else if (ch->type == NODE_NUMBER) {
                mp_rat_mul(acc, ch->op.num, acc);
            } else {
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

    /* a*var + b (b constant) */
    if (expo->type == NODE_OPERATOR && optype(expo) == OP_ADD) {
        pcas_ast_t *term_with_var = NULL;

        for (pcas_ast_t *t = ast_ChildGet(expo, 0); t; t = t->next) {
            bool dep = depends_on_var(t, var);
            if (dep) {
                if (term_with_var) return false;
                term_with_var = t;
            } else {
                if (!is_const_wrt(t, var)) return false;
            }
        }
        if (!term_with_var) return false;
        return expo_linear_coeff(term_with_var, var, a_out);
    }

    return false;
}

/* ---------------- Quadratic-under-root (complete the square) ---------------- */

/* Try to extract radicand polynomial if root_like = sqrt(expr) or expr^(1/2) */
static bool extract_radicand(pcas_ast_t *root_like, pcas_ast_t **poly_out) {
    if (!root_like || !poly_out) return false;
    if (is_op(root_like, OP_ROOT)) {
        pcas_ast_t *deg = ast_ChildGet(root_like, 0);
        if (deg && deg->type == NODE_NUMBER && mp_rat_compare_value(deg->op.num, 2, 1) == 0) {
            *poly_out = ast_ChildGet(root_like, 1);
            return *poly_out != NULL;
        }
    }
    if (is_op(root_like, OP_POW)) {
        pcas_ast_t *b = ast_ChildGet(root_like, 0);
        pcas_ast_t *e = ast_ChildGet(root_like, 1);
        if (e && e->type == NODE_OPERATOR && optype(e) == OP_DIV) {
            pcas_ast_t *n = ast_ChildGet(e, 0);
            pcas_ast_t *d = ast_ChildGet(e, 1);
            if (n && d && is_ast_int(n, 1) && is_ast_int(d, 2)) {
                *poly_out = b;
                return *poly_out != NULL;
            }
        }
    }
    return false;
}

/* Parse a quadratic of the form  ±x^2 + b x + c (a = ±1 only) into sgn, b, c.
   Input poly should be flattened sum. */
static bool read_ax2_bx_c_a_pm1(pcas_ast_t *poly, pcas_ast_t *var, int *sgn_out, mp_rat *b_out, mp_rat *c_out) {
    if (!poly || !is_op(poly, OP_ADD)) return false;

    int sgn = 0; /* +1 if +x^2 appears, -1 if -x^2 appears */
    mp_rat b = num_FromInt(0);
    mp_rat c = num_FromInt(0);

    for (pcas_ast_t *t = ast_ChildGet(poly,0); t; t=t->next) {
        if (is_op(t, OP_POW)) {
            pcas_ast_t *base = ast_ChildGet(t,0), *exp = ast_ChildGet(t,1);
            if (base && base->type==NODE_SYMBOL && ast_Compare(base,var)
                && exp && exp->type==NODE_NUMBER && mp_rat_compare_value(exp->op.num,2,1)==0) {
                if (sgn == 0) sgn = +1;
                else if (sgn != +1) { num_Cleanup(b); num_Cleanup(c); return false; }
                continue;
            }
        }
        if (is_op(t, OP_MULT)) {
            /* check -x^2 */
            if (is_ast_int(ast_ChildGet(t,0), -1) && is_op(ast_ChildGet(t,1), OP_POW)) {
                pcas_ast_t *p = ast_ChildGet(t,1);
                pcas_ast_t *base = ast_ChildGet(p,0), *exp = ast_ChildGet(p,1);
                if (base && base->type==NODE_SYMBOL && ast_Compare(base,var)
                    && exp && exp->type==NODE_NUMBER && mp_rat_compare_value(exp->op.num,2,1)==0) {
                    if (sgn == 0) sgn = -1;
                    else if (sgn != -1) { num_Cleanup(b); num_Cleanup(c); return false; }
                    continue;
                }
            }
            /* k*x or x*k */
            pcas_ast_t *a = ast_ChildGet(t,0), *d = ast_ChildGet(t,1);
            if (a && d && a->type==NODE_NUMBER && d->type==NODE_SYMBOL && ast_Compare(d,var)) {
                mp_rat_add(b, a->op.num, b);
                continue;
            }
            if (d && a && d->type==NODE_NUMBER && a->type==NODE_SYMBOL && ast_Compare(a,var)) {
                mp_rat_add(b, d->op.num, b);
                continue;
            }
        }
        if (t->type==NODE_NUMBER) {
            mp_rat_add(c, t->op.num, c);
            continue;
        }
        /* Something else — give up */
        num_Cleanup(b); num_Cleanup(c);
        return false;
    }

    if (sgn == 0) { num_Cleanup(b); num_Cleanup(c); return false; }

    *sgn_out = sgn;
    *b_out   = b;
    *c_out   = c;
    return true;
}

/* Complete the square for ±x^2 + b x + c.
   For sgn=+1:  x^2 + b x + c = (x - h)^2 + K,  h = -b/2, K = c - (b/2)^2
   For sgn=-1: -x^2 + b x + c = -[(x - h)^2 - K] = -(x - h)^2 + K,
               h =  b/2, K = c + h^2
*/
static bool complete_square_simple(pcas_ast_t *poly, pcas_ast_t *var, int *sgn_out, mp_rat *h_out, mp_rat *K_out) {
    int sgn = 0; mp_rat b = NULL, c = NULL;
    if (!read_ax2_bx_c_a_pm1(poly, var, &sgn, &b, &c)) return false;

    mp_rat half = num_FromInt(1); mp_rat_div(half, num_FromInt(2), half);
    mp_rat h = num_FromInt(0);

    if (sgn > 0) {
        /* h = -b/2 */
        mp_rat_mul(b, half, h);   /* b/2 */
        mp_rat_sub(num_FromInt(0), h, h); /* -b/2 */
        /* K = c - (b/2)^2 = c - ( (-h)^2 ) = c - h^2 */
        mp_rat h2 = num_FromInt(0); mp_rat_mul(h, h, h2);
        mp_rat K = num_FromInt(0); mp_rat_sub(c, h2, K);
        *sgn_out = sgn; *h_out = h; *K_out = K;
        num_Cleanup(half); num_Cleanup(b); num_Cleanup(c); num_Cleanup(h2);
        return true;
    } else {
        /* sgn < 0: h = b/2 */
        mp_rat_mul(b, half, h);   /* b/2 */
        /* K = c + h^2 */
        mp_rat h2 = num_FromInt(0); mp_rat_mul(h, h, h2);
        mp_rat K = num_FromInt(0); mp_rat_add(c, h2, K);
        *sgn_out = sgn; *h_out = h; *K_out = K;
        num_Cleanup(half); num_Cleanup(b); num_Cleanup(c); num_Cleanup(h2);
        return true;
    }
}

/* Try to read coefficients (a,b,c) from a quadratic in 'var'.
   Accepts a sum of terms like:
     k2 * var^2    or   var^2 * k2   or   var^2        (k2 defaults to 1)
     k1 * var      or   var * k1
     k0            (number)
   Returns true on success and writes copies of the rationals into a_out,b_out,c_out.
   NOTE: We simplify a local copy of 'den' to improve matching. */
static bool read_quadratic_coeffs_general(pcas_ast_t *den, pcas_ast_t *var,
                                          mp_rat *a_out, mp_rat *b_out, mp_rat *c_out) {
    if (!den || !var || !a_out || !b_out || !c_out) return false;

    pcas_ast_t *flat = ast_Copy(den);
    simplify(flat, SIMP_NORMALIZE | SIMP_RATIONAL | SIMP_COMMUTATIVE |
                   SIMP_EVAL | SIMP_LIKE_TERMS);

    mp_rat a = num_FromInt(0), b = num_FromInt(0), c = num_FromInt(0);
    bool ok = true;

    /* If it's just a number or single term, normalize to an ADD with one child */
    if (!is_op(flat, OP_ADD)) {
        pcas_ast_t *sum = ast_MakeOperator(OP_ADD);
        ast_ChildAppend(sum, ast_Copy(flat));
        ast_Cleanup(flat);
        flat = sum;
    }

    for (pcas_ast_t *t = ast_ChildGet(flat, 0); t && ok; t = t->next) {
        if (is_op(t, OP_POW)) {
            /* var^2 */
            pcas_ast_t *base = ast_ChildGet(t,0), *exp = ast_ChildGet(t,1);
            if (base && base->type==NODE_SYMBOL && ast_Compare(base,var) &&
                exp && exp->type==NODE_NUMBER && mp_rat_compare_value(exp->op.num,2,1)==0) {
                mp_rat_add(a, num_FromInt(1), a);
            } else {
                ok = false;
            }
        } else if (is_op(t, OP_MULT)) {
            pcas_ast_t *u = ast_ChildGet(t,0), *v = ast_ChildGet(t,1);
            /* k * var^2  or  var^2 * k */
            if (u && v && is_op(u, OP_POW) && v->type==NODE_NUMBER) {
                pcas_ast_t *base = ast_ChildGet(u,0), *exp = ast_ChildGet(u,1);
                if (base && base->type==NODE_SYMBOL && ast_Compare(base,var) &&
                    exp && exp->type==NODE_NUMBER && mp_rat_compare_value(exp->op.num,2,1)==0) {
                    mp_rat_add(a, v->op.num, a);
                } else { ok = false; }
            } else if (u && v && is_op(v, OP_POW) && u->type==NODE_NUMBER) {
                pcas_ast_t *base = ast_ChildGet(v,0), *exp = ast_ChildGet(v,1);
                if (base && base->type==NODE_SYMBOL && ast_Compare(base,var) &&
                    exp && exp->type==NODE_NUMBER && mp_rat_compare_value(exp->op.num,2,1)==0) {
                    mp_rat_add(a, u->op.num, a);
                } else { ok = false; }
            }
            /* k * var  or  var * k */
            else if (u && v && u->type==NODE_NUMBER && v->type==NODE_SYMBOL && ast_Compare(v,var)) {
                mp_rat_add(b, u->op.num, b);
            } else if (u && v && v->type==NODE_NUMBER && u->type==NODE_SYMBOL && ast_Compare(u,var)) {
                mp_rat_add(b, v->op.num, b);
            } else {
                /* allow trailing numeric factors folded by simplifier (e.g., 0*var) -> already handled,
                   but any other var-dependent structure is unsupported */
                if (!is_const_wrt(t, var)) ok = false;
                else mp_rat_add(c, ((t->type==NODE_NUMBER) ? t->op.num : num_FromInt(0)), c);
            }
        } else if (t->type == NODE_SYMBOL && ast_Compare(t, var)) {
            /* bare var → +1*var */
            mp_rat_add(b, num_FromInt(1), b);
        } else if (t->type == NODE_NUMBER) {
            mp_rat_add(c, t->op.num, c);
        } else {
            ok = false;
        }
    }

    ast_Cleanup(flat);

    if (!ok) { num_Cleanup(a); num_Cleanup(b); num_Cleanup(c); return false; }

    *a_out = a; *b_out = b; *c_out = c;
    return true;
}
/* ∫ dx / (a x^2 + b x + c)
   Δ = b^2 - 4ac  (note the sign convention!)
   Δ < 0 :  2/√(-Δ) * atan( (2a x + b)/√(-Δ) )
   Δ > 0 :  1/√Δ   * ln| (2a x + b - √Δ) / (2a x + b + √Δ) |
   Δ = 0 :  -1 / ( a * ( x + b/(2a) ) )
*/
/* ∫ dx / (a x^2 + b x + c)
   Δ = b^2 - 4ac
   Δ < 0 :  (2/√(4ac - b^2)) * atan( (2a/√(4ac - b^2)) * (x + b/(2a)) )
   Δ > 0 :  1/√Δ * ln|(2a x + b - √Δ)/(2a x + b + √Δ)|
   Δ = 0 :  -1 / ( a * ( x + b/(2a) ) )
*/
/* ∫ dx / (a x^2 + b x + c)
   Δ = b^2 - 4ac
   Δ < 0 :  (1/√(aK)) * atan( √(a/K) * (x + b/(2a)) ),  where K = c - b^2/(4a)
   Δ > 0 :  1/√Δ * ln|(2a x + b - √Δ)/(2a x + b + √Δ)|
   Δ = 0 :  -1 / ( a * ( x + b/(2a) ) )
*/
/* ∫ dx / (a x^2 + b x + c)
   Δ = b^2 - 4ac
   Δ < 0 :  (2/√(4ac - b^2)) * atan( (2a/√(4ac - b^2)) * (x + b/(2a)) )
   Δ > 0 :  1/√Δ * ln|(2a x + b - √Δ)/(2a x + b + √Δ)|
   Δ = 0 :  -1 / ( a * ( x + b/(2a) ) )
*/
/* ∫ dx / (a x^2 + b x + c)
   Δ = b^2 - 4ac
   Δ < 0 :  (1/√(aK)) * atan( √(a/K) * (x + b/(2a)) ),  where K = c - b^2/(4a)
   Δ > 0 :  1/√Δ * ln|(2a x + b - √Δ)/(2a x + b + √Δ)|
   Δ = 0 :  -1 / ( a * ( x + b/(2a) ) )
*/
static pcas_ast_t *integrate_recip_quadratic_poly(pcas_ast_t *den, pcas_ast_t *var) {
    if (!den || !var) return NULL;

    mp_rat a = NULL, b = NULL, c = NULL;
    if (!read_quadratic_coeffs_general(den, var, &a, &b, &c)) return NULL;

    /* Linear fallback: ∫ dx/(b x + c) = (1/b) ln|b x + c| */
    if (mp_rat_compare_zero(a) == 0) {
        if (mp_rat_compare_zero(b) == 0) { num_Cleanup(a); num_Cleanup(b); num_Cleanup(c); return NULL; }
        mp_rat invb = num_FromInt(1); mp_rat_div(invb, b, invb);
        pcas_ast_t *lin = ast_MakeBinary(OP_ADD,
                             ast_MakeBinary(OP_MULT, ast_MakeNumber(num_Copy(b)), ast_Copy(var)),
                             ast_MakeNumber(num_Copy(c)));
        pcas_ast_t *res = ast_MakeBinary(OP_MULT, ast_MakeNumber(invb), ast_MakeUnary(OP_LOG, lin));
        simp(res);
        num_Cleanup(a); num_Cleanup(b); num_Cleanup(c);
        return res;
    }

    /* Δ = b^2 - 4ac */
    mp_rat b2 = num_FromInt(0); mp_rat_mul(b, b, b2);
    mp_rat fourac = num_FromInt(4); mp_rat_mul(fourac, a, fourac); mp_rat_mul(fourac, c, fourac);
    mp_rat Delta = num_FromInt(0); mp_rat_sub(b2, fourac, Delta);
    int sgnDelta = mp_rat_compare_zero(Delta);

    /* twoa = 2a;  t = 2 a x + b (used in Δ>0 branch) */
    mp_rat twoa = num_FromInt(2); mp_rat_mul(twoa, a, twoa);
    pcas_ast_t *t = ast_MakeBinary(OP_ADD,
                      ast_MakeBinary(OP_MULT, ast_MakeNumber(num_Copy(twoa)), ast_Copy(var)),
                      ast_MakeNumber(num_Copy(b)));

    pcas_ast_t *res = NULL;

    if (sgnDelta < 0) {
        /* Completed-square style:
           K = c - b^2/(4a);  h = b/(2a)
           result = (1/√(aK)) * atan( √(a/K) * (x + h) )
        */
        mp_rat foura = num_FromInt(4); mp_rat_mul(foura, a, foura);               /* 4a */
        mp_rat b2_over_4a = num_FromInt(0); mp_rat_div(b2, foura, b2_over_4a);    /* b^2/(4a) */
        mp_rat K = num_FromInt(0); mp_rat_sub(c, b2_over_4a, K);                  /* K = c - b^2/(4a) */

        /* h = b/(2a) */
        mp_rat h = num_FromInt(0); mp_rat_div(b, twoa, h);
        pcas_ast_t *shift = ast_MakeBinary(OP_ADD, ast_Copy(var), ast_MakeNumber(num_Copy(h)));

        /* coef = 1 / √(a*K) */
        mp_rat aK = num_FromInt(0); mp_rat_mul(a, K, aK);
        pcas_ast_t *sqrt_aK = ast_MakeBinary(OP_ROOT, N(2), ast_MakeNumber(num_Copy(aK)));
        pcas_ast_t *coef = ast_MakeBinary(OP_DIV, N(1), sqrt_aK);

        /* factor = √(a/K)  (build as a/K first to prefer √(2/5) style) */
        mp_rat a_over_K = num_FromInt(0); mp_rat_div(a, K, a_over_K);
        pcas_ast_t *sqrt_a_over_K = ast_MakeBinary(OP_ROOT, N(2), ast_MakeNumber(num_Copy(a_over_K)));

        /* atan( √(a/K) * (x + h) ) */
        pcas_ast_t *atan = ast_MakeUnary(OP_TAN_INV,
                              ast_MakeBinary(OP_MULT, sqrt_a_over_K, shift));

        res = ast_MakeBinary(OP_MULT, coef, atan);
        simp(res);

        /* cleanup locals */
        num_Cleanup(foura); num_Cleanup(b2_over_4a); num_Cleanup(K);
        num_Cleanup(h); num_Cleanup(aK); num_Cleanup(a_over_K);
    } else if (sgnDelta > 0) {
        /* Δ > 0 → 1/√Δ * ln|(t - √Δ)/(t + √Δ)| */
        pcas_ast_t *sqrtD = ast_MakeBinary(OP_ROOT, N(2), ast_MakeNumber(num_Copy(Delta)));
        pcas_ast_t *nume  = ast_MakeBinary(OP_ADD, ast_Copy(t), ast_MakeBinary(OP_MULT, N(-1), ast_Copy(sqrtD)));
        pcas_ast_t *deno  = ast_MakeBinary(OP_ADD, ast_Copy(t),                ast_Copy(sqrtD));
        pcas_ast_t *frac  = ast_MakeBinary(OP_DIV, nume, deno);
        pcas_ast_t *ln    = ast_MakeUnary(OP_LOG, frac);
        pcas_ast_t *coef  = ast_MakeBinary(OP_DIV, N(1), sqrtD); /* 1/√Δ */
        res = ast_MakeBinary(OP_MULT, coef, ln);
        simp(res);
    } else {
        /* Δ == 0 → -1 / ( a * ( x + b/(2a) ) ) */
        mp_rat h = num_FromInt(0); mp_rat_div(b, twoa, h);              /* h = b/(2a) */
        pcas_ast_t *shift = ast_MakeBinary(OP_ADD, ast_Copy(var), ast_MakeNumber(num_Copy(h)));
        pcas_ast_t *denom = ast_MakeBinary(OP_MULT, ast_MakeNumber(num_Copy(a)), shift);
        res = ast_MakeBinary(OP_DIV, N(-1), denom);
        simp(res);
        num_Cleanup(h);
    }

    /* cleanup */
    num_Cleanup(a); num_Cleanup(b); num_Cleanup(c);
    num_Cleanup(b2); num_Cleanup(fourac); num_Cleanup(Delta); num_Cleanup(twoa);
    return res;
}




/* ∫ sqrt(Q(x)) / x dx for the common form Q(x) = (x - h)^2 + K with h = 0, K < 0
   i.e., Q(x) = x^2 - a^2 where a = sqrt(-K) > 0.
   Result: sqrt(x^2 - a^2) - a * arccos(a/x) */
static pcas_ast_t *integrate_sqrt_x2_minus_a2_over_x(pcas_ast_t *num, pcas_ast_t *den, pcas_ast_t *var) {
    /* need numerator = sqrt(Q(x)) and denominator = x */
    if (!num || !den) return NULL;
    if (!(den->type == NODE_SYMBOL && ast_Compare(den, var))) return NULL;  /* denom must be x */
    /* numerator must be sqrt-like */
    if (!is_sqrt_like(num)) return NULL;

    /* extract Q(x) from sqrt(Q(x)) */
    pcas_ast_t *poly = NULL;
    if (!extract_radicand(num, &poly) || !poly) return NULL;

    /* complete the square: require sgn>0, h=0 (so Q = (x-h)^2 + K with h=0), and K<0 */
    int sgn = 0; mp_rat h = num_FromInt(0), K = num_FromInt(0);
    if (!complete_square_simple(poly, var, &sgn, &h, &K)) { num_Cleanup(h); num_Cleanup(K); return NULL; }

    bool ok = (sgn > 0) && (mp_rat_compare_zero(h) == 0) && (mp_rat_compare_zero(K) < 0);
    if (!ok) { num_Cleanup(h); num_Cleanup(K); return NULL; }

    /* a = sqrt(-K) */
    mp_rat negK = num_FromInt(0); mp_rat_sub(num_FromInt(0), K, negK);
    pcas_ast_t *a = ast_MakeBinary(OP_ROOT, N(2), ast_MakeNumber(num_Copy(negK)));

    /* term1 = sqrt(Q(x)) -- just copy numerator */
    pcas_ast_t *term1 = ast_Copy(num);

    /* acos(a/x) */
    pcas_ast_t *arg = ast_MakeBinary(OP_DIV, ast_Copy(a), ast_Copy(var));
    pcas_ast_t *acos = ast_MakeUnary(OP_COS_INV, arg);  /* use your enum token for arccos */

    /* term2 = a * acos(a/x) */
    pcas_ast_t *term2 = ast_MakeBinary(OP_MULT, ast_Copy(a), acos);

    /* result = term1 - term2 */
    pcas_ast_t *res = ast_MakeBinary(OP_ADD, term1, ast_MakeBinary(OP_MULT, N(-1), term2));
    simp(res);

    num_Cleanup(h); num_Cleanup(K); num_Cleanup(negK);
    return res;
}

/* Read linear numerator n1*x + n0 (w.r.t. var). Accepts sums of terms:
   k*x, x, number, and ignores pure numeric factors folded by simplifier.
   Returns true on success and writes rationals into n1_out, n0_out. */
static bool read_linear_coeffs_general(pcas_ast_t *num, pcas_ast_t *var,
                                       mp_rat *n1_out, mp_rat *n0_out) {
    if (!num || !var || !n1_out || !n0_out) return false;

    pcas_ast_t *flat = ast_Copy(num);
    simplify(flat, SIMP_NORMALIZE | SIMP_RATIONAL | SIMP_COMMUTATIVE |
                   SIMP_EVAL | SIMP_LIKE_TERMS);

    mp_rat n1 = num_FromInt(0), n0 = num_FromInt(0);
    bool ok = true;

    if (!is_op(flat, OP_ADD)) {
        pcas_ast_t *sum = ast_MakeOperator(OP_ADD);
        ast_ChildAppend(sum, ast_Copy(flat));
        ast_Cleanup(flat);
        flat = sum;
    }

    for (pcas_ast_t *t = ast_ChildGet(flat, 0); t && ok; t = t->next) {
        if (t->type == NODE_SYMBOL && ast_Compare(t, var)) {
            /* bare var -> +1*x */
            mp_rat_add(n1, num_FromInt(1), n1);
        } else if (is_op(t, OP_MULT)) {
            pcas_ast_t *u = ast_ChildGet(t,0), *v = ast_ChildGet(t,1);
            if (u && v && u->type==NODE_NUMBER && v && v->type==NODE_SYMBOL && ast_Compare(v,var)) {
                mp_rat_add(n1, u->op.num, n1);
            } else if (u && v && v->type==NODE_NUMBER && u && u->type==NODE_SYMBOL && ast_Compare(u,var)) {
                mp_rat_add(n1, v->op.num, n1);
            } else if (is_const_wrt(t, var) && t->type==NODE_NUMBER) {
                mp_rat_add(n0, t->op.num, n0);
            } else {
                ok = false;
            }
        } else if (t->type == NODE_NUMBER) {
            mp_rat_add(n0, t->op.num, n0);
        } else if (is_const_wrt(t, var)) {
            /* any other constant term (e.g., folded) */
            if (t->type == NODE_NUMBER) mp_rat_add(n0, t->op.num, n0);
            else ok = false;
        } else {
            ok = false;
        }
    }

    ast_Cleanup(flat);
    if (!ok) { num_Cleanup(n1); num_Cleanup(n0); return false; }

    *n1_out = n1; *n0_out = n0;
    return true;
}

/* ∫ dx / ( k * x * sqrt(Q(x)) ) for Q(x) = K - (x - h)^2 with h = 0, K > 0
   Returns  -(1/(k√K)) * ln( (√K + √Q)/x )  or NULL if not matched. */
static pcas_ast_t *integrate_recip_x_times_quadratic_root(pcas_ast_t *den, pcas_ast_t *var) {
    pcas_ast_t *root_like = NULL;
    mp_rat k = num_FromInt(1);

    if (!is_op(den, OP_MULT)) { num_Cleanup(k); return NULL; }
    if (!split_x_times_root(den, var, &root_like, &k)) { num_Cleanup(k); return NULL; }

    /* Pull Q(x) out of sqrt(Q(x)) */
    pcas_ast_t *poly = NULL;
    if (!extract_radicand(root_like, &poly) || !poly) { num_Cleanup(k); return NULL; }

    /* Complete the square: need sgn < 0 and h == 0 (i.e., Q(x) = K - x^2) */
    int sgn = 0; mp_rat h = num_FromInt(0), K = num_FromInt(0);
    if (!complete_square_simple(poly, var, &sgn, &h, &K)) {
        num_Cleanup(k); num_Cleanup(h); num_Cleanup(K);
        return NULL;
    }
    bool ok = (sgn < 0) && (mp_rat_compare_zero(h) == 0) && (mp_rat_compare_zero(K) > 0);
    if (!ok) { num_Cleanup(k); num_Cleanup(h); num_Cleanup(K); return NULL; }

    /* Build:  -(1/(k√K)) * ln( (√K + √Q(x))/x ) */
    pcas_ast_t *sqrtK_1 = ast_MakeBinary(OP_ROOT, N(2), ast_MakeNumber(num_Copy(K)));
    pcas_ast_t *sqrtK_2 = ast_Copy(sqrtK_1);

    pcas_ast_t *sqrtQ   = ast_MakeBinary(OP_ROOT, N(2), ast_Copy(poly));
    pcas_ast_t *sum     = ast_MakeBinary(OP_ADD, sqrtK_1, sqrtQ);
    pcas_ast_t *frac    = ast_MakeBinary(OP_DIV, sum, ast_Copy(var));
    pcas_ast_t *ln      = ast_MakeUnary(OP_LOG, frac);

    /* coef = -(1/(k√K)) */
    mp_rat invk = num_FromInt(1); mp_rat_div(invk, k, invk);      /* 1/k */
    pcas_ast_t *coef = ast_MakeBinary(OP_MULT,
                        ast_MakeNumber(invk),
                        ast_MakeBinary(OP_DIV, N(-1), sqrtK_2));

    pcas_ast_t *res  = ast_MakeBinary(OP_MULT, coef, ln);
    simp(res);

    num_Cleanup(k); num_Cleanup(h); num_Cleanup(K);
    return res;
}


/* ∫ (n1*x + n0) / (a2*x^2 + a1*x + a0) dx
   = α ln|den| + β ∫ dx/(den),  where α = n1/(2*a2), β = n0 - α*a1 */
static pcas_ast_t *integrate_linear_over_quadratic(pcas_ast_t *num, pcas_ast_t *den, pcas_ast_t *var) {
    if (!num || !den) return NULL;

    /* read numerator and denominator coefficients */
    mp_rat n1=NULL, n0=NULL;
    if (!read_linear_coeffs_general(num, var, &n1, &n0)) return NULL;

    mp_rat a2=NULL, a1=NULL, a0=NULL;
    if (!read_quadratic_coeffs_general(den, var, &a2, &a1, &a0)) {
        num_Cleanup(n1); num_Cleanup(n0);
        return NULL;
    }

    /* require a2 != 0 (den really quadratic) */
    if (mp_rat_compare_zero(a2) == 0) {
        num_Cleanup(n1); num_Cleanup(n0); num_Cleanup(a2); num_Cleanup(a1); num_Cleanup(a0);
        return NULL;
    }

    /* α = n1 / (2*a2) */
    mp_rat twoa2 = num_FromInt(2); mp_rat_mul(twoa2, a2, twoa2);
    mp_rat alpha = num_FromInt(0); mp_rat_div(n1, twoa2, alpha);

    /* β = n0 - α*a1 */
    mp_rat alpha_a1 = num_FromInt(0); mp_rat_mul(alpha, a1, alpha_a1);
    mp_rat beta = num_FromInt(0); mp_rat_sub(n0, alpha_a1, beta);

    /* term1 = α * ln|den|  (we'll just build ln(den) per your conventions) */
    pcas_ast_t *ln_den = ast_MakeUnary(OP_LOG, ast_Copy(den));
    pcas_ast_t *term1  = ast_MakeBinary(OP_MULT, ast_MakeNumber(num_Copy(alpha)), ln_den);

    /* term2 = β * ∫ dx/(den)   — reuse your 1/quadratic integrator */
    pcas_ast_t *Irecip = integrate_recip_quadratic_poly(den, var);
    if (!Irecip) {
        ast_Cleanup(term1);
        num_Cleanup(n1); num_Cleanup(n0); num_Cleanup(a2); num_Cleanup(a1); num_Cleanup(a0);
        num_Cleanup(twoa2); num_Cleanup(alpha); num_Cleanup(alpha_a1); num_Cleanup(beta);
        return NULL;
    }
    pcas_ast_t *term2 = ast_MakeBinary(OP_MULT, ast_MakeNumber(num_Copy(beta)), Irecip);

    /* sum */
    pcas_ast_t *res = ast_MakeBinary(OP_ADD, term1, term2);
    simp(res);

    /* cleanup rationals */
    num_Cleanup(n1); num_Cleanup(n0); num_Cleanup(a2); num_Cleanup(a1); num_Cleanup(a0);
    num_Cleanup(twoa2); num_Cleanup(alpha); num_Cleanup(alpha_a1); num_Cleanup(beta);

    return res;
}

/* ∫ dx / sqrt( s*(x-h)^2 + K )
   If s = -1 and K>0: integral = arcsin( (x-h)/sqrt(K) )
   If s = +1 and K>0: integral = ln| x-h + sqrt((x-h)^2 + K) |  (asinh form)
   Other cases: return NULL (extend later if needed).
*/
static pcas_ast_t *integrate_quadratic_root(pcas_ast_t *root_like, pcas_ast_t *var) {
    pcas_ast_t *poly = NULL;
    if (!extract_radicand(root_like, &poly)) return NULL;
    if (!poly) return NULL;

    int sgn = 0; mp_rat h = num_FromInt(0), K = num_FromInt(0);
    if (!complete_square_simple(poly, var, &sgn, &h, &K)) {
        num_Cleanup(h); num_Cleanup(K);
        return NULL;
    }

    /* (x - h) == x + (-h) */
    mp_rat neg_h = num_FromInt(0); mp_rat_sub(neg_h, h, neg_h);
    pcas_ast_t *shift = ast_MakeBinary(OP_ADD, ast_Copy(var), ast_MakeNumber(neg_h));

    if (sgn < 0 && mp_rat_compare_zero(K) > 0) {
        /* arcsin( (x - h) / sqrt(K) ) */
        pcas_ast_t *sqrtK = ast_MakeBinary(OP_ROOT, N(2), ast_MakeNumber(num_Copy(K)));
        pcas_ast_t *arg   = ast_MakeBinary(OP_DIV, shift, sqrtK);
        pcas_ast_t *res   = ast_MakeUnary(OP_SIN_INV, arg);
        simp(res);
        num_Cleanup(h); num_Cleanup(K);
        return res;
    }

    if (sgn > 0 && mp_rat_compare_zero(K) > 0) {
        /* ln| x-h + sqrt( (x-h)^2 + K ) | */
        pcas_ast_t *sq = ast_MakeBinary(OP_POW, ast_Copy(shift), N(2));
        pcas_ast_t *inside_rad = ast_MakeBinary(OP_ADD, sq, ast_MakeNumber(num_Copy(K)));
        pcas_ast_t *sqrt = ast_MakeBinary(OP_ROOT, N(2), inside_rad);
        pcas_ast_t *sum  = ast_MakeBinary(OP_ADD, shift, sqrt);
        pcas_ast_t *res  = ast_MakeUnary(OP_LOG, sum);
        simp(res);
        num_Cleanup(h); num_Cleanup(K);
        return res;
    }

    num_Cleanup(h); num_Cleanup(K);
    return NULL;
}

/* ---------------- IBP: poly(x) * (sin|cos)(x)  (1 step; recursion guarded) ---------------- */
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
        if (!picked && !poly && (ch->type == NODE_SYMBOL && ast_Compare(ch, var))) {
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
        mp_small num, den;
        if (mp_rat_to_ints(poly_pow->op.num, &num, &den) != MP_OK || den != 1 || num < 1) {
            ast_Cleanup(const_factor);
            return NULL;
        }
        n = (int)num;
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

/* ---------------- Integrators by operator ---------------- */

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

    /* e^(a*x [+ b]) : ∫ = (1/a) e^(a x) */
    if (base->type == NODE_SYMBOL && base->op.symbol == SYM_EULER) {
        pcas_ast_t *a_num = NULL;
        if (expo_linear_coeff(expo, var, &a_num)) {
            if (mp_rat_compare_value(a_num->op.num, 1, 1) == 0) {
                pcas_ast_t *res = ast_MakeBinary(OP_POW, ast_Copy(base), ast_Copy(expo));
                ast_Cleanup(a_num);
                simp(res);
                return res;
            }
            mp_rat c = num_FromInt(1); mp_rat_div(c, a_num->op.num, c); /* 1/a */
            pcas_ast_t *coef = ast_MakeNumber(c);
            pcas_ast_t *pow  = ast_MakeBinary(OP_POW, ast_Copy(base), ast_Copy(expo));
            pcas_ast_t *res  = ast_MakeBinary(OP_MULT, coef, pow);
            ast_Cleanup(a_num);
            simp(res);
            return res;
        }
    }

    /* x^n where n is NUMBER (fractional allowed) */
    {
        pcas_ast_t *r = integrate_x_power_any(expr, var);
        if (r) return r;
    }

    /* sec^2 / csc^2 via cos/sin powers (covers cos^(-2), 1/(cos^2), (1/cos)^2, etc.) */
    if (is_sec2_of_var(expr, var)) {
        pcas_ast_t *res = ast_MakeUnary(OP_TAN, ast_Copy(var));   /* ∫sec^2 = tan */
        simp(res);
        return res;
    }
    if (is_csc2_of_var(expr, var)) {
        pcas_ast_t *cot = ast_MakeBinary(OP_DIV, ast_MakeUnary(OP_COS, ast_Copy(var)),
                                         ast_MakeUnary(OP_SIN, ast_Copy(var)));
        pcas_ast_t *res = ast_MakeBinary(OP_MULT, N(-1), cot);    /* ∫csc^2 = -cot */
        simp(res);
        return res;
    }

    /* NEW: tan^2(x) = sec^2(x) - 1  ⇒  ∫ tan^2 x dx = tan x - x  */
    if (is_op(base, OP_TAN)) {
        pcas_ast_t *arg = ast_ChildGet(base, 0);
        if (arg && arg->type == NODE_SYMBOL && ast_Compare(arg, var) &&
            expo->type == NODE_NUMBER && mp_rat_compare_value(expo->op.num, 2, 1) == 0) {

            /* tan(x) - x */
            pcas_ast_t *tanx = ast_MakeUnary(OP_TAN, ast_Copy(var));
            pcas_ast_t *res  = ast_MakeBinary(OP_ADD, tanx,
                                  ast_MakeBinary(OP_MULT, N(-1), ast_Copy(var)));
            simp(res);
            return res;
        }
    }

    return NULL;
}

/* Return true if node is x^deg (deg>=1) or x (deg=1). Writes deg to *deg_out. */
static bool read_poly_power_of_var(pcas_ast_t *node, pcas_ast_t *var, int *deg_out) {
    if (!node) return false;

    if (node->type == NODE_SYMBOL && ast_Compare(node, var)) {
        *deg_out = 1;
        return true;
    }

    /* FIX: use is_op(...) here (not isoptype) */
    if (is_op(node, OP_POW)) {
        pcas_ast_t *b = ast_ChildGet(node,0), *e = ast_ChildGet(node,1);
        if (b && b->type == NODE_SYMBOL && ast_Compare(b, var) &&
            e && e->type == NODE_NUMBER) {
            mp_small num, den;
            if (mp_rat_to_ints(e->op.num, &num, &den) == MP_OK && den == 1 && num >= 1) {
                *deg_out = (int)num;
                return true;
            }
        }
    }
    return false;
}

/* ∫ x^n ln x dx = (x^{n+1}/(n+1)) ln x - x^{n+1}/(n+1)^2, n>=0 */
static pcas_ast_t *integrate_xn_lnx_product(pcas_ast_t *expr, pcas_ast_t *var) {
    if (!expr || !is_op(expr, OP_MULT)) return NULL;

    bool saw_lnx = false; int n = -1; mp_rat c = num_FromInt(1);

    for (pcas_ast_t *ch = ast_ChildGet(expr,0); ch; ch=ch->next) {
        if (ch->type==NODE_NUMBER) { mp_rat_mul(c, ch->op.num, c); continue; }
        if (!saw_lnx && is_op(ch, OP_LOG)) {
            pcas_ast_t *a0 = ast_ChildGet(ch,0), *a1 = ast_ChildGet(ch,1);
            if (a1==NULL && a0 && a0->type==NODE_SYMBOL && ast_Compare(a0,var)) { saw_lnx = true; continue; }
        }
        if (n < 0) { int deg; if (read_poly_power_of_var(ch, var, &deg)) { n = deg; continue; } }
        if (!is_const_wrt(ch, var)) { num_Cleanup(c); return NULL; }
        /* other constants would be NODE_NUMBER; anything else → bail */
        num_Cleanup(c); return NULL;
    }
    if (!saw_lnx || n < 0) { num_Cleanup(c); return NULL; }

    int np1i = n + 1;
    mp_rat np1 = num_FromInt(np1i);
    mp_rat np1_sq = num_FromInt(np1i); mp_rat_mul(np1_sq, np1_sq, np1_sq);

    pcas_ast_t *x_np1_a = ast_MakeBinary(OP_POW, ast_Copy(var), ast_MakeNumber(num_Copy(np1)));
    pcas_ast_t *x_np1_b = ast_MakeBinary(OP_POW, ast_Copy(var), ast_MakeNumber(num_Copy(np1)));

    pcas_ast_t *term1 = ast_MakeBinary(OP_MULT,
                        ast_MakeBinary(OP_DIV, x_np1_a, ast_MakeNumber(num_Copy(np1))),
                        ast_MakeUnary(OP_LOG, ast_Copy(var)));
    pcas_ast_t *term2 = ast_MakeBinary(OP_DIV, x_np1_b, ast_MakeNumber(np1_sq));

    pcas_ast_t *core = ast_MakeBinary(OP_ADD, term1, ast_MakeBinary(OP_MULT, N(-1), term2));
    pcas_ast_t *res  = (mp_rat_compare_value(c,1,1)!=0)
                        ? ast_MakeBinary(OP_MULT, ast_MakeNumber(c), core)
                        : core;
    simp(res);
    return res;
}


/* ∫ x^n e^{a x} dx with e^{a x [+ b]} allowed (b folds into the power node).
   Finite non-recursive IBP (tabular). Returns NULL if pattern not matched. */
static pcas_ast_t *integrate_poly_times_exp_linear(pcas_ast_t *expr, pcas_ast_t *var) {
    if (!expr || !is_op(expr, OP_MULT)) return NULL;

    int n = -1;
    pcas_ast_t *exp = NULL;
    mp_rat c = num_FromInt(1);

    for (pcas_ast_t *ch = ast_ChildGet(expr,0); ch; ch=ch->next) {
        if (ch->type == NODE_NUMBER) { mp_rat_mul(c, ch->op.num, c); continue; }
        if (n < 0) { int deg; if (read_poly_power_of_var(ch, var, &deg)) { n = deg; continue; } }
        if (!exp && is_op(ch, OP_POW)) {
            pcas_ast_t *b = ast_ChildGet(ch,0), *e = ast_ChildGet(ch,1);
            if (b && b->type==NODE_SYMBOL && b->op.symbol==SYM_EULER && e) { exp = ch; continue; }
        }
        if (!is_const_wrt(ch, var)) { num_Cleanup(c); return NULL; }
    }
    if (n < 0 || !exp) { num_Cleanup(c); return NULL; }

    pcas_ast_t *a_node = NULL;
    if (!expo_linear_coeff(ast_ChildGet(exp,1), var, &a_node)) { num_Cleanup(c); return NULL; }
    mp_rat a = num_Copy(a_node->op.num); ast_Cleanup(a_node);
    if (mp_rat_compare_zero(a) == 0) { num_Cleanup(c); num_Cleanup(a); return NULL; }

    pcas_ast_t *e_ax = ast_MakeBinary(OP_POW, ast_MakeSymbol(SYM_EULER), ast_Copy(ast_ChildGet(exp,1)));
    pcas_ast_t *sum = N(0);

    mp_rat coeff = num_FromInt(1);
    mp_rat inva  = num_FromInt(1); mp_rat_div(inva, a, inva);
    int p = n;

    while (1) {
        mp_rat termc = num_FromInt(0); mp_rat_mul(coeff, inva, termc); /* coeff/a */

        pcas_ast_t *xpow = (p==0) ? N(1) :
                           (p==1) ? ast_Copy(var) :
                                    ast_MakeBinary(OP_POW, ast_Copy(var), N(p));

        pcas_ast_t *term = ast_MakeBinary(
            OP_MULT,
            ast_MakeNumber(termc),
            ast_MakeBinary(OP_MULT, xpow, ast_Copy(e_ax))
        );
        sum = ast_MakeBinary(OP_ADD, sum, term);

        if (p == 0) break;

        mp_rat tmp = num_FromInt(p);
        mp_rat_mul(coeff, tmp, coeff);
        mp_rat_div(coeff, a, coeff);
        mp_rat_neg(coeff, coeff);
        num_Cleanup(tmp);
        p -= 1;
    }

    pcas_ast_t *res = (mp_rat_compare_value(c,1,1)!=0)
                        ? ast_MakeBinary(OP_MULT, ast_MakeNumber(c), sum)
                        : sum;
    simp(res);
    num_Cleanup(a);
    return res;
}



/* ∫ x^n * (sin|cos)(u) dx for integer n>=0 and linear u = a*var + b (a != 0)
   Non-recursive tabular implementation:
     Define I_c(k) = ∫ x^k cos(u) dx, I_s(k) = ∫ x^k sin(u) dx, u' = a
     Bases:
       I_c(0) =  sin(u)/a
       I_s(0) = -cos(u)/a
     Recurrences (k >= 1):
       I_c(k) =  x^k sin(u)/a - (k/a) * I_s(k-1)
       I_s(k) = -x^k cos(u)/a + (k/a) * I_c(k-1)
   We build up from k=0..n and return I_c(n) or I_s(n) accordingly.
   Pattern match: product of (numeric consts) * (x or x^n) * (sin(u) or cos(u)); nothing else with var.
*/
static pcas_ast_t *integrate_poly_times_trig_linear(pcas_ast_t *expr, pcas_ast_t *var) {
    if (!expr || !is_op(expr, OP_MULT)) return NULL;

    /* Parse product */
    mp_rat c = num_FromInt(1);
    int n = -1; /* degree of x^n */
    pcas_ast_t *trig = NULL;   /* SIN or COS node */
    pcas_ast_t *u    = NULL;   /* its argument */

    for (pcas_ast_t *ch = ast_ChildGet(expr, 0); ch; ch = ch->next) {
        if (ch->type == NODE_NUMBER) { mp_rat_mul(c, ch->op.num, c); continue; }

        if (n < 0) {
            int deg;
            if (read_poly_power_of_var(ch, var, &deg)) { n = deg; continue; }
        }

        if (!trig && (is_op(ch, OP_SIN) || is_op(ch, OP_COS))) {
            pcas_ast_t *arg = ast_ChildGet(ch, 0);
            if (arg && depends_on_var(arg, var)) { trig = ch; u = arg; continue; }
        }

        if (!is_const_wrt(ch, var)) { num_Cleanup(c); return NULL; }
    }

    if (n < 0 || !trig || !u) { num_Cleanup(c); return NULL; }

    /* u must be linear: u = a*var + b, with a != 0 */
    pcas_ast_t *a_node = NULL;
    if (!expo_linear_coeff(u, var, &a_node)) { num_Cleanup(c); return NULL; }
    if (!a_node || a_node->type != NODE_NUMBER || mp_rat_compare_zero(a_node->op.num) == 0) {
        if (a_node) ast_Cleanup(a_node);
        num_Cleanup(c);
        return NULL;
    }
    mp_rat a = num_Copy(a_node->op.num);
    ast_Cleanup(a_node);

    /* Precompute 1/a and 1/a^2 as rationals we’ll copy when needed */
    mp_rat inva  = num_FromInt(1); mp_rat_div(inva,  a, inva);             /* 1/a */
    mp_rat inva2 = num_FromInt(1); mp_rat_div(inva2, a, inva2); mp_rat_div(inva2, a, inva2); /* 1/a^2 */

    /* Bases */
    pcas_ast_t *sin_u = ast_MakeUnary(OP_SIN, ast_Copy(u));
    pcas_ast_t *cos_u = ast_MakeUnary(OP_COS, ast_Copy(u));

    pcas_ast_t *I_c = ast_MakeBinary(OP_MULT, ast_MakeNumber(num_Copy(inva)), ast_Copy(sin_u));  /* sin(u)/a */
    pcas_ast_t *I_s = ast_MakeBinary(OP_MULT, ast_MakeNumber(num_Copy(inva)),
                                     ast_MakeBinary(OP_MULT, N(-1), ast_Copy(cos_u)));           /* -cos(u)/a */
    simp(I_c); simp(I_s);

    /* Build up k = 1..n */
    for (int k = 1; k <= n; ++k) {
        /* x^k */
        pcas_ast_t *xk = (k == 1) ? ast_Copy(var)
                                  : ast_MakeBinary(OP_POW, ast_Copy(var), N(k));

        /* I_c(k) = x^k sin(u)/a - (k/a) * I_s(k-1) */
        pcas_ast_t *term1_c = ast_MakeBinary(OP_MULT,
                                ast_MakeNumber(num_Copy(inva)),
                                ast_MakeBinary(OP_MULT, ast_Copy(xk), ast_Copy(sin_u)));
        mp_rat k_over_a = num_FromInt(k); mp_rat_div(k_over_a, a, k_over_a);
        pcas_ast_t *term2_c = ast_MakeBinary(OP_MULT,
                                ast_MakeNumber(k_over_a),
                                I_s); /* I_s is I_s(k-1) */
        pcas_ast_t *I_c_new = ast_MakeBinary(OP_ADD, term1_c, ast_MakeBinary(OP_MULT, N(-1), term2_c));
        simp(I_c_new);

        /* I_s(k) = - x^k cos(u)/a + (k/a) * I_c(k-1) */
        pcas_ast_t *term1_s = ast_MakeBinary(OP_MULT,
                                ast_MakeNumber(num_Copy(inva)),
                                ast_MakeBinary(OP_MULT, N(-1),
                                    ast_MakeBinary(OP_MULT, ast_Copy(xk), ast_Copy(cos_u))));
        mp_rat k_over_a2 = num_FromInt(k); mp_rat_div(k_over_a2, a, k_over_a2);
        pcas_ast_t *term2_s = ast_MakeBinary(OP_MULT,
                                ast_MakeNumber(k_over_a2),
                                I_c); /* I_c is I_c(k-1) */
        pcas_ast_t *I_s_new = ast_MakeBinary(OP_ADD, term1_s, term2_s);
        simp(I_s_new);

        ast_Cleanup(I_c);
        ast_Cleanup(I_s);
        ast_Cleanup(xk);

        I_c = I_c_new;
        I_s = I_s_new;
    }

    /* Select final */
    pcas_ast_t *Result = is_op(trig, OP_COS) ? I_c : I_s;

    /* Apply numeric front factor c */
    if (mp_rat_compare_value(c, 1, 1) != 0) {
        Result = ast_MakeBinary(OP_MULT, ast_MakeNumber(num_Copy(c)), Result);
        simp(Result);
    }

    /* cleanup */
    ast_Cleanup(sin_u);
    ast_Cleanup(cos_u);
    num_Cleanup(c);
    num_Cleanup(a);
    num_Cleanup(inva);
    num_Cleanup(inva2);

    return Result;
}





/* Handle c*x*sin^2(x), c*x*cos^2(x), c*x*tan^2(x) (closed forms; avoids IBP loops). */
static pcas_ast_t *integrate_x_times_trig_square(pcas_ast_t *expr, pcas_ast_t *var) {
    if (!expr || !is_op(expr, OP_MULT)) return NULL;

    bool saw_x = false;
    OperatorType sq_kind = (OperatorType)0;
    mp_rat c = num_FromInt(1);

    for (pcas_ast_t *ch = ast_ChildGet(expr,0); ch; ch=ch->next) {
        if (!saw_x && is_var_deg1(ch, var)) { saw_x = true; continue; }
        if (!sq_kind && is_op(ch, OP_POW)) {
            pcas_ast_t *b = ast_ChildGet(ch,0), *p = ast_ChildGet(ch,1);
            if (p && p->type==NODE_NUMBER && mp_rat_compare_value(p->op.num,2,1)==0) {
                if (is_op(b, OP_SIN) || is_op(b, OP_COS) || is_op(b, OP_TAN)) {
                    pcas_ast_t *a = ast_ChildGet(b,0);
                    if (a && a->type==NODE_SYMBOL && ast_Compare(a,var)) { sq_kind = optype(b); continue; }
                }
            }
        }
        if (ch->type==NODE_NUMBER) { mp_rat_mul(c, ch->op.num, c); continue; }
        if (!is_const_wrt(ch, var)) { num_Cleanup(c); return NULL; }
    }

    if (!saw_x || !sq_kind) { num_Cleanup(c); return NULL; }

    pcas_ast_t *res = NULL;
    if (sq_kind == OP_TAN) {
        /* ∫ x tan^2 x dx = x tan x + ln|cos x| - x^2/2 */
        pcas_ast_t *x_tanx = ast_MakeBinary(OP_MULT, ast_Copy(var), ast_MakeUnary(OP_TAN, ast_Copy(var)));
        pcas_ast_t *lncos  = ast_MakeUnary(OP_LOG, ast_MakeUnary(OP_COS, ast_Copy(var)));
        pcas_ast_t *term   = ast_MakeBinary(OP_ADD, x_tanx, lncos);
        res = ast_MakeBinary(OP_ADD, term, ast_MakeBinary(OP_MULT, N(-1),
                          ast_MakeBinary(OP_DIV, ast_MakeBinary(OP_POW, ast_Copy(var), N(2)), N(2))));
    } else if (sq_kind == OP_SIN) {
        /* x sin^2 x = x*(1-cos 2x)/2 ⇒ ∫ = x^2/4 - x sin 2x /4 - cos 2x /8 */
        pcas_ast_t *x2_over4 = ast_MakeBinary(OP_DIV, ast_MakeBinary(OP_POW, ast_Copy(var), N(2)), N(4));
        pcas_ast_t *xsin2x   = ast_MakeBinary(OP_MULT, ast_Copy(var),
                               ast_MakeUnary(OP_SIN, ast_MakeBinary(OP_MULT, N(2), ast_Copy(var))));
        pcas_ast_t *cos2x    = ast_MakeUnary(OP_COS, ast_MakeBinary(OP_MULT, N(2), ast_Copy(var)));
        pcas_ast_t *res1     = ast_MakeBinary(OP_ADD, x2_over4,
                               ast_MakeBinary(OP_MULT, N(-1), ast_MakeBinary(OP_DIV, xsin2x, N(4))));
        res = ast_MakeBinary(OP_ADD, res1,
                ast_MakeBinary(OP_MULT, N(-1), ast_MakeBinary(OP_DIV, cos2x, N(8))));
    } else if (sq_kind == OP_COS) {
        /* x cos^2 x = x*(1+cos 2x)/2 ⇒ ∫ = x^2/4 + x sin 2x /4 + cos 2x /8 */
        pcas_ast_t *x2_over4 = ast_MakeBinary(OP_DIV, ast_MakeBinary(OP_POW, ast_Copy(var), N(2)), N(4));
        pcas_ast_t *xsin2x   = ast_MakeBinary(OP_MULT, ast_Copy(var),
                               ast_MakeUnary(OP_SIN, ast_MakeBinary(OP_MULT, N(2), ast_Copy(var))));
        pcas_ast_t *cos2x    = ast_MakeUnary(OP_COS, ast_MakeBinary(OP_MULT, N(2), ast_Copy(var)));
        pcas_ast_t *res1     = ast_MakeBinary(OP_ADD, x2_over4, ast_MakeBinary(OP_DIV, xsin2x, N(4)));
        res = ast_MakeBinary(OP_ADD, res1, ast_MakeBinary(OP_DIV, cos2x, N(8)));
    }

    if (!res) { num_Cleanup(c); return NULL; }
    if (mp_rat_compare_value(c,1,1)!=0)
        res = ast_MakeBinary(OP_MULT, ast_MakeNumber(c), res);
    simp(res);
    return res;
}

/* Closed-form handler for products of the shape: (const) * x * trig^2(u),
   where u is linear in 'var' (u = a*var + b). Supports sin^2, cos^2, tan^2.
   Returns an antiderivative WITHOUT recursing into integrate_node (prevents loops).
   If the pattern doesn't match, returns NULL.

   Identities used:
     sin^2(u) = (1 - cos(2u))/2
     cos^2(u) = (1 + cos(2u))/2
     tan^2(u) = sec^2(u) - 1

   Closed forms (a ≠ 0):
     ∫ x cos(κx+φ) dx =  x sin(κx+φ)/κ + cos(κx+φ)/κ^2
     ∫ x sin(κx+φ) dx = -x cos(κx+φ)/κ + sin(κx+φ)/κ^2
     ∫ x sec^2(κx+φ) dx = x tan(κx+φ)/κ + (1/κ^2) ln|cos(κx+φ)|
*/
static pcas_ast_t *rewrite_trig_square_in_product_and_integrate(pcas_ast_t *expr, pcas_ast_t *var) {
    if (!expr || !is_op(expr, OP_MULT)) return NULL;

    /* 1) Parse product: require exactly one 'x', exactly one trig^2 factor,
          and everything else numeric constants. Accumulate numeric constant 'c'. */
    bool saw_x = false;
    pcas_ast_t *trig_pow2 = NULL;  /* (sin u)^2, (cos u)^2, or (tan u)^2 */
    mp_rat c = num_FromInt(1);

    for (pcas_ast_t *f = ast_ChildGet(expr, 0); f; f = f->next) {
        if (f->type == NODE_NUMBER) {
            mp_rat_mul(c, f->op.num, c);
            continue;
        }
        if (is_var_deg1(f, var)) {
            if (saw_x) { num_Cleanup(c); return NULL; } /* more than one x */
            saw_x = true;
            continue;
        }
        if (is_op(f, OP_POW)) {
            pcas_ast_t *b = ast_ChildGet(f,0), *e = ast_ChildGet(f,1);
            if (e && e->type == NODE_NUMBER && mp_rat_compare_value(e->op.num, 2, 1) == 0 &&
                b && (is_op(b, OP_SIN) || is_op(b, OP_COS) || is_op(b, OP_TAN))) {
                if (trig_pow2) { num_Cleanup(c); return NULL; } /* more than one trig^2 */
                trig_pow2 = f;
                continue;
            }
        }
        /* Anything else must be constant wrt var; otherwise bail. */
        if (!is_const_wrt(f, var)) { num_Cleanup(c); return NULL; }
    }

    if (!saw_x || !trig_pow2) { num_Cleanup(c); return NULL; }

    /* 2) Extract u from trig^2(u) and ensure u is linear in var: u = a*var + b */
    pcas_ast_t *base = ast_ChildGet(trig_pow2, 0); /* SIN/COS/TAN */
    pcas_ast_t *u    = ast_ChildGet(base, 0);      /* argument */
    if (!u) { num_Cleanup(c); return NULL; }

    pcas_ast_t *a_node = NULL;
    if (!expo_linear_coeff(u, var, &a_node)) { num_Cleanup(c); return NULL; }   /* uses your existing helper */
    if (!a_node || a_node->type != NODE_NUMBER || mp_rat_compare_zero(a_node->op.num) == 0) {
        if (a_node) ast_Cleanup(a_node);
        num_Cleanup(c);
        return NULL; /* non-linear or a==0 */
    }
    mp_rat a = num_Copy(a_node->op.num);
    ast_Cleanup(a_node);

    /* Prepare rationals we'll need */
    mp_rat two   = num_FromInt(2);
    mp_rat inva  = num_FromInt(1); mp_rat_div(inva, a, inva);                    /* 1/a */
    mp_rat inva2 = num_FromInt(1); mp_rat_div(inva2, a, inva2); mp_rat_div(inva2, a, inva2); /* 1/a^2 */

    /* Result we'll build */
    pcas_ast_t *result = NULL;

    if (is_op(base, OP_SIN) || is_op(base, OP_COS)) {
        /* sin^2(u) or cos^2(u) */
        bool is_sin2 = is_op(base, OP_SIN);

        /* Part A: (c/2) * ∫ x dx = (c/2) * x^2/2 */
        mp_rat c_over2 = num_Copy(c); mp_rat_div(c_over2, two, c_over2);   /* c/2 */
        pcas_ast_t *Ix  = ast_MakeBinary(OP_DIV, ast_MakeBinary(OP_POW, ast_Copy(var), N(2)), N(2));  /* x^2/2 */
        pcas_ast_t *partA = ast_MakeBinary(OP_MULT, ast_MakeNumber(num_Copy(c_over2)), Ix);
        simp(partA);

        /* Part B: (± c/2) * ∫ x * cos(2u) dx, with κ = 2a */
        pcas_ast_t *two_u  = ast_MakeBinary(OP_MULT, N(2), ast_Copy(u));
        pcas_ast_t *cos_2u = ast_MakeUnary(OP_COS, ast_Copy(two_u));

        /* κ = 2a, 1/κ and 1/κ^2  */
        mp_rat twoa = num_Copy(a); mp_rat_mul(twoa, two, twoa);                         /* 2a */
        mp_rat inv_twoa  = num_FromInt(1); mp_rat_div(inv_twoa, twoa, inv_twoa);       /* 1/(2a) */
        mp_rat inv_twoa2 = num_FromInt(1); mp_rat_div(inv_twoa2, twoa, inv_twoa2); mp_rat_div(inv_twoa2, twoa, inv_twoa2); /* 1/(2a)^2 */

        /* ∫ x cos(2u) dx = x sin(2u)/(2a) + cos(2u)/(2a)^2 */
        pcas_ast_t *sin_2u = ast_MakeUnary(OP_SIN, two_u); /* two_u already a new node */
        pcas_ast_t *term1 = ast_MakeBinary(OP_MULT, ast_Copy(var), sin_2u);                    /* x sin(2u) */
        term1 = ast_MakeBinary(OP_MULT, ast_MakeNumber(num_Copy(inv_twoa)), term1);           /* / (2a) */

        pcas_ast_t *term2 = ast_MakeBinary(OP_MULT, ast_MakeNumber(num_Copy(inv_twoa2)), ast_Copy(cos_2u));

        pcas_ast_t *int_x_cos_2u = ast_MakeBinary(OP_ADD, term1, term2);
        simp(int_x_cos_2u);

        mp_rat c_over2_signed = num_Copy(c_over2);
        if (is_sin2) mp_rat_neg(c_over2_signed, c_over2_signed); /* sin^2 has minus sign */

        pcas_ast_t *partB = ast_MakeBinary(OP_MULT, ast_MakeNumber(num_Copy(c_over2_signed)), int_x_cos_2u);
        simp(partB);

        result = ast_MakeBinary(OP_ADD, partA, partB);
        simp(result);

        /* cleanup locals */
        num_Cleanup(twoa);
        num_Cleanup(inv_twoa);
        num_Cleanup(inv_twoa2);
        num_Cleanup(c_over2_signed);
        num_Cleanup(c_over2);
    } else {
        /* tan^2(u): c * ( ∫ x sec^2(u) dx - ∫ x dx ) */
        /* ∫ x sec^2(u) dx = x tan(u)/a + (1/a^2) ln|cos(u)| */
        pcas_ast_t *tanu = ast_MakeUnary(OP_TAN, ast_Copy(u));
        pcas_ast_t *x_tan_over_a = ast_MakeBinary(OP_MULT,
                                   ast_MakeNumber(num_Copy(inva)),
                                   ast_MakeBinary(OP_MULT, ast_Copy(var), tanu));   /* (1/a) * x * tan(u) */
        pcas_ast_t *ln_cosu = ast_MakeUnary(OP_LOG, ast_MakeUnary(OP_COS, ast_Copy(u)));
        pcas_ast_t *ln_term = ast_MakeBinary(OP_MULT, ast_MakeNumber(num_Copy(inva2)), ln_cosu);
        pcas_ast_t *I_sec2 = ast_MakeBinary(OP_ADD, x_tan_over_a, ln_term);
        simp(I_sec2);

        /* ∫ x dx = x^2/2 */
        pcas_ast_t *I_x = ast_MakeBinary(OP_DIV, ast_MakeBinary(OP_POW, ast_Copy(var), N(2)), N(2));

        /* c * ( I_sec2 - I_x ) */
        pcas_ast_t *diff = ast_MakeBinary(OP_ADD, I_sec2, ast_MakeBinary(OP_MULT, N(-1), I_x));
        result = ast_MakeBinary(OP_MULT, ast_MakeNumber(num_Copy(c)), diff);
        simp(result);
    }

    /* cleanup rationals */
    num_Cleanup(c);
    num_Cleanup(a);
    num_Cleanup(inva);
    num_Cleanup(inva2);
    num_Cleanup(two);

    return result;
}


/* DIRECT closed-form for ∫ x^n * (sin|cos)(u) dx, n>=0, u = a*var + b with a!=0.
   Pattern-match a single trig(u) factor and accumulate total degree of x across factors.
   Uses the finite sum from the e^{i(ax+b)} derivation.
   IMPORTANT: coeff_k does NOT include (-1)^k; the sign cycle below already accounts for it. */
static pcas_ast_t *integrate_xn_times_trig_linear(pcas_ast_t *expr, pcas_ast_t *var) {
    if (!expr || !is_op(expr, OP_MULT)) return NULL;

    /* Parse product: numeric factor c, degree n, trig node & its argument u */
    mp_rat c = num_FromInt(1);
    int n = 0;
    pcas_ast_t *trig = NULL, *u = NULL;

    for (pcas_ast_t *ch = ast_ChildGet(expr,0); ch; ch = ch->next) {
        if (ch->type == NODE_NUMBER) { mp_rat_mul(c, ch->op.num, c); continue; }

        /* accumulate x^k */
        if (ch->type == NODE_SYMBOL && ast_Compare(ch, var)) { n += 1; continue; }
        if (is_op(ch, OP_POW)) {
            pcas_ast_t *b = ast_ChildGet(ch,0), *e = ast_ChildGet(ch,1);
            if (b && b->type==NODE_SYMBOL && ast_Compare(b,var) && e && e->type==NODE_NUMBER) {
                mp_small numi, deni;
                if (mp_rat_to_ints(e->op.num,&numi,&deni)==MP_OK && deni==1 && numi>=1) { n += (int)numi; continue; }
            }
        }

        /* single trig(u) */
        if (!trig && (is_op(ch, OP_SIN) || is_op(ch, OP_COS))) {
            pcas_ast_t *arg = ast_ChildGet(ch, 0);
            if (arg && depends_on_var(arg, var)) { trig = ch; u = arg; continue; }
        }

        if (!is_const_wrt(ch, var)) { num_Cleanup(c); return NULL; }
    }
    if (!trig || !u) { num_Cleanup(c); return NULL; }

    /* u = a*var + b with a != 0 */
    pcas_ast_t *a_node = NULL;
    if (!expo_linear_coeff(u, var, &a_node)) { num_Cleanup(c); return NULL; }
    if (!a_node || a_node->type!=NODE_NUMBER || mp_rat_compare_zero(a_node->op.num)==0) {
        if (a_node) ast_Cleanup(a_node);
        num_Cleanup(c);
        return NULL;
    }
    mp_rat a = num_Copy(a_node->op.num);
    ast_Cleanup(a_node);

    /* Prebuild sin(u), cos(u) once */
    pcas_ast_t *sin_u = ast_MakeUnary(OP_SIN, ast_Copy(u));
    pcas_ast_t *cos_u = ast_MakeUnary(OP_COS, ast_Copy(u));

    /* Polynomials Ps, Pc so that result = Ps*sin(u) + Pc*cos(u) */
    pcas_ast_t *Ps = N(0), *Pc = N(0);

    /* Accumulators: inva_pow = 1/a^{k+1}, fall = n!/(n-k)! */
    mp_rat inva     = num_FromInt(1); mp_rat_div(inva, a, inva);   /* 1/a */
    mp_rat inva_pow = num_Copy(inva);                               /* 1/a^{1} */
    mp_rat fall     = num_FromInt(1);                               /* k=0: 1 */

    for (int k = 0; k <= n; ++k) {
        /* coeff_k = (n!/(n-k)!) * (1/a^{k+1})  (NO (-1)^k here) */
        mp_rat coeff = num_Copy(fall);
        mp_rat_mul(coeff, inva_pow, coeff);

        pcas_ast_t *xpow = (n-k==0) ? N(1) : ast_MakeBinary(OP_POW, ast_Copy(var), N(n-k));

        int r = k & 3; /* k mod 4 */

        if (is_op(trig, OP_COS)) {
            /* cos integral pattern: +sin, +cos, −sin, −cos */
            if (r == 0) {
                Ps = ast_MakeBinary(OP_ADD, Ps, ast_MakeBinary(OP_MULT, ast_MakeNumber(num_Copy(coeff)), xpow));
            } else if (r == 1) {
                Pc = ast_MakeBinary(OP_ADD, Pc, ast_MakeBinary(OP_MULT, ast_MakeNumber(num_Copy(coeff)), xpow));
            } else if (r == 2) {
                Ps = ast_MakeBinary(OP_ADD, Ps, ast_MakeBinary(OP_MULT, N(-1),
                        ast_MakeBinary(OP_MULT, ast_MakeNumber(num_Copy(coeff)), xpow)));
            } else { /* r == 3 */
                Pc = ast_MakeBinary(OP_ADD, Pc, ast_MakeBinary(OP_MULT, N(-1),
                        ast_MakeBinary(OP_MULT, ast_MakeNumber(num_Copy(coeff)), xpow)));
            }
        } else {
            /* sin integral pattern: −cos, +sin, +cos, −sin */
            if (r == 0) {
                Pc = ast_MakeBinary(OP_ADD, Pc, ast_MakeBinary(OP_MULT, N(-1),
                        ast_MakeBinary(OP_MULT, ast_MakeNumber(num_Copy(coeff)), xpow)));
            } else if (r == 1) {
                Ps = ast_MakeBinary(OP_ADD, Ps, ast_MakeBinary(OP_MULT, ast_MakeNumber(num_Copy(coeff)), xpow));
            } else if (r == 2) {
                Pc = ast_MakeBinary(OP_ADD, Pc, ast_MakeBinary(OP_MULT, ast_MakeNumber(num_Copy(coeff)), xpow));
            } else { /* r == 3 */
                Ps = ast_MakeBinary(OP_ADD, Ps, ast_MakeBinary(OP_MULT, N(-1),
                        ast_MakeBinary(OP_MULT, ast_MakeNumber(num_Copy(coeff)), xpow)));
            }
        }

        simp(Ps); simp(Pc);
        num_Cleanup(coeff);

        /* Update accumulators for next k (stop before multiplying by zero). */
        if (k < n) {
            mp_rat_mul(inva_pow, inva, inva_pow);        /* 1/a^{k+2} */
            mp_rat mul = num_FromInt(n - k);             /* (n-k) */
            mp_rat_mul(fall, mul, fall);                 /* n!/(n-(k+1))! */
            num_Cleanup(mul);
        }
    }

    /* Combine into Ps*sin(u) + Pc*cos(u) */
    pcas_ast_t *res = ast_MakeBinary(
        OP_ADD,
        ast_MakeBinary(OP_MULT, Ps, sin_u),
        ast_MakeBinary(OP_MULT, Pc, cos_u)
    );

    /* Apply numeric factor c if needed */
    if (mp_rat_compare_value(c,1,1)!=0) {
        res = ast_MakeBinary(OP_MULT, ast_MakeNumber(num_Copy(c)), res);
    }

    /* Expand (distribute) and then simplify */
    expand(res, EXP_DISTRIB_NUMBERS | EXP_DISTRIB_MULTIPLICATION | EXP_DISTRIB_ADDITION);
    simp(res);

    /* cleanup */
    num_Cleanup(c);
    num_Cleanup(a);
    num_Cleanup(inva);
    num_Cleanup(inva_pow);
    num_Cleanup(fall);

    return res;
}

/* helper: detect x^n * tan(linear) with n>=1 */
static bool is_poly_times_tan_linear(pcas_ast_t *expr, pcas_ast_t *var) {
    if (!is_op(expr, OP_MULT)) return false;

    int n = 0;
    pcas_ast_t *one_tan = NULL;

    for (pcas_ast_t *ch = ast_ChildGet(expr,0); ch; ch=ch->next) {
        if (ch->type == NODE_NUMBER) continue;

        if (ch->type == NODE_SYMBOL && ast_Compare(ch, var)) { n += 1; continue; }
        if (is_op(ch, OP_POW)) {
            pcas_ast_t *b = ast_ChildGet(ch,0), *e = ast_ChildGet(ch,1);
            if (b && b->type==NODE_SYMBOL && ast_Compare(b,var) && e && e->type==NODE_NUMBER) {
                mp_small numi, deni;
                if (mp_rat_to_ints(e->op.num,&numi,&deni)==MP_OK && deni==1 && numi>=1) { n += (int)numi; continue; }
            }
        }
        if (!one_tan && is_op(ch, OP_TAN)) {
            pcas_ast_t *u = ast_ChildGet(ch,0);
            if (u && depends_on_var(u, var)) one_tan = ch;
            continue;
        }

        if (!is_const_wrt(ch, var)) return false;
    }
    return (n >= 1) && (one_tan != NULL);
}

/* ∫ (const) * x^n * (sin^2|cos^2)(u) dx,  n>=0,  u = a*x + b with a≠0.
   Closed form without recursion. Expands result at the end.
   Return NULL if pattern not matched. */
static pcas_ast_t *integrate_xn_times_trig_square_linear(pcas_ast_t *expr, pcas_ast_t *var) {
    if (!expr || !is_op(expr, OP_MULT)) return NULL;

    /* Parse product: collect numeric const c, degree n, and exactly one (sin|cos)^2(u). */
    mp_rat c = num_FromInt(1);
    int n = 0;
    pcas_ast_t *trig_pow2 = NULL;      /* node: POW( SIN/ COS (u) , 2 ) */
    OperatorType trig_kind = (OperatorType)0; /* OP_SIN or OP_COS */
    pcas_ast_t *u = NULL;

    for (pcas_ast_t *ch = ast_ChildGet(expr, 0); ch; ch = ch->next) {
        if (ch->type == NODE_NUMBER) { mp_rat_mul(c, ch->op.num, c); continue; }

        /* x or x^k */
        if (ch->type == NODE_SYMBOL && ast_Compare(ch, var)) { n += 1; continue; }
        if (is_op(ch, OP_POW)) {
            pcas_ast_t *b = ast_ChildGet(ch,0), *e = ast_ChildGet(ch,1);
            if (b && b->type==NODE_SYMBOL && ast_Compare(b,var) && e && e->type==NODE_NUMBER) {
                mp_small numi, deni;
                if (mp_rat_to_ints(e->op.num, &numi, &deni)==MP_OK && deni==1 && numi>=1) {
                    n += (int)numi; continue;
                }
            }
        }

        /* (sin|cos)^2(u) */
        if (is_op(ch, OP_POW)) {
            pcas_ast_t *b = ast_ChildGet(ch,0), *e = ast_ChildGet(ch,1);
            if (b && (is_op(b, OP_SIN) || is_op(b, OP_COS)) &&
                e && e->type==NODE_NUMBER && mp_rat_compare_value(e->op.num, 2, 1)==0) {

                pcas_ast_t *arg = ast_ChildGet(b,0);
                if (arg && depends_on_var(arg, var)) {
                    if (trig_pow2) { num_Cleanup(c); return NULL; } /* more than one */
                    trig_pow2 = ch;
                    trig_kind = optype(b);
                    u = arg;
                    continue;
                }
            }
        }

        if (!is_const_wrt(ch, var)) { num_Cleanup(c); return NULL; }
    }

    if (!trig_pow2 || !u || n < 0) { num_Cleanup(c); return NULL; }

    /* u must be linear in var: u = a*x + b (a ≠ 0) */
    pcas_ast_t *a_node = NULL;
    if (!expo_linear_coeff(u, var, &a_node)) { num_Cleanup(c); return NULL; }
    if (!a_node || a_node->type!=NODE_NUMBER || mp_rat_compare_zero(a_node->op.num)==0) {
        if (a_node) ast_Cleanup(a_node);
        num_Cleanup(c);
        return NULL;
    }
    mp_rat a = num_Copy(a_node->op.num);
    ast_Cleanup(a_node);

    /* Helper: make x^k */
    pcas_ast_t *x_pow_k = NULL;
    #define MAKE_X_POW(k) ( (k)==0 ? N(1) : ((k)==1 ? ast_Copy(var) : ast_MakeBinary(OP_POW, ast_Copy(var), N(k))) )

    /* Build cos(2u) and sin(2u) with distinct 2u nodes to avoid aliasing */
    pcas_ast_t *two_u_for_cos = ast_MakeBinary(OP_MULT, N(2), ast_Copy(u));
    pcas_ast_t *two_u_for_sin = ast_MakeBinary(OP_MULT, N(2), ast_Copy(u));
    pcas_ast_t *cos_2u = ast_MakeUnary(OP_COS, two_u_for_cos);
    pcas_ast_t *sin_2u = ast_MakeUnary(OP_SIN, two_u_for_sin);

    /* Part A: (c/2) * ∫ x^n dx = (c/2) * x^{n+1}/(n+1) */
    mp_rat c_over_2 = num_Copy(c); mp_rat_div(c_over_2, num_FromInt(2), c_over_2);
    x_pow_k = MAKE_X_POW(n+1);
    pcas_ast_t *partA = ast_MakeBinary(OP_MULT,
                        ast_MakeNumber(num_Copy(c_over_2)),
                        ast_MakeBinary(OP_DIV, x_pow_k, N(n+1)));
    simp(partA);

    /* Part B: ± (c/2) * ∫ x^n * cos(2u) dx  ( + for cos^2, − for sin^2 ) */
    pcas_ast_t *partB = NULL;
    {
        /* Build product fresh for the trusted finite-sum integrator */
        pcas_ast_t *prod = ast_MakeBinary(OP_MULT, MAKE_X_POW(n), ast_Copy(cos_2u));
        pcas_ast_t *Int  = integrate_xn_times_trig_linear(prod, var);
        ast_Cleanup(prod);
        if (!Int) Int = N(0); /* safety */

        pcas_ast_t *coef = ast_MakeNumber(num_Copy(c_over_2));
        if (trig_kind == OP_SIN) {
            coef = ast_MakeBinary(OP_MULT, N(-1), coef); /* minus for sin^2 */
        }
        partB = ast_MakeBinary(OP_MULT, coef, Int);
        simp(partB);
    }

    /* Result */
    pcas_ast_t *res = ast_MakeBinary(OP_ADD, partA, partB);
    simp(res);

    /* Expand nicely */
    expand(res, EXP_DISTRIB_NUMBERS | EXP_DISTRIB_MULTIPLICATION | EXP_DISTRIB_ADDITION);
    simp(res);

    /* cleanup */
    num_Cleanup(c);
    num_Cleanup(a);
    num_Cleanup(c_over_2);
    ast_Cleanup(sin_2u);
    ast_Cleanup(cos_2u);

    return res;

    #undef MAKE_X_POW
}
/* OPTIONAL: one IBP for x^n * tan(u), u = a*var + b, a!=0
   u' = a.  ∫ x^n tan(u) dx = -(x^n/a) ln(cos u) + (n/a) ∫ x^{n-1} ln(cos u) dx
   This lowers the poly degree and avoids recursion depth loops. */
static pcas_ast_t *ibp_poly_times_tan_linear_once(pcas_ast_t *expr, pcas_ast_t *var) {
    if (!expr || !is_op(expr, OP_MULT)) return NULL;

    int n = 0;
    pcas_ast_t *tan_u = NULL, *u = NULL;
    mp_rat c = num_FromInt(1);

    for (pcas_ast_t *ch = ast_ChildGet(expr,0); ch; ch=ch->next) {
        if (ch->type == NODE_NUMBER) { mp_rat_mul(c, ch->op.num, c); continue; }
        if (!tan_u && is_op(ch, OP_TAN)) {
            pcas_ast_t *arg = ast_ChildGet(ch,0);
            if (arg && depends_on_var(arg, var)) { tan_u = ch; u = arg; continue; }
        }
        if (ch->type == NODE_SYMBOL && ast_Compare(ch, var)) { n += 1; continue; }
        if (is_op(ch, OP_POW)) {
            pcas_ast_t *b = ast_ChildGet(ch,0), *e = ast_ChildGet(ch,1);
            if (b && b->type==NODE_SYMBOL && ast_Compare(b,var) && e && e->type==NODE_NUMBER) {
                mp_small num, den;
                if (mp_rat_to_ints(e->op.num,&num,&den)==MP_OK && den==1 && num>=1) { n += (int)num; continue; }
            }
        }
        if (!is_const_wrt(ch, var)) { num_Cleanup(c); return NULL; }
    }
    if (!tan_u) { num_Cleanup(c); return NULL; }

    /* u linear? */
    pcas_ast_t *a_node = NULL;
    if (!expo_linear_coeff(u, var, &a_node)) { num_Cleanup(c); return NULL; }
    if (!a_node || a_node->type!=NODE_NUMBER || mp_rat_compare_zero(a_node->op.num)==0) {
        if (a_node) ast_Cleanup(a_node);
        num_Cleanup(c);
        return NULL;
    }
    mp_rat a = num_Copy(a_node->op.num);
    ast_Cleanup(a_node);

    /* -(x^n/a) ln(cos u) */
    pcas_ast_t *xpow = (n==0) ? N(1) : ast_MakeBinary(OP_POW, ast_Copy(var), N(n));
    pcas_ast_t *lncos = ast_MakeUnary(OP_LOG, ast_MakeUnary(OP_COS, ast_Copy(u)));
    mp_rat inva = num_FromInt(1); mp_rat_div(inva, a, inva);
    pcas_ast_t *lead = ast_MakeBinary(OP_MULT,
                         ast_MakeNumber(inva),
                         ast_MakeBinary(OP_MULT, ast_MakeBinary(OP_MULT, N(-1), xpow), lncos));
    simp(lead);

    /* +(n/a) ∫ x^{n-1} ln(cos u) dx  (leave to general integrator) */
    pcas_ast_t *tail = NULL;
    if (n >= 1) {
        pcas_ast_t *xpowm1 = (n==1) ? ast_Copy(var) : ast_MakeBinary(OP_POW, ast_Copy(var), N(n-1));
        pcas_ast_t *lncos2  = ast_MakeUnary(OP_LOG, ast_MakeUnary(OP_COS, ast_Copy(u)));
        pcas_ast_t *prod    = ast_MakeBinary(OP_MULT, xpowm1, lncos2);
        pcas_ast_t *I       = integrate_node(prod, var);
        if (!I) { ast_Cleanup(lead); num_Cleanup(a); num_Cleanup(c); return NULL; }
        mp_rat n_over_a = num_FromInt(n); mp_rat_div(n_over_a, a, n_over_a);
        tail = ast_MakeBinary(OP_MULT, ast_MakeNumber(n_over_a), I);
        simp(tail);
    } else {
        tail = N(0);
    }

    pcas_ast_t *sum = ast_MakeBinary(OP_ADD, lead, tail);
    if (mp_rat_compare_value(c,1,1)!=0) {
        sum = ast_MakeBinary(OP_MULT, ast_MakeNumber(num_Copy(c)), sum);
        simp(sum);
    }

    num_Cleanup(a);
    num_Cleanup(c);
    return sum;
}

/* ∫ x^n ln(x) * (sin|cos)(a*x + b) dx, with n>=1 and linear phase.
   Strategy: one IBP with u = ln(x), dv = x^n * trig(a*x+b) dx.
   Then ∫ = ln(x)*V  -  ∫ (V/x) dx, where V = ∫ x^n * trig(a*x+b) dx
   and the tail lowers polynomial degree, terminating via existing handlers. */
static pcas_ast_t *integrate_poly_log_times_trig_linear(pcas_ast_t *expr, pcas_ast_t *var) {
    if (!expr || !is_op(expr, OP_MULT)) return NULL;

    bool saw_ln = false;
    int n = -1;
    bool saw_trig = false;

    /* Scan: need exactly one ln(x), one trig(sin|cos)(depends on var), and x^n (n>=1). Others must be numeric constants. */
    for (pcas_ast_t *ch = ast_ChildGet(expr, 0); ch; ch = ch->next) {
        if (ch->type == NODE_NUMBER) continue;

        if (!saw_ln && is_op(ch, OP_LOG) && is_ln_of_var_either_node(ch, var)) {
            saw_ln = true;
            continue;
        }

        if (n < 0) {
            int deg;
            if (read_poly_power_of_var(ch, var, &deg)) { n = deg; continue; }
        }

        if (!saw_trig && (is_op(ch, OP_SIN) || is_op(ch, OP_COS))) {
            pcas_ast_t *arg = ast_ChildGet(ch, 0);
            if (arg && depends_on_var(arg, var)) { saw_trig = true; continue; }
        }

        /* Anything else that depends on var => not our pattern */
        if (!is_const_wrt(ch, var)) return NULL;
    }

    if (!(saw_ln && saw_trig && n >= 1)) return NULL;

    /* Build dv = expr / ln(x): copy product but skip exactly one ln(x) factor */
    pcas_ast_t *dv_prod = ast_MakeNumber(num_FromInt(1));
    bool ln_removed = false;
    for (pcas_ast_t *ch = ast_ChildGet(expr, 0); ch; ch = ch->next) {
        if (!ln_removed && is_op(ch, OP_LOG) && is_ln_of_var_either_node(ch, var)) {
            ln_removed = true;
            continue;
        }
        dv_prod = ast_MakeBinary(OP_MULT, dv_prod, ast_Copy(ch));
    }
    simp(dv_prod);
    if (!ln_removed) { ast_Cleanup(dv_prod); return NULL; }

    /* V = ∫ x^n * trig(a*x+b) dx via the closed-form handler (no recursion loops) */
    pcas_ast_t *V = integrate_xn_times_trig_linear(dv_prod, var);
    ast_Cleanup(dv_prod);
    if (!V) return NULL;

    /* term1 = ln(x) * V (normalize ln as unary LOG(x)) */
    pcas_ast_t *lnx   = ast_MakeUnary(OP_LOG, ast_Copy(var));
    pcas_ast_t *term1 = ast_MakeBinary(OP_MULT, lnx, ast_Copy(V));

    /* tail = ∫ (V/x) dx */
    pcas_ast_t *V_over_x = ast_MakeBinary(OP_DIV, V, ast_Copy(var));
    simp(V_over_x);
    pcas_ast_t *tail = integrate_node(V_over_x, var);
    if (!tail) { ast_Cleanup(term1); return NULL; }

    /* result = term1 - tail  => term1 + (-1)*tail */
    pcas_ast_t *res = ast_MakeBinary(OP_ADD, term1,
                       ast_MakeBinary(OP_MULT, ast_MakeNumber(num_FromInt(-1)), tail));
    simp(res);
    return res;
}



/* Product integrator: prefer finite/closed-form handlers first to avoid IBP loops. */
static pcas_ast_t *integrate_product(pcas_ast_t *expr, pcas_ast_t *var) {
    if (!expr || !is_op(expr, OP_MULT)) return NULL;

    /* --- DEBUG-SAFE fast path: exactly x^n * sin(x) or x^n * cos(x) --- */
    {
        int deg = -1;
        pcas_ast_t *the_trig = NULL;
        bool bad = false;

        for (pcas_ast_t *ch = ast_ChildGet(expr,0); ch; ch = ch->next) {
            if (ch->type == NODE_NUMBER || is_const_wrt(ch, var)) continue;

            if (!the_trig && (isoptype(ch, OP_SIN) || isoptype(ch, OP_COS))) {
                pcas_ast_t *a = ast_ChildGet(ch, 0);
                if (a && depends_on_var(a, var)) { the_trig = ch; continue; }
            }

            if (deg < 0) {
                int dtmp;
                if (read_poly_power_of_var(ch, var, &dtmp)) { deg = dtmp; continue; }
            }

            bad = true; break;
        }

        if (!bad && the_trig && deg >= 0) {
            pcas_ast_t *special = integrate_xn_times_trig_linear(expr, var);
            if (special) return special;
        }
    }

    /* 0) Very common trig×trig shortcuts (sin·cos, sec·tan, csc·cot). */
    {
        pcas_ast_t *sp = integrate_special_trig_product(expr, var);
        if (sp) return sp;
    }

    /* 0.5) x^n * (sin^2|cos^2)(a x + b), a!=0  (closed-form; NO expand) */
    {
        pcas_ast_t *sq = integrate_xn_times_trig_square_linear(expr, var);
        if (sq) return sq;
    }

    /* 1) Pure poly×log: x^n (ln x)^m */
    {
        pcas_ast_t *pl = integrate_poly_times_log(expr, var);
        if (pl) return pl;
    }

    /* 2) Poly×trig (linear phase): x^n sin(ax+b) or x^n cos(ax+b) — finite sum */
    {
        pcas_ast_t *pt = integrate_xn_times_trig_linear(expr, var);
        if (pt) return pt;
    }

    /* 3) Poly×log×trig (linear) — one-shot IBP around ln(x) with finite-sum core */
    {
        pcas_ast_t *plt = integrate_poly_log_times_trig_linear(expr, var);
        if (plt) return plt;
    }

    /* 4) One-step IBP for poly×(sin|cos) (depth guarded) */
    if (s_ibp_enabled) {
        pcas_ast_t *t = ibp_poly_trig_once(expr, var);
        if (t) return t;
    }

    /* 4.5) OPTIONAL: one-step IBP for x^n * tan(a x + b) to avoid “no-op”.
            Comment this block out if you prefer to leave tan products unsupported. */
    if (s_ibp_enabled) {
        pcas_ast_t *tt = ibp_poly_times_tan_linear_once(expr, var);
        if (tt) return tt;
    }

    /* 5) Trig-only >1 factor? skip to avoid loops. */
    {
        int nonconst = 0, triglike = 0;
        for (pcas_ast_t *ch = ast_ChildGet(expr,0); ch; ch=ch->next) {
            if (!is_const_wrt(ch, var)) {
                nonconst++;
                if (isoptype(ch, OP_SIN) || isoptype(ch, OP_COS) ||
                    is_tan_of_var(ch,var) || is_sec_of_var(ch,var) ||
                    is_csc_of_var(ch,var) || is_cot_of_var(ch,var))
                    triglike++;
            }
        }
        if (nonconst >= 2 && triglike == nonconst) return NULL;
    }

    /* 6) Constant-factor extraction → recurse on the var-dependent rest. */
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
    ast_Cleanup(rest_factor);
    return NULL;
}


/* === NEW: gather sqrt(Q) in numerator and constant factor (defaults to 1) === */
static bool split_root_times_const(pcas_ast_t *num, pcas_ast_t **root_out, mp_rat *c_out) {
    if (!num || !root_out || !c_out) return false;

    *root_out = NULL;
    mp_rat c = num_FromInt(1); /* product of numeric constants */

    if (is_op(num, OP_MULT)) {
        for (pcas_ast_t *ch = ast_ChildGet(num, 0); ch; ch = ch->next) {
            if (!*root_out && is_sqrt_like(ch)) { *root_out = ch; continue; }
            if (ch->type == NODE_NUMBER) { mp_rat_mul(c, ch->op.num, c); continue; }
            /* any other var-dependent factor -> not our pattern */
            if (!is_const_wrt(ch, NULL)) { num_Cleanup(c); return false; }
        }
    } else {
        if (is_sqrt_like(num)) { *root_out = num; }
        else if (num->type == NODE_NUMBER) { mp_rat_mul(c, num->op.num, c); }
        else { num_Cleanup(c); return false; }
    }

    if (!*root_out) { num_Cleanup(c); return false; }
    *c_out = c;
    return true;
}

/* === NEW: gather x in denominator and constant factor (defaults to 1) === */
static bool split_var_times_const_in_den(pcas_ast_t *den, pcas_ast_t *var, mp_rat *c_out) {
    if (!den || !var || !c_out) return false;

    bool saw_x = false;
    mp_rat c = num_FromInt(1);

    if (is_op(den, OP_MULT)) {
        for (pcas_ast_t *ch = ast_ChildGet(den, 0); ch; ch = ch->next) {
            if (!saw_x && is_var_deg1(ch, var)) { saw_x = true; continue; }
            if (ch->type == NODE_NUMBER) { mp_rat_mul(c, ch->op.num, c); continue; }
            if (!is_const_wrt(ch, var)) { num_Cleanup(c); return false; }
        }
    } else {
        if (is_var_deg1(den, var)) { saw_x = true; }
        else if (den->type == NODE_NUMBER) { mp_rat_mul(c, den->op.num, c); }
        else { num_Cleanup(c); return false; }
    }

    if (!saw_x) { num_Cleanup(c); return false; }
    *c_out = c;
    return true;
}

/* === NEW: ∫ [ c1*sqrt(Q(x)) ] / [ c2*x ] dx, where Q(x)=x^2 - A^2  ===
   returns NULL when pattern doesn't match */
static pcas_ast_t *integrate_root_over_x(pcas_ast_t *num, pcas_ast_t *den, pcas_ast_t *var) {
    if (!num || !den || !var) return NULL;

    /* 1) identify sqrt(Q(x)) in numerator and x in denominator; collect constants */
    pcas_ast_t *root_like = NULL;
    mp_rat c_num = num_FromInt(0), c_den = num_FromInt(0);
    if (!split_root_times_const(num, &root_like, &c_num)) { num_Cleanup(c_num); return NULL; }
    if (!split_var_times_const_in_den(den, var, &c_den))   { num_Cleanup(c_num); num_Cleanup(c_den); return NULL; }

    /* 2) grab Q(x) and complete the square; require Q(x) = x^2 - A^2 */
    pcas_ast_t *poly = NULL;
    if (!extract_radicand(root_like, &poly) || !poly) { num_Cleanup(c_num); num_Cleanup(c_den); return NULL; }

    int sgn = 0; mp_rat h = num_FromInt(0), K = num_FromInt(0);
    if (!complete_square_simple(poly, var, &sgn, &h, &K)) { num_Cleanup(c_num); num_Cleanup(c_den); num_Cleanup(h); num_Cleanup(K); return NULL; }

    /* we need: sgn = +1 (x^2 + ...), h = 0, and K < 0  ⇒ Q = (x - 0)^2 + K = x^2 - A^2 with A^2 = -K */
    bool h_is_zero = (mp_rat_compare_zero(h) == 0);
    bool K_is_neg  = (mp_rat_sign(K) < 0);

    if (!(sgn > 0 && h_is_zero && K_is_neg)) {
        num_Cleanup(c_num); num_Cleanup(c_den); num_Cleanup(h); num_Cleanup(K);
        return NULL;
    }

    /* A = sqrt(-K) as an AST: ROOT(2, -K) */
    mp_rat Kneg = num_FromInt(0); mp_rat_sub(num_FromInt(0), K, Kneg); /* -K */
    pcas_ast_t *A = ast_MakeBinary(OP_ROOT, N(2), ast_MakeNumber(Kneg));

    /* 3) Build F(x) = sqrt(Q(x)) + A * asin(A/x)  */
    pcas_ast_t *sqrtQ = ast_Copy(root_like); /* reuse the exact sqrt(Q) form from input */
    pcas_ast_t *A_over_x = ast_MakeBinary(OP_DIV, ast_Copy(A), ast_Copy(var));
    pcas_ast_t *asin_term = ast_MakeUnary(OP_SIN_INV, A_over_x); /* arcsin(A/x) */
    pcas_ast_t *A_times_asin = ast_MakeBinary(OP_MULT, A, asin_term);
    pcas_ast_t *Fx = ast_MakeBinary(OP_ADD, sqrtQ, A_times_asin);

    /* 4) Scale by numeric factor (c_num / c_den) if needed */
    mp_rat scale = num_FromInt(1);
    mp_rat_div(c_num, c_den, scale);
    pcas_ast_t *result = is_one(ast_MakeNumber(scale)) ? Fx
                        : ast_MakeBinary(OP_MULT, ast_MakeNumber(scale), Fx);

    /* 5) clean & simplify */
    simp(result);
    num_Cleanup(c_num); num_Cleanup(c_den); num_Cleanup(h); num_Cleanup(K);
    return result;
}

/* Front-door catch-all for (const)*x^n*(sin|cos)(u) with u linear in var.
   Returns a finite, non-recursive closed form or NULL if not matched. */
static pcas_ast_t *integrate_poly_trig_frontdoor(pcas_ast_t *expr, pcas_ast_t *var) {
    if (!expr || !is_op(expr, OP_MULT)) return NULL;

    int n = 0;
    pcas_ast_t *trig = NULL, *u = NULL;

    for (pcas_ast_t *ch = ast_ChildGet(expr,0); ch; ch = ch->next) {
        if (ch->type == NODE_NUMBER) continue;

        /* accumulate all x and x^k */
        int deg;
        if (read_poly_power_of_var(ch, var, &deg)) { n += deg; continue; }

        /* single trig(u) that depends on var */
        if (!trig && (is_op(ch, OP_SIN) || is_op(ch, OP_COS))) {
            pcas_ast_t *arg = ast_ChildGet(ch, 0);
            if (arg && depends_on_var(arg, var)) { trig = ch; u = arg; continue; }
        }

        /* anything else var-dependent -> not this pattern */
        if (!is_const_wrt(ch, var)) return NULL;
    }

    if (!trig) return NULL;

    /* u must be linear in var: u = a*var + b, a != 0 */
    pcas_ast_t *a_node = NULL;
    if (!expo_linear_coeff(u, var, &a_node)) return NULL;
    if (!a_node || a_node->type != NODE_NUMBER || mp_rat_compare_zero(a_node->op.num) == 0) {
        if (a_node) ast_Cleanup(a_node);
        return NULL;
    }
    ast_Cleanup(a_node);

    /* Use your closed-form finite sum builder */
    return integrate_xn_times_trig_linear(expr, var);
}

/* ---------------- Main integrator ---------------- */
/* ---------------- Main integrator ---------------- */
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
            /* ∫ x dx = x^2/2 */
            pcas_ast_t *res = ast_MakeBinary(OP_DIV,
                ast_MakeBinary(OP_POW, ast_Copy(var), N(2)), N(2));
            simp(res);
            return res;
        } else {
            /* ∫ c dx = c*x */
            pcas_ast_t *res = ast_MakeBinary(OP_MULT, ast_Copy(expr), ast_Copy(var));
            simp(res);
            return res;
        }
    }

    if (expr->type != NODE_OPERATOR) return NULL;

    OperatorType op = optype(expr);

    /* Sums: integrate termwise */
    if (op == OP_ADD) {
        return integrate_sum(expr, var);
    }

    /* Products: special trig products first, then targeted IBP and constant-factor extraction */
    if (op == OP_MULT) {
        /* NEW: front-door for x^n * (sin|cos)(linear) — mirror the ln(x) fast path */
        {
            pcas_ast_t *pt_front = integrate_poly_trig_frontdoor(expr, var);
            if (pt_front) return pt_front;
        }

        /* sin^m x cos^n x (m odd or n odd) */
        pcas_ast_t *sp1 = integrate_sin_cos_product(expr, var);
        if (sp1) return sp1;

        /* tan^m x sec^n x (n even; plus n odd & m even) */
        pcas_ast_t *sp2 = integrate_tan_sec_product(expr, var);
        if (sp2) return sp2;

        return integrate_product(expr, var);
    }

    /* Powers: x^n rule, e^(a x) rule, sec^2/csc^2, tan^2, etc. */
    if (op == OP_POW)  {
        pcas_ast_t *r = integrate_power(expr, var);
        if (r) return r;

        /* Reduction formulas for sin^n x and cos^n x */
        pcas_ast_t *r2 = integrate_sin_power_node(expr, var);
        if (r2) return r2;
        pcas_ast_t *r3 = integrate_cos_power_node(expr, var);
        if (r3) return r3;
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

    /* Quadratic-under-root and related quotient patterns */
    if (op == OP_DIV) {
        pcas_ast_t *num = ast_ChildGet(expr,0), *den = ast_ChildGet(expr,1);

        /* sqrt(Q(x))/x with Q(x)=x^2 - A^2 (and numeric factors handled inside) */
        {
            pcas_ast_t *sp = integrate_root_over_x(num, den, var);
            if (sp) return sp;
        }

        /* (linear)/(quadratic) split: (n1 x + n0)/(a2 x^2 + a1 x + a0) */
        {
            pcas_ast_t *lq = integrate_linear_over_quadratic(num, den, var);
            if (lq) return lq;
        }

        /* Case A: 1 / sqrt(Q(x))  → arcsin/asinh */
        if (num && num->type==NODE_NUMBER && mp_rat_compare_value(num->op.num,1,1)==0) {
            pcas_ast_t *qrt = integrate_quadratic_root(den, var);
            if (qrt) return qrt;
        }

        /* Case B: c / ( k * x * sqrt(Q(x)) ) */
        {
            pcas_ast_t *base = integrate_recip_x_times_quadratic_root(den, var);
            if (base) {
                if (num && num->type == NODE_NUMBER) {
                    pcas_ast_t *res = ast_MakeBinary(OP_MULT, ast_MakeNumber(num_Copy(num->op.num)), base);
                    simp(res);
                    return res;
                }
                return base;
            }
        }

        /* Case C: 1 / (a x^2 + b x + c) */
        if (num && num->type==NODE_NUMBER && mp_rat_compare_value(num->op.num,1,1)==0) {
            pcas_ast_t *rq = integrate_recip_quadratic_poly(den, var);
            if (rq) return rq;
        }

        /* Case D: fallback sqrt(x^2 - a^2) / (k*x) normalization */
        if (num && is_sqrt_like(num)) {
            bool ok = false, saw_var = false;
            mp_rat k = num_FromInt(1);
            if (den->type == NODE_SYMBOL && ast_Compare(den, var)) {
                ok = true; saw_var = true;
            } else if (is_op(den, OP_MULT)) {
                ok = true;
                for (pcas_ast_t *f = ast_ChildGet(den, 0); f && ok; f = f->next) {
                    if (f->type == NODE_SYMBOL && ast_Compare(f, var)) {
                        if (saw_var) ok = false;
                        else saw_var = true;
                    } else if (f->type == NODE_NUMBER) {
                        mp_rat_mul(k, f->op.num, k);
                    } else {
                        ok = false;
                    }
                }
                if (!saw_var) ok = false;
            }

            if (ok) {
                pcas_ast_t *base = integrate_sqrt_x2_minus_a2_over_x(num, ast_Copy(var), var);
                if (base) {
                    pcas_ast_t *res = base;
                    if (mp_rat_compare_value(k, 1, 1) != 0) {
                        mp_rat invk = num_FromInt(1); mp_rat_div(invk, k, invk);
                        res = ast_MakeBinary(OP_MULT, ast_MakeNumber(invk), base);
                        simp(res);
                    }
                    num_Cleanup(k);
                    return res;
                }
            }
            num_Cleanup(k);
        }
    }

    /* Direct forms:  Q(x)^(-1/2)  → 1/sqrt(Q) handler;  Q(x)^(-1) → rational quadratic handler */
    if (op == OP_POW || op == OP_ROOT) {
        if (is_op(expr, OP_POW)) {
            pcas_ast_t *B = ast_ChildGet(expr,0), *E = ast_ChildGet(expr,1);
            if (E && E->type==NODE_NUMBER) {
                /* exponent = -1/2 */
                if (mp_rat_compare_value(E->op.num, -1, 2)==0) {
                    pcas_ast_t *qrt = integrate_quadratic_root(
                        ast_MakeBinary(OP_ROOT, N(2), ast_Copy(B)), var);
                    if (qrt) return qrt;
                }
                /* exponent = -1  → 1/(quadratic) */
                if (mp_rat_compare_value(E->op.num, -1, 1)==0) {
                    pcas_ast_t *rq = integrate_recip_quadratic_poly(B, var);
                    if (rq) return rq;
                }
            }
        }
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
