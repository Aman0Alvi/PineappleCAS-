#include "integral.h"
#include "cas.h"
#include "identities.h"

/* Provided elsewhere */
void replace_node(pcas_ast_t *dst, pcas_ast_t *src);

/* Forward declaration so callers compile before the definition appears. */
static pcas_ast_t *integrate_node(pcas_ast_t *expr, pcas_ast_t *var);

/* ---------------- IBP controls ---------------- */
static bool s_ibp_enabled = true;
void integral_set_ibp_enabled(bool on) { s_ibp_enabled = on; }

static int  s_ibp_depth = 0;
static const int S_IBP_MAX_DEPTH = 8;

/* ---------------- Small helpers ---------------- */

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

static inline bool is_const_wrt(pcas_ast_t *e, pcas_ast_t *var) {
    return !depends_on_var(e, var);
}

static inline bool is_var_deg1(pcas_ast_t *e, pcas_ast_t *var) {
    return e && e->type == NODE_SYMBOL && ast_Compare(e, var);
}

static bool is_op(pcas_ast_t *e, OperatorType k) {
    return e && e->type == NODE_OPERATOR && optype(e) == k;
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

/* From a product, try to find exactly one x and exactly one sqrt(Q(x)).
   Allow numeric constants as extra factors; reject any other var-dependent factor. */
static bool split_x_times_root(pcas_ast_t *den, pcas_ast_t *var, pcas_ast_t **root_like_out) {
    if (!den || !is_op(den, OP_MULT)) return false;

    pcas_ast_t *xnode = NULL, *root_like = NULL;

    for (pcas_ast_t *ch = ast_ChildGet(den, 0); ch; ch = ch->next) {
        if (!xnode && is_var_deg1(ch, var)) {
            xnode = ch; 
            continue;
        }
        if (!root_like && is_sqrt_like(ch)) {
            root_like = ch;
            continue;
        }
        /* permit pure numeric constants; anything else that depends on var => bail */
        if (!is_const_wrt(ch, var)) return false;
    }

    if (xnode && root_like) {
        if (root_like_out) *root_like_out = root_like;
        return true;
    }
    return false;
}

static bool is_one(pcas_ast_t *e) {
    if (!e || e->type != NODE_NUMBER) return false;
    return mp_rat_compare_value(e->op.num, 1, 1) == 0;
}

/* ---------------- LOG matching ---------------- */

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

    /* t = 2 a x + b */
    mp_rat twoa = num_FromInt(2); mp_rat_mul(twoa, a, twoa);
    pcas_ast_t *t = ast_MakeBinary(OP_ADD,
                      ast_MakeBinary(OP_MULT, ast_MakeNumber(num_Copy(twoa)), ast_Copy(var)),
                      ast_MakeNumber(num_Copy(b)));

    pcas_ast_t *res = NULL;

    if (sgnDelta < 0) {
        /* Δ < 0 → 2/√(-Δ) * atan( t / √(-Δ) ) */
        mp_rat negDelta = num_FromInt(0); mp_rat_sub(num_FromInt(0), Delta, negDelta); /* -Δ */
        pcas_ast_t *sqrtND = ast_MakeBinary(OP_ROOT, N(2), ast_MakeNumber(num_Copy(negDelta)));
        pcas_ast_t *arg    = ast_MakeBinary(OP_DIV, t, ast_Copy(sqrtND));
        pcas_ast_t *atan   = ast_MakeUnary(OP_TAN_INV, arg); /* swap token if your enum uses OP_ATAN */
        mp_rat two = num_FromInt(2);
        pcas_ast_t *coef = ast_MakeBinary(OP_DIV, ast_MakeNumber(two), sqrtND); /* 2/√(-Δ) */
        res = ast_MakeBinary(OP_MULT, coef, atan);
        simp(res);
        num_Cleanup(negDelta);
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
        mp_rat h = num_FromInt(1);        /* start at 1 */
        mp_rat twoa2 = num_Copy(twoa);    /* twoa = 2a */
        mp_rat_div(h, twoa2, h);          /* h = 1/(2a) */
        mp_rat_mul(h, b, h);              /* h = b/(2a) */
        pcas_ast_t *shift = ast_MakeBinary(OP_ADD, ast_Copy(var), ast_MakeNumber(num_Copy(h)));
        pcas_ast_t *denom = ast_MakeBinary(OP_MULT, ast_MakeNumber(num_Copy(a)), shift);
        res = ast_MakeBinary(OP_DIV, N(-1), denom);
        simp(res);
        num_Cleanup(h); num_Cleanup(twoa2);
    }

    /* cleanup */
    num_Cleanup(a); num_Cleanup(b); num_Cleanup(c);
    num_Cleanup(b2); num_Cleanup(fourac); num_Cleanup(Delta); num_Cleanup(twoa);
    return res;
}


/* ∫ dx / ( x * sqrt(Q(x)) ) for the common case Q(x) = K - (x - h)^2 with h = 0, K > 0.
   Returns  - (1/sqrt(K)) * ln( (sqrt(K) + sqrt(Q(x)))/x )  or NULL if not matched. */
static pcas_ast_t *integrate_recip_x_times_quadratic_root(pcas_ast_t *den, pcas_ast_t *var) {
    pcas_ast_t *root_like = NULL;
    if (!split_x_times_root(den, var, &root_like)) return NULL;

    /* Pull Q(x) out of sqrt(Q(x)) */
    pcas_ast_t *poly = NULL;
    if (!extract_radicand(root_like, &poly) || !poly) return NULL;

    /* Complete the square: we need sgn < 0 and h == 0 (i.e., Q(x) = K - x^2) */
    int sgn = 0;
    mp_rat h = num_FromInt(0), K = num_FromInt(0);
    if (!complete_square_simple(poly, var, &sgn, &h, &K)) {
        num_Cleanup(h); num_Cleanup(K);
        return NULL;
    }

    bool ok = (sgn < 0) && (mp_rat_compare_zero(h) == 0) && (mp_rat_compare_zero(K) > 0);
    if (!ok) { num_Cleanup(h); num_Cleanup(K); return NULL; }

    /* Build:  -1/sqrt(K) * ln( (sqrt(K) + sqrt(Q(x)))/x ) */
    pcas_ast_t *sqrtK_1 = ast_MakeBinary(OP_ROOT, N(2), ast_MakeNumber(num_Copy(K)));
    pcas_ast_t *sqrtK_2 = ast_Copy(sqrtK_1);

    pcas_ast_t *sqrtQ   = ast_MakeBinary(OP_ROOT, N(2), ast_Copy(poly));
    pcas_ast_t *sum     = ast_MakeBinary(OP_ADD, sqrtK_1, sqrtQ);
    pcas_ast_t *frac    = ast_MakeBinary(OP_DIV, sum, ast_Copy(var));
    pcas_ast_t *ln      = ast_MakeUnary(OP_LOG, frac);

    pcas_ast_t *coef    = ast_MakeBinary(OP_DIV, N(-1), sqrtK_2);
    pcas_ast_t *res     = ast_MakeBinary(OP_MULT, coef, ln);
    simp(res);

    num_Cleanup(h);
    num_Cleanup(K);
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

    /* sec^2 / csc^2 via cos/sin powers */
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
    if (op == OP_ADD)  {
        return integrate_sum(expr, var);
    }

    /* Products: special trig products + targeted IBP and constant-factor extraction */
    if (op == OP_MULT) {
        return integrate_product(expr, var);
    }

    /* Powers: x^n rule, e^(a x) rule, sec^2/csc^2, etc. */
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

    /* Quadratic-under-root and related quotient patterns */
    if (op == OP_DIV) {
        pcas_ast_t *num = ast_ChildGet(expr,0), *den = ast_ChildGet(expr,1);

        /* Case A: 1 / sqrt(Q(x))  → arcsin/asinh (existing) */
        if (num && num->type==NODE_NUMBER && mp_rat_compare_value(num->op.num,1,1)==0) {
            pcas_ast_t *qrt = integrate_quadratic_root(den, var);
            if (qrt) return qrt;
        }

        /* Case B: c / ( x * sqrt(Q(x)) )  →  -(c/√K) ln( (√K + √Q)/x ) (new) */
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

        /* Case C: 1 / (a x^2 + b x + c)  → arctan / log depending on discriminant (new) */
        if (num && num->type==NODE_NUMBER && mp_rat_compare_value(num->op.num,1,1)==0) {
            pcas_ast_t *rq = integrate_recip_quadratic_poly(den, var);
            if (rq) return rq;
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
