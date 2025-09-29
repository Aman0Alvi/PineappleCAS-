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
        if (!plus && (j & 1)) { mp_rat_neg(C, C); } /* (−1)^j */
        int p = base_pow + 2*j;                     /* u^{base_pow} * u^{2j} */
        mp_rat inv = num_FromInt(p+1); mp_rat_recip(inv, inv); /* 1/(p+1) */
        mp_rat coeff = num_FromInt(0); mp_rat_mul(C, inv, coeff);

        pcas_ast_t *u = u_of_x(var);
        pcas_ast_t *u_pow = (p==0) ? N(1) : ast_MakeBinary(OP_POW, u, N(p+1)); /* antiderivative power p+1 */

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
