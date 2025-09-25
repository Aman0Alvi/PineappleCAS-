// /* integral.c
//  * PineappleCAS — Antiderivative (indefinite integral) routines
//  * - ln/log support: unary OP_LOG(arg) = ln(arg); binary OP_LOG(base,arg) = log_base(arg)
//  * - Trig set via sin/cos/tan + quotient/power recognition (tan, sec, csc, cot; sec^2, csc^2; sec*tan, csc*cot)
//  * - Direct rule for ∫ sin x cos x dx = 1/2 sin^2 x and avoidance of IBP on pure trig×trig
//  * - Robust poly×(sin|cos) IBP with constants factored and bare x as degree 1
//  * - Linear-over-linear: ∫(a1 x + b1)/(a2 x + b2) dx
//  */

// #include "integral.h"
// #include "cas.h"
// #include "identities.h"

// #include <stdlib.h>
// #include <string.h>

// /* Provided elsewhere */
// void replace_node(pcas_ast_t *dst, pcas_ast_t *src);

// /* ---------------- IBP controls ---------------- */
// static bool s_ibp_enabled = true;
// void integral_set_ibp_enabled(bool on) { s_ibp_enabled = on; }

// static int s_ibp_depth = 0;
// static const int S_IBP_MAX_DEPTH = 8;

// /* ---------------- Helpers --------------------- */

// static inline pcas_ast_t *N(int v) { return ast_MakeNumber(num_FromInt(v)); }

// static void simp(pcas_ast_t *e) {
//     simplify(e, SIMP_NORMALIZE | SIMP_RATIONAL | SIMP_COMMUTATIVE |
//                 SIMP_EVAL | SIMP_LIKE_TERMS);
// }

// static bool depends_on_var(pcas_ast_t *e, pcas_ast_t *var) {
//     if (!e) return false;
//     if (e->type == NODE_SYMBOL) return ast_Compare(e, var);
//     if (e->type != NODE_OPERATOR) return false;
//     for (pcas_ast_t *ch = ast_ChildGet(e, 0); ch; ch = ch->next) {
//         if (depends_on_var(ch, var)) return true;
//     }
//     return false;
// }
// static inline bool is_const_wrt(pcas_ast_t *e, pcas_ast_t *var) {
//     return !depends_on_var(e, var);
// }

// static inline bool is_var_deg1(pcas_ast_t *e, pcas_ast_t *var) {
//     return e && e->type == NODE_SYMBOL && ast_Compare(e, var);
// }

// static bool is_one(pcas_ast_t *e) {
//     if (!e || e->type != NODE_NUMBER) return false;
//     return mp_rat_compare_value(e->op.num, 1, 1) == 0;
// }

// static bool is_op(pcas_ast_t *e, OperatorType k) {
//     return e && e->type == NODE_OPERATOR && optype(e) == k;
// }

// /* Exact sin(var) or cos(var)? return child if matches */
// static pcas_ast_t *is_sin_of_var(pcas_ast_t *e, pcas_ast_t *var) {
//     if (!is_op(e, OP_SIN)) return NULL;
//     pcas_ast_t *a = ast_ChildGet(e, 0);
//     return (a && a->type == NODE_SYMBOL && ast_Compare(a, var)) ? a : NULL;
// }
// static pcas_ast_t *is_cos_of_var(pcas_ast_t *e, pcas_ast_t *var) {
//     if (!is_op(e, OP_COS)) return NULL;
//     pcas_ast_t *a = ast_ChildGet(e, 0);
//     return (a && a->type == NODE_SYMBOL && ast_Compare(a, var)) ? a : NULL;
// }

// /* Detect tan(x) with arg==var (assuming OP_TAN exists) */
// static bool is_tan_of_var(pcas_ast_t *e, pcas_ast_t *var) {
//     if (!is_op(e, OP_TAN)) return false;
//     pcas_ast_t *a = ast_ChildGet(e, 0);
//     return a && a->type == NODE_SYMBOL && ast_Compare(a, var);
// }

// /* Recognize sec/csc/cot using only sin/cos/div/pow:
//    sec(x): 1/cos(x)  or  cos(x)^(-1)
//    csc(x): 1/sin(x)  or  sin(x)^(-1)
//    cot(x): cos(x)/sin(x)
// */
// static bool is_sec_of_var(pcas_ast_t *e, pcas_ast_t *var) {
//     if (!e) return false;
//     if (is_op(e, OP_DIV)) {
//         pcas_ast_t *num = ast_ChildGet(e, 0), *den = ast_ChildGet(e, 1);
//         if (is_one(num) && is_cos_of_var(den, var)) return true;
//     }
//     if (is_op(e, OP_POW)) {
//         pcas_ast_t *b = ast_ChildGet(e, 0), *p = ast_ChildGet(e, 1);
//         if (is_cos_of_var(b, var) && p && p->type == NODE_NUMBER &&
//             mp_rat_compare_value(p->op.num, -1, 1) == 0) return true;
//     }
//     return false;
// }
// static bool is_csc_of_var(pcas_ast_t *e, pcas_ast_t *var) {
//     if (!e) return false;
//     if (is_op(e, OP_DIV)) {
//         pcas_ast_t *num = ast_ChildGet(e, 0), *den = ast_ChildGet(e, 1);
//         if (is_one(num) && is_sin_of_var(den, var)) return true;
//     }
//     if (is_op(e, OP_POW)) {
//         pcas_ast_t *b = ast_ChildGet(e, 0), *p = ast_ChildGet(e, 1);
//         if (is_sin_of_var(b, var) && p && p->type == NODE_NUMBER &&
//             mp_rat_compare_value(p->op.num, -1, 1) == 0) return true;
//     }
//     return false;
// }
// static bool is_cot_of_var(pcas_ast_t *e, pcas_ast_t *var) {
//     if (!e || !is_op(e, OP_DIV)) return false;
//     pcas_ast_t *num = ast_ChildGet(e, 0), *den = ast_ChildGet(e, 1);
//     return is_cos_of_var(num, var) && is_sin_of_var(den, var);
// }

// /* sec^2 / csc^2 via cos/sin powers or reciprocals */
// static bool is_sec2_of_var(pcas_ast_t *e, pcas_ast_t *var) {
//     if (!e) return false;
//     if (is_op(e, OP_POW)) {
//         pcas_ast_t *b = ast_ChildGet(e, 0), *p = ast_ChildGet(e, 1);
//         if (is_cos_of_var(b, var) && p && p->type == NODE_NUMBER &&
//             mp_rat_compare_value(p->op.num, -2, 1) == 0) return true;
//     }
//     if (is_op(e, OP_DIV)) {
//         pcas_ast_t *num = ast_ChildGet(e, 0), *den = ast_ChildGet(e, 1);
//         if (is_one(num) && is_op(den, OP_POW)) {
//             pcas_ast_t *db = ast_ChildGet(den, 0), *dp = ast_ChildGet(den,1);
//             if (is_cos_of_var(db, var) && dp && dp->type==NODE_NUMBER &&
//                 mp_rat_compare_value(dp->op.num, 2, 1) == 0) return true;
//         }
//     }
//     return false;
// }
// static bool is_csc2_of_var(pcas_ast_t *e, pcas_ast_t *var) {
//     if (!e) return false;
//     if (is_op(e, OP_POW)) {
//         pcas_ast_t *b = ast_ChildGet(e, 0), *p = ast_ChildGet(e, 1);
//         if (is_sin_of_var(b, var) && p && p->type == NODE_NUMBER &&
//             mp_rat_compare_value(p->op.num, -2, 1) == 0) return true;
//     }
//     if (is_op(e, OP_DIV)) {
//         pcas_ast_t *num = ast_ChildGet(e, 0), *den = ast_ChildGet(e, 1);
//         if (is_one(num) && is_op(den, OP_POW)) {
//             pcas_ast_t *db = ast_ChildGet(den, 0), *dp = ast_ChildGet(den,1);
//             if (is_sin_of_var(db, var) && dp && dp->type==NODE_NUMBER &&
//                 mp_rat_compare_value(dp->op.num, 2, 1) == 0) return true;
//         }
//     }
//     return false;
// }

// /* Elementary trig antiderivatives (arg expected to be var) */
// static pcas_ast_t *int_sin_of(pcas_ast_t *arg) { /* ∫ sin(x) dx = -cos(x) */
//     return ast_MakeBinary(OP_MULT, N(-1), ast_MakeUnary(OP_COS, arg));
// }
// static pcas_ast_t *int_cos_of(pcas_ast_t *arg) { /* ∫ cos(x) dx =  sin(x) */
//     return ast_MakeUnary(OP_SIN, arg);
// }

// /* Return 1 if node is unary natural log ln(arg) with arg==var.
//    Return 2 if node is binary log_base(arg) with arg==var and set *base_out=base.
//    Return 0 otherwise.
//    NOTE: repo convention is child0=base, child1=arg for binary LOG; unary has child0=arg, child1=NULL. */
// static int match_log_of_var(pcas_ast_t *e, pcas_ast_t *var, pcas_ast_t **base_out) {
//     if (!e || e->type != NODE_OPERATOR || optype(e) != OP_LOG) return 0;

//     pcas_ast_t *c0 = ast_ChildGet(e, 0);
//     pcas_ast_t *c1 = ast_ChildGet(e, 1);

//     if (c1 == NULL) {
//         /* unary: LOG(arg) -> ln(arg) */
//         pcas_ast_t *arg = c0;
//         if (arg && arg->type == NODE_SYMBOL && ast_Compare(arg, var)) {
//             if (base_out) *base_out = NULL;
//             return 1;
//         }
//         return 0;
//     } else {
//         /* binary: LOG(base, arg) */
//         pcas_ast_t *base = c0;
//         pcas_ast_t *arg  = c1;
//         if (arg && arg->type == NODE_SYMBOL && ast_Compare(arg, var)) {
//             if (base_out) *base_out = base;
//             return 2;
//         }
//         return 0;
//     }
// }

// /* ∫ ln(x) dx = x ln(x) - x */
// static pcas_ast_t *int_ln_of_x(pcas_ast_t *var) {
//     pcas_ast_t *lnx  = ast_MakeUnary(OP_LOG, ast_Copy(var));        /* ln(x) */
//     pcas_ast_t *xlnx = ast_MakeBinary(OP_MULT, ast_Copy(var), lnx); /* x*ln(x) */
//     pcas_ast_t *res  = ast_MakeBinary(OP_ADD, xlnx,
//                          ast_MakeBinary(OP_MULT, N(-1), ast_Copy(var)));
//     simp(res);
//     return res;
// }

// /* Forward decl of the integrator core. */
// static pcas_ast_t *integrate_node(pcas_ast_t *expr, pcas_ast_t *var);

// /* ---------------- x^n integrator (supports fractional exponent in OP_DIV) ---- */
// static pcas_ast_t *integrate_x_power_any(pcas_ast_t *expr, pcas_ast_t *var) {
//     if (!expr || !isoptype(expr, OP_POW)) return NULL;
//     pcas_ast_t *base = ast_ChildGet(expr,0), *expo = ast_ChildGet(expr,1);
//     if (!base || !expo) return NULL;
//     if (!(base->type == NODE_SYMBOL && ast_Compare(base, var))) return NULL;

//     /* Make a NUMBER node 'n' for the exponent if possible */
//     pcas_ast_t *nnum = NULL;

//     if (expo->type == NODE_NUMBER) {
//         nnum = ast_MakeNumber(num_Copy(expo->op.num));
//     } else if (expo->type == NODE_OPERATOR && optype(expo) == OP_DIV) {
//         pcas_ast_t *n = ast_ChildGet(expo, 0);
//         pcas_ast_t *d = ast_ChildGet(expo, 1);
//         if (n && d && n->type == NODE_NUMBER && d->type == NODE_NUMBER) {
//             mp_rat r = num_FromInt(1);
//             /* r = n/d  (exact rational) */
//             mp_rat_div(n->op.num, d->op.num, r);
//             nnum = ast_MakeNumber(r);
//         }
//     } else {
//         return NULL;
//     }

//     if (!nnum) return NULL; /* not a supported exponent */

//     /* If n == -1, hand off to ln|x| */
//     if (mp_rat_compare_value(nnum->op.num, -1, 1) == 0) {
//         ast_Cleanup(nnum);
//         return NULL;
//     }

//     /* n+1 */
//     mp_rat np1 = num_Copy(nnum->op.num);
//     mp_rat_add(np1, num_FromInt(1), np1);

//     /* coef = 1/(n+1) */
//     mp_rat coef = num_FromInt(1);
//     mp_rat_div(coef, np1, coef);

//     pcas_ast_t *pow  = ast_MakeBinary(OP_POW, ast_Copy(var), ast_MakeNumber(num_Copy(np1)));
//     pcas_ast_t *res  = ast_MakeBinary(OP_MULT, ast_MakeNumber(coef), pow);

//     /* cleanup */
//     num_Cleanup(np1);
//     ast_Cleanup(nnum);

//     simp(res);
//     return res;
// }

// /* ---------------- IBP: poly(x) * (sin|cos)(x) ---------------- */
// static pcas_ast_t *ibp_poly_trig_once(pcas_ast_t *expr, pcas_ast_t *var) {
//     if (!expr || !is_op(expr, OP_MULT)) return NULL;

//     pcas_ast_t *poly = NULL, *poly_pow = NULL, *trig = NULL;
//     pcas_ast_t *const_factor = N(1);

//     for (pcas_ast_t *ch = ast_ChildGet(expr, 0); ch; ch = ch->next) {
//         bool picked = false;

//         if (!poly && is_op(ch, OP_POW)) {
//             pcas_ast_t *base = ast_ChildGet(ch, 0);
//             pcas_ast_t *expo = ast_ChildGet(ch, 1);
//             if (base && expo && base->type == NODE_SYMBOL &&
//                 ast_Compare(base, var) && expo->type == NODE_NUMBER) {
//                 poly = ch; poly_pow = expo; picked = true;
//             }
//         }
//         if (!picked && !poly && is_var_deg1(ch, var)) {
//             poly = ch; poly_pow = NULL; picked = true;
//         }

//         if (!picked && !trig && (is_op(ch, OP_SIN) || is_op(ch, OP_COS))) {
//             pcas_ast_t *arg = ast_ChildGet(ch, 0);
//             if (arg && arg->type == NODE_SYMBOL && ast_Compare(arg, var)) {
//                 trig = ch; picked = true;
//             }
//         }

//         if (!picked) {
//             if (!is_const_wrt(ch, var)) { ast_Cleanup(const_factor); return NULL; }
//             const_factor = ast_MakeBinary(OP_MULT, const_factor, ast_Copy(ch));
//         }
//     }

//     if (!poly || !trig) { ast_Cleanup(const_factor); return NULL; }

//     int n = 1;
//     if (poly_pow) {
//         char *nstr = num_ToString(poly_pow->op.num, 24);
//         n = (int)strtol(nstr, NULL, 10);
//         free(nstr);
//         if (n < 1) { ast_Cleanup(const_factor); return NULL; }
//     }

//     pcas_ast_t *u = ast_Copy(poly);
//     pcas_ast_t *v = is_op(trig, OP_SIN)
//                     ? int_sin_of(ast_Copy(ast_ChildGet(trig, 0)))
//                     : int_cos_of(ast_Copy(ast_ChildGet(trig, 0)));

//     pcas_ast_t *du = (n == 1) ? N(1)
//                               : ast_MakeBinary(OP_MULT, N(n),
//                                   ast_MakeBinary(OP_POW, ast_Copy(var), N(n-1)) );

//     pcas_ast_t *uv  = ast_MakeBinary(OP_MULT, ast_Copy(const_factor),
//                                      ast_MakeBinary(OP_MULT, u, ast_Copy(v)));
//     pcas_ast_t *vdu = ast_MakeBinary(OP_MULT, v, du);

//     if (s_ibp_depth >= S_IBP_MAX_DEPTH) {
//         simp(uv); ast_Cleanup(vdu); ast_Cleanup(const_factor); return uv;
//     }

//     s_ibp_depth++;
//     pcas_ast_t *rest = integrate_node(ast_MakeBinary(OP_MULT, ast_Copy(const_factor), vdu), var);
//     s_ibp_depth--;

//     ast_Cleanup(const_factor);

//     if (!rest) { ast_Cleanup(uv); return NULL; }

//     pcas_ast_t *res = ast_MakeBinary(OP_ADD, uv, ast_MakeBinary(OP_MULT, N(-1), rest));
//     simp(res);
//     return res;
// }

// /* ---------------- Special trig handling ---------------- */

// /* EXACT product sin(x)*cos(x) (same var) → 1/2 sin^2 x */
// static pcas_ast_t *integrate_sin_cos_simple(pcas_ast_t *expr, pcas_ast_t *var) {
//     if (!expr || !is_op(expr, OP_MULT)) return NULL;
//     pcas_ast_t *a = ast_ChildGet(expr, 0), *b = ast_ChildGet(expr, 1);
//     if (!a || !b || a->next) return NULL; /* only two factors */
//     if ((is_sin_of_var(a,var) && is_cos_of_var(b,var)) ||
//         (is_sin_of_var(b,var) && is_cos_of_var(a,var))) {
//         pcas_ast_t *s  = ast_MakeUnary(OP_SIN, ast_Copy(var));
//         pcas_ast_t *s2 = ast_MakeBinary(OP_POW, s, N(2));
//         pcas_ast_t *res = ast_MakeBinary(OP_DIV, s2, N(2)); /* 1/2 * sin^2(x) */
//         simp(res);
//         return res;
//     }
//     return NULL;
// }

// /* sec*tan and csc*cot in quotient form */
// static bool is_sec_times_tan(pcas_ast_t *e, pcas_ast_t *var) {
//     if (!e || !is_op(e, OP_MULT)) return false;
//     if (ast_ChildLength(e) != 2) return false;
//     pcas_ast_t *a = ast_ChildGet(e,0), *b = ast_ChildGet(e,1);
//     return (is_sec_of_var(a,var) && is_tan_of_var(b,var)) ||
//            (is_sec_of_var(b,var) && is_tan_of_var(a,var));
// }
// static bool is_csc_times_cot(pcas_ast_t *e, pcas_ast_t *var) {
//     if (!e || !is_op(e, OP_MULT)) return false;
//     if (ast_ChildLength(e) != 2) return false;
//     pcas_ast_t *a = ast_ChildGet(e,0), *b = ast_ChildGet(e,1);
//     return (is_csc_of_var(a,var) && is_cot_of_var(b,var)) ||
//            (is_csc_of_var(b,var) && is_cot_of_var(a,var));
// }
// static pcas_ast_t *integrate_special_trig_product(pcas_ast_t *expr, pcas_ast_t *var) {
//     if (!expr || !is_op(expr, OP_MULT)) return NULL;

//     /* sin·cos first to avoid recursion crashes */
//     pcas_ast_t *sc = integrate_sin_cos_simple(expr, var);
//     if (sc) return sc;

//     if (is_sec_times_tan(expr, var)) {
//         pcas_ast_t *res = ast_MakeBinary(OP_DIV, N(1), ast_MakeUnary(OP_COS, ast_Copy(var))); /* sec */
//         simp(res);
//         return res;
//     }
//     if (is_csc_times_cot(expr, var)) {
//         pcas_ast_t *csc = ast_MakeBinary(OP_DIV, N(1), ast_MakeUnary(OP_SIN, ast_Copy(var)));
//         pcas_ast_t *res = ast_MakeBinary(OP_MULT, N(-1), csc); /* -csc */
//         simp(res);
//         return res;
//     }
//     return NULL;
// }

// /* -------------- Linear-over-linear helpers ----------------------------- */

// /* Collect coefficients so e == a*var + b.
//    Returns true with a_out,b_out filled (heap mp_rat). */
// static bool lin_coeffs(pcas_ast_t *e, pcas_ast_t *var, mp_rat *a_out, mp_rat *b_out) {
//     if (!e || !a_out || !b_out) return false;

//     mp_rat a = num_FromInt(0);
//     mp_rat b = num_FromInt(0);
//     bool ok = true;

//     switch (e->type) {
//     case NODE_SYMBOL:
//         if (ast_Compare(e, var)) {
//             mp_rat_add(a, num_FromInt(1), a);
//         } else {
//             ok = false;
//         }
//         break;

//     case NODE_NUMBER:
//         mp_rat_add(b, e->op.num, b);
//         break;

//     case NODE_OPERATOR: {
//         OperatorType k = optype(e);
//         if (k == OP_ADD) {
//             for (pcas_ast_t *ch = ast_ChildGet(e,0); ch; ch = ch->next) {
//                 mp_rat ta = num_FromInt(0), tb = num_FromInt(0);
//                 if (!lin_coeffs(ch, var, &ta, &tb)) { ok = false; num_Cleanup(ta); num_Cleanup(tb); break; }
//                 mp_rat_add(a, ta, a);
//                 mp_rat_add(b, tb, b);
//                 num_Cleanup(ta); num_Cleanup(tb);
//             }
//         } else if (k == OP_MULT) {
//             /* allow ANY number of numeric factors times exactly ONE 'var' */
//             mp_rat coef = num_FromInt(1);
//             int var_count = 0;
//             for (pcas_ast_t *ch = ast_ChildGet(e,0); ch; ch = ch->next) {
//                 if (ch->type == NODE_NUMBER) {
//                     mp_rat_mul(coef, ch->op.num, coef);
//                 } else if (ch->type == NODE_SYMBOL && ast_Compare(ch, var)) {
//                     var_count++;
//                 } else {
//                     ok = false; break;
//                 }
//             }
//             if (ok && var_count == 1) {
//                 mp_rat_add(a, coef, a);
//             } else ok = false;
//             num_Cleanup(coef);
//         } else {
//             ok = false;
//         }
//         break;
//     }

//     default: ok = false; break;
//     }

//     if (!ok) { num_Cleanup(a); num_Cleanup(b); return false; }
//     *a_out = a; *b_out = b;
//     return true;
// }

// /* helper: is node exactly (linear)^(-1)? If yes, set *base_out to that linear base. */
// static bool is_pow_minus1_of_linear(pcas_ast_t *node, pcas_ast_t **base_out, pcas_ast_t *var) {
//     if (!node || !isoptype(node, OP_POW)) return false;
//     pcas_ast_t *base = ast_ChildGet(node,0);
//     pcas_ast_t *expo = ast_ChildGet(node,1);
//     if (!base || !expo) return false;
//     if (!(expo->type == NODE_NUMBER && mp_rat_compare_value(expo->op.num, -1, 1) == 0)) return false;
//     mp_rat A = NULL, B = NULL;
//     bool ok = lin_coeffs(base, var, &A, &B);
//     if (A) num_Cleanup(A);
//     if (B) num_Cleanup(B);
//     if (!ok) return false;
//     if (base_out) *base_out = base;
//     return true;
// }

// /* ∫ (a1 x + b1)/(a2 x + b2) dx = (a1/a2) x + ((b1 - (a1/a2) b2)/a2) ln|a2 x + b2| */
// static pcas_ast_t *integrate_linear_over_linear(pcas_ast_t *expr, pcas_ast_t *var) {
//     if (!expr || !isoptype(expr, OP_DIV)) return NULL;
//     pcas_ast_t *num = ast_ChildGet(expr,0), *den = ast_ChildGet(expr,1);
//     if (!num || !den) return NULL;

//     mp_rat a1, b1, a2, b2;
//     if (!lin_coeffs(num, var, &a1, &b1)) return NULL;
//     if (!lin_coeffs(den, var, &a2, &b2)) { num_Cleanup(a1); num_Cleanup(b1); return NULL; }

//     /* a2 must be nonzero */
//     if (mp_rat_compare_zero(a2) == 0) {
//         num_Cleanup(a1); num_Cleanup(b1); num_Cleanup(a2); num_Cleanup(b2);
//         return NULL;
//     }

//     /* A = a1/a2 */
//     mp_rat A = num_FromInt(1); mp_rat_div(a1, a2, A);

//     /* B = b1 - A*b2 */
//     mp_rat Ab2 = num_Copy(A); mp_rat_mul(Ab2, b2, Ab2);
//     mp_rat B   = num_Copy(b1); mp_rat_sub(B, Ab2, B);

//     /* C = B/a2 (coefficient of ln term) */
//     mp_rat C = num_FromInt(1); mp_rat_div(B, a2, C);

//     /* Build Ax + C*ln(den) */
//     pcas_ast_t *Ax   = ast_MakeBinary(OP_MULT, ast_MakeNumber(num_Copy(A)), ast_Copy(var));
//     pcas_ast_t *ln_d = ast_MakeUnary(OP_LOG, ast_Copy(den));
//     pcas_ast_t *Cln  = ast_MakeBinary(OP_MULT, ast_MakeNumber(num_Copy(C)), ln_d);
//     pcas_ast_t *res  = ast_MakeBinary(OP_ADD, Ax, Cln);

//     /* cleanup temps */
//     num_Cleanup(a1); num_Cleanup(b1); num_Cleanup(a2); num_Cleanup(b2);
//     num_Cleanup(A);  num_Cleanup(Ab2); num_Cleanup(B); num_Cleanup(C);

//     simp(res);
//     return res;
// }

// /* If expr is MULT and equals  (L1)*(L2)^(-1) with L1, L2 linear in var, route to LoL */
// static pcas_ast_t *try_lol_from_product(pcas_ast_t *expr, pcas_ast_t *var) {
//     if (!expr || !isoptype(expr, OP_MULT)) return NULL;
//     if (ast_ChildLength(expr) != 2) return NULL;

//     pcas_ast_t *a = ast_ChildGet(expr,0), *b = ast_ChildGet(expr,1);

//     /* case1: (ax+b) * (cx+d)^(-1) */
//     {
//         mp_rat Aa=NULL,Ba=NULL;
//         if (lin_coeffs(a, var, &Aa, &Ba)) {
//             pcas_ast_t *den_base = NULL;
//             if (is_pow_minus1_of_linear(b, &den_base, var)) {
//                 pcas_ast_t *div = ast_MakeBinary(OP_DIV, ast_Copy(a), ast_Copy(den_base));
//                 pcas_ast_t *res = integrate_linear_over_linear(div, var);
//                 ast_Cleanup(div);
//                 num_Cleanup(Aa); num_Cleanup(Ba);
//                 return res;
//             }
//         }
//         if (Aa) num_Cleanup(Aa);
//         if (Ba) num_Cleanup(Ba);
//     }

//     /* case2: (ax+b)^(-1) * (cx+d) */
//     {
//         pcas_ast_t *den_base = NULL;
//         if (is_pow_minus1_of_linear(a, &den_base, var)) {
//             mp_rat Ab=NULL,Bb=NULL;
//             if (lin_coeffs(b, var, &Ab, &Bb)) {
//                 pcas_ast_t *div = ast_MakeBinary(OP_DIV, ast_Copy(b), ast_Copy(den_base));
//                 pcas_ast_t *res = integrate_linear_over_linear(div, var);
//                 ast_Cleanup(div);
//                 num_Cleanup(Ab); num_Cleanup(Bb);
//                 return res;
//             }
//             if (Ab) num_Cleanup(Ab);
//             if (Bb) num_Cleanup(Bb);
//         }
//     }
//     return NULL;
// }

// /* ---------------- Pieces for common node types --------------------------- */

// static pcas_ast_t *integrate_sum(pcas_ast_t *expr, pcas_ast_t *var) {
//     pcas_ast_t *sum = ast_MakeOperator(OP_ADD);
//     for (pcas_ast_t *ch = ast_ChildGet(expr, 0); ch; ch = ch->next) {
//         pcas_ast_t *i = integrate_node(ast_Copy(ch), var);
//         if (!i) { ast_Cleanup(sum); return NULL; }
//         ast_ChildAppend(sum, i);
//     }
//     simp(sum);
//     return sum;
// }

// static bool expo_linear_coeff(pcas_ast_t *expo, pcas_ast_t *var, pcas_ast_t **a_out) {
//     if (!expo || !var || !a_out) return false;

//     /* direct: expo == var */
//     if (expo->type == NODE_SYMBOL && ast_Compare(expo, var)) {
//         *a_out = ast_MakeNumber(num_FromInt(1));
//         return true;
//     }

//     /* product case: (num ...)*var (order-insensitive), ONLY numbers and var allowed */
//     if (expo->type == NODE_OPERATOR && optype(expo) == OP_MULT) {
//         mp_rat acc = num_FromInt(1);
//         bool saw_var = false;

//         for (pcas_ast_t *ch = ast_ChildGet(expo, 0); ch; ch = ch->next) {
//             if (ch->type == NODE_SYMBOL && ast_Compare(ch, var)) {
//                 if (saw_var) { num_Cleanup(acc); return false; }  /* var must appear once */
//                 saw_var = true;
//             } else if (ch->type == NODE_NUMBER) {
//                 mp_rat_mul(acc, ch->op.num, acc);
//             } else {
//                 /* some other non-numeric/non-var node => not linear */
//                 num_Cleanup(acc);
//                 return false;
//             }
//         }

//         if (saw_var) {
//             *a_out = ast_MakeNumber(num_Copy(acc));
//             num_Cleanup(acc);
//             return true;
//         }
//         num_Cleanup(acc);
//         return false;
//     }

//     /* sum (affine) case: a*var + b, where b is numeric-only (or absent) */
//     if (expo->type == NODE_OPERATOR && optype(expo) == OP_ADD) {
//         pcas_ast_t *term_with_var = NULL;

//         /* Find exactly one addend containing var (as var or product of numbers*var) */
//         for (pcas_ast_t *t = ast_ChildGet(expo, 0); t; t = t->next) {
//             bool dep = depends_on_var(t, var);
//             if (dep) {
//                 if (term_with_var) return false; /* more than one linear term => not strictly linear */
//                 term_with_var = t;
//             } else {
//                 /* require other addends to be numeric-only (constants) */
//                 if (!is_const_wrt(t, var)) return false;
//             }
//         }
//         if (!term_with_var) return false;

//         /* Recurse: extract coefficient from the term-with-var (must be var or numbers*var) */
//         return expo_linear_coeff(term_with_var, var, a_out);
//     }

//     return false;
// }

// static pcas_ast_t *integrate_power(pcas_ast_t *expr, pcas_ast_t *var) {
//     pcas_ast_t *base = ast_ChildGet(expr, 0);
//     pcas_ast_t *expo = ast_ChildGet(expr, 1);
//     if (!base || !expo) return NULL;

//     /* e^(a*x [+ b]) : ∫ e^(a x) dx = (1/a) e^(a x) */
//     if (base->type == NODE_SYMBOL && base->op.symbol == SYM_EULER) {
//         pcas_ast_t *a_num = NULL;
//         if (expo_linear_coeff(expo, var, &a_num)) {
//             /* Build coefficient c = 1 / a_num */
//             mp_rat c = num_FromInt(1);
//             mp_rat_div(c, a_num->op.num, c);

//             pcas_ast_t *coef = ast_MakeNumber(c);
//             pcas_ast_t *pow  = ast_MakeBinary(OP_POW, ast_Copy(base), ast_Copy(expo));
//             pcas_ast_t *res  = ast_MakeBinary(OP_MULT, coef, pow);

//             ast_Cleanup(a_num);
//             simp(res);
//             return res;
//         }
//     }

//     /* x^n (including fractional n != -1) */
//     {
//         pcas_ast_t *r = integrate_x_power_any(expr, var);
//         if (r) return r;
//     }

//     /* sec^2 and csc^2 via pattern */
//     if (is_sec2_of_var(expr, var)) {
//         pcas_ast_t *res = ast_MakeUnary(OP_TAN, ast_Copy(var));
//         simp(res);
//         return res;
//     }
//     if (is_csc2_of_var(expr, var)) {
//         pcas_ast_t *cot = ast_MakeBinary(OP_DIV, ast_MakeUnary(OP_COS, ast_Copy(var)),
//                                          ast_MakeUnary(OP_SIN, ast_Copy(var)));
//         pcas_ast_t *res = ast_MakeBinary(OP_MULT, N(-1), cot);
//         simp(res);
//         return res;
//     }

//     return NULL;
// }

// static pcas_ast_t *integrate_product(pcas_ast_t *expr, pcas_ast_t *var) {
//     /* Try linear-over-linear disguised as product: (ax+b)*(cx+d)^(-1) */
//     {
//         pcas_ast_t *lol = try_lol_from_product(expr, var);
//         if (lol) return lol;
//     }

//     /* Short-circuit common trig×trig to avoid recursion crashes */
//     {
//         pcas_ast_t *sp = integrate_special_trig_product(expr, var);
//         if (sp) return sp;
//     }

//     /* Targeted poly×(sin|cos) IBP */
//     if (s_ibp_enabled) {
//         pcas_ast_t *t = ibp_poly_trig_once(expr, var);
//         if (t) return t;
//     }

//     /* If remaining non-constant factors are all trig and >1, skip (avoid loops) */
//     int nonconst_count = 0, trig_like_count = 0;
//     for (pcas_ast_t *ch = ast_ChildGet(expr,0); ch; ch=ch->next) {
//         if (!is_const_wrt(ch, var)) {
//             nonconst_count++;
//             if (is_op(ch, OP_SIN) || is_op(ch, OP_COS) || is_tan_of_var(ch,var) ||
//                 is_sec_of_var(ch,var) || is_csc_of_var(ch,var) || is_cot_of_var(ch,var)) {
//                 trig_like_count++;
//             }
//         }
//     }
//     if (nonconst_count >= 2 && trig_like_count == nonconst_count) {
//         return NULL; /* let higher-level trig identities handle */
//     }

//     /* Constant factor extraction (c * f(x) -> c * ∫ f(x) dx) */
//     pcas_ast_t *const_factor = N(1);
//     pcas_ast_t *rest_factor  = N(1);
//     for (pcas_ast_t *ch = ast_ChildGet(expr, 0); ch; ch = ch->next) {
//         if (is_const_wrt(ch, var)) {
//             const_factor = ast_MakeBinary(OP_MULT, const_factor, ast_Copy(ch));
//         } else {
//             rest_factor  = ast_MakeBinary(OP_MULT, rest_factor,  ast_Copy(ch));
//         }
//     }
//     simp(const_factor); simp(rest_factor);

//     if (is_one(rest_factor)) {
//         pcas_ast_t *res = ast_MakeBinary(OP_MULT, const_factor, ast_Copy(var));
//         simp(res);
//         ast_Cleanup(rest_factor);
//         return res;
//     }

//     pcas_ast_t *inner = integrate_node(rest_factor, var);
//     if (inner) {
//         pcas_ast_t *res = ast_MakeBinary(OP_MULT, const_factor, inner);
//         simp(res);
//         return res;
//     }

//     ast_Cleanup(const_factor);
//     return NULL;
// }

// /* ---------------- Main integrator ---------------- */
// static pcas_ast_t *integrate_node(pcas_ast_t *expr, pcas_ast_t *var) {
//     if (!expr) return NULL;

//     /* Numbers: ∫ c dx = c*x */
//     if (expr->type == NODE_NUMBER) {
//         pcas_ast_t *res = ast_MakeBinary(OP_MULT, ast_Copy(expr), ast_Copy(var));
//         simp(res);
//         return res;
//     }

//     /* Symbols */
//     if (expr->type == NODE_SYMBOL) {
//         if (ast_Compare(expr, var)) {
//             /* ∫ x dx = x^2/2 */
//             pcas_ast_t *res = ast_MakeBinary(OP_DIV,
//                 ast_MakeBinary(OP_POW, ast_Copy(var), N(2)), N(2));
//             simp(res);
//             return res;
//         } else {
//             /* ∫ c dx = c*x */
//             pcas_ast_t *res = ast_MakeBinary(OP_MULT, ast_Copy(expr), ast_Copy(var));
//             simp(res);
//             return res;
//         }
//     }

//     if (expr->type != NODE_OPERATOR) return NULL;

//     OperatorType op = optype(expr);

//     /* Sums: integrate termwise */
//     if (op == OP_ADD)  {
//         return integrate_sum(expr, var);
//     }

//     /* Linear-over-linear when it really is a DIV node */
//     if (op == OP_DIV) {
//         pcas_ast_t *r = integrate_linear_over_linear(expr, var);
//         if (r) return r;
//         /* else fall through */
//     }

//     /* Products: special trig products + targeted IBP and constant-factor extraction */
//     if (op == OP_MULT) {
//         return integrate_product(expr, var);
//     }

//     /* Powers: x^n rule, e^(a x) rule, sec^2/csc^2, etc. */
//     if (op == OP_POW)  {
//         pcas_ast_t *r = integrate_power(expr, var);
//         if (r) return r;
//     }

//     /* Trig singletons with arg == var */
//     if (op == OP_SIN || op == OP_COS || op == OP_TAN) {
//         pcas_ast_t *arg = ast_ChildGet(expr, 0);
//         if (arg && arg->type == NODE_SYMBOL && ast_Compare(arg, var)) {
//             pcas_ast_t *res = NULL;
//             switch (op) {
//                 case OP_SIN: /* ∫ sin x dx = -cos x */
//                     res = ast_MakeBinary(OP_MULT, N(-1), ast_MakeUnary(OP_COS, ast_Copy(arg)));
//                     break;
//                 case OP_COS: /* ∫ cos x dx =  sin x */
//                     res = ast_MakeUnary(OP_SIN, ast_Copy(arg));
//                     break;
//                 case OP_TAN: /* ∫ tan x dx = -ln|cos x| -> represent as -ln(cos x) */
//                     res = ast_MakeBinary(OP_MULT, N(-1),
//                             ast_MakeUnary(OP_LOG, ast_MakeUnary(OP_COS, ast_Copy(arg))));
//                     break;
//                 default: break;
//             }
//             if (res) { simp(res); return res; }
//         }
//     }

//     /* Natural log / base log when argument is the integration variable */
//     {
//         pcas_ast_t *base = NULL;
//         int kind = match_log_of_var(expr, var, &base); /* 1 = ln(x); 2 = log_base(x) with base_out */
//         if (kind == 1) {
//             /* ∫ ln x dx = x ln x - x */
//             return int_ln_of_x(var);
//         } else if (kind == 2) {
//             /* base e => ln(x) */
//             if (base && base->type == NODE_SYMBOL && base->op.symbol == SYM_EULER) {
//                 return int_ln_of_x(var);
//             }
//             /* general base: (x ln x - x) / ln(a) */
//             pcas_ast_t *numer = int_ln_of_x(var);
//             pcas_ast_t *den   = ast_MakeUnary(OP_LOG, ast_Copy(base)); /* ln(a) */
//             pcas_ast_t *res   = ast_MakeBinary(OP_DIV, numer, den);
//             simp(res);
//             return res;
//         }
//     }

//     /* sec, csc, cot singletons recognized via sin/cos/quotient patterns */
//     if (is_sec_of_var(expr, var)) {
//         /* ∫ sec x dx = ln|sec x + tan x|  -> ln(sec x + tan x) */
//         pcas_ast_t *sec = ast_MakeBinary(OP_DIV, N(1), ast_MakeUnary(OP_COS, ast_Copy(var)));
//         pcas_ast_t *tan = ast_MakeUnary(OP_TAN, ast_Copy(var));
//         pcas_ast_t *sum = ast_MakeBinary(OP_ADD, sec, tan);
//         pcas_ast_t *res = ast_MakeUnary(OP_LOG, sum);
//         simp(res);
//         return res;
//     }
//     if (is_csc_of_var(expr, var)) {
//         /* ∫ csc x dx = ln|csc x - cot x| -> ln(1/sin - cos/sin) */
//         pcas_ast_t *csc = ast_MakeBinary(OP_DIV, N(1), ast_MakeUnary(OP_SIN, ast_Copy(var)));
//         pcas_ast_t *cot = ast_MakeBinary(OP_DIV, ast_MakeUnary(OP_COS, ast_Copy(var)),
//                                          ast_MakeUnary(OP_SIN, ast_Copy(var)));
//         pcas_ast_t *diff = ast_MakeBinary(OP_ADD, csc, ast_MakeBinary(OP_MULT, N(-1), cot));
//         pcas_ast_t *res  = ast_MakeUnary(OP_LOG, diff);
//         simp(res);
//         return res;
//     }
//     if (is_cot_of_var(expr, var)) {
//         /* ∫ cot x dx = ln|sin x| -> ln(sin x) */
//         pcas_ast_t *res = ast_MakeUnary(OP_LOG, ast_MakeUnary(OP_SIN, ast_Copy(var)));
//         simp(res);
//         return res;
//     }

//     /* Not handled */
//     return NULL;
// }

// /* Public entry */
// void antiderivative(pcas_ast_t *e, pcas_ast_t *respect_to) {
//     if (!e || !respect_to) return;
//     pcas_ast_t *copy = ast_Copy(e);
//     pcas_ast_t *res  = integrate_node(copy, respect_to);
//     if (!res) { ast_Cleanup(copy); return; }
//     replace_node(e, res);
// }

/* integral.c
 * PineappleCAS — Antiderivative (indefinite integral) routines
 * - ln/log support: unary OP_LOG(arg) = ln(arg); binary OP_LOG(base,arg) = log_base(arg)
 * - Trig set via sin/cos/tan + quotient/power recognition (tan, sec, csc, cot; sec^2, csc^2; sec*tan, csc*cot)
 * - Direct rule for ∫ sin x cos x dx = 1/2 sin^2 x and avoidance of IBP on pure trig×trig
 * - Robust poly×(sin|cos) IBP with constants factored and bare x as degree 1
 * - Power rule for fractional exponents (e.g., 1/sqrt(x))
 * - Quadratic-under-root handler with completing the square for common forms (e.g., ∫ dx / sqrt(3+2x-x^2))
 */

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

    /* Quadratic-under-root: ∫ dx / sqrt( ax^2+bx+c )  (common cases) */
    if (op == OP_DIV) {
        pcas_ast_t *num = ast_ChildGet(expr,0), *den = ast_ChildGet(expr,1);
        if (num && num->type==NODE_NUMBER && mp_rat_compare_value(num->op.num,1,1)==0) {
            pcas_ast_t *qrt = integrate_quadratic_root(den, var);
            if (qrt) return qrt;
        }
    }
    if (op == OP_POW || op == OP_ROOT) {
        /* Direct ∫ 1 / sqrt(Q(x)) dx form as POW(Q, -1/2) etc. */
        if (is_op(expr, OP_POW)) {
            pcas_ast_t *B = ast_ChildGet(expr,0), *E = ast_ChildGet(expr,1);
            if (E && E->type==NODE_NUMBER && mp_rat_compare_value(E->op.num, -1, 2)==0) {
                pcas_ast_t *qrt = integrate_quadratic_root(ast_MakeBinary(OP_ROOT, N(2), ast_Copy(B)), var);
                if (qrt) return qrt;
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
