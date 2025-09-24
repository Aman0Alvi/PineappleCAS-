/*
 * integral.c
 *
 * A conservative antiderivative (indefinite integral) routine for PineappleCAS.
 * It walks the AST and applies a small set of safe rules (sum, constant
 * multiple, power rule, sin/cos, a^x). Expressions it cannot handle are
 * returned unchanged so you can layer advanced techniques later (IBP, trig
 * substitution, partial fractions, …).
 */

#include "integral.h"
#include "cas.h"     /* for replace_node, simplify, eval_derivative_nodes */
#include "identities.h"

/* -------- IBP runtime toggle (default ON) -------- */
static bool s_ibp_enabled = true;
void integral_set_ibp_enabled(bool on) { s_ibp_enabled = on; }

/* -------- IBP recursion guard --------
   Depth 4 lets us do x^2 sin(x) (two IBP steps) and similar without hanging. */
static int  s_ibp_depth      = 0;
static const int s_ibp_max_depth = 4;

/* replace_node() is defined in simplify.c but not declared in a header. */
void replace_node(pcas_ast_t *a, pcas_ast_t *b);

/* true if `expr` does not depend on `var` */
static bool is_constant_internal(pcas_ast_t *expr, pcas_ast_t *var) {
    pcas_ast_t *child;
    if (ast_Compare(expr, var)) return false;
    if (expr->type == NODE_OPERATOR) {
        for (child = ast_ChildGet(expr, 0); child != NULL; child = child->next) {
            if (!is_constant_internal(child, var)) return false;
        }
    }
    return true;
}

/* helper: does expression simplify to the exact number -1 ? */
static bool simplifies_to_minus_one(pcas_ast_t *e) {
    pcas_ast_t *tmp;
    bool res = false;
    if (!e) return false;
    if (e->type == NODE_NUMBER) {
        return mp_rat_compare_value(e->op.num, -1, 1) == 0;
    }
    tmp = ast_Copy(e);
    simplify(tmp, SIMP_EVAL | SIMP_RATIONAL | SIMP_NORMALIZE | SIMP_COMMUTATIVE);
    if (tmp->type == NODE_NUMBER && mp_rat_compare_value(tmp->op.num, -1, 1) == 0) {
        res = true;
    }
    ast_Cleanup(tmp);
    return res;
}

/* Heuristic: rank a node for being 'u' in IBP using LIATE priority.
   Lower score = better 'u'. Non-constants only. */
static int ibp_rank_u(pcas_ast_t *e) {
    if (!e) return 1000;
    if (e->type == NODE_NUMBER) return 999;

    if (e->type == NODE_SYMBOL) return 30;
    if (e->type == NODE_OPERATOR && optype(e) == OP_POW) {
        pcas_ast_t *b = ast_ChildGet(e, 0);
        pcas_ast_t *p = ast_ChildGet(e, 1);
        if (b && b->type == NODE_SYMBOL && p && p->type == NODE_NUMBER) return 32;
    }

    if (e->type == NODE_OPERATOR && optype(e) == OP_LOG) {
        pcas_ast_t *base = ast_ChildGet(e, 0);
        if (base && base->type == NODE_SYMBOL && base->op.symbol == SYM_EULER) return 10; /* L */
        return 12;
    }

    if (e->type == NODE_OPERATOR &&
        (optype(e) == OP_SIN_INV || optype(e) == OP_COS_INV || optype(e) == OP_TAN_INV))
        return 20; /* I */

    if (e->type == NODE_OPERATOR &&
        (optype(e) == OP_ADD || optype(e) == OP_MULT || optype(e) == OP_DIV || optype(e) == OP_POW))
        return 40; /* A */

    if (e->type == NODE_OPERATOR &&
        (optype(e) == OP_SIN || optype(e) == OP_COS || optype(e) == OP_TAN))
        return 60; /* T */

    if (e->type == NODE_OPERATOR && optype(e) == OP_POW)
        return 80; /* E (e^x is OP_POW with base e) */

    return 50;
}

/* Split a product into two factors A*B (flattened). */
static bool ibp_split_product_2(pcas_ast_t *prod, pcas_ast_t **a, pcas_ast_t **b) {
    if (!prod || prod->type != NODE_OPERATOR || optype(prod) != OP_MULT) return false;
    unsigned n = ast_ChildLength(prod);
    if (n < 2) return false;

    pcas_ast_t *left = ast_Copy(ast_ChildGet(prod, 0));
    pcas_ast_t *right = NULL;
    for (unsigned i = 1; i < n; ++i) {
        if (!right) right = ast_Copy(ast_ChildGet(prod, i));
        else right = ast_MakeBinary(OP_MULT, right, ast_Copy(ast_ChildGet(prod, i)));
    }
    *a = left;
    *b = right ? right : ast_MakeNumber(num_FromInt(1));
    return true;
}

/* d(expr)/d(var) */
static pcas_ast_t *ibp_diff(pcas_ast_t *expr, pcas_ast_t *var) {
    pcas_ast_t *d = ast_MakeUnary(OP_DERIV, ast_Copy(expr));
    ast_ChildAppend(d, ast_Copy(var));
    eval_derivative_nodes(d);
    simplify(d, SIMP_NORMALIZE | SIMP_RATIONAL | SIMP_COMMUTATIVE | SIMP_EVAL | SIMP_LIKE_TERMS);
    return d;
}

/* Try our main integrator; return NULL if unsupported */
static pcas_ast_t *ibp_anti_try(pcas_ast_t *e, pcas_ast_t *var);

/* One-step generic IBP */
static pcas_ast_t *ibp_try_once(pcas_ast_t *prod, pcas_ast_t *var) {
    pcas_ast_t *A = NULL, *B = NULL;
    if (!ibp_split_product_2(prod, &A, &B)) return NULL;

    int rA = ibp_rank_u(A);
    int rB = ibp_rank_u(B);
    pcas_ast_t *u  = (rA <= rB) ? A : B;
    pcas_ast_t *dv = (rA <= rB) ? B : A;

    pcas_ast_t *du = ibp_diff(u, var);
    pcas_ast_t *v  = ibp_anti_try(dv, var);

    if (!v) { /* try swapping */
        ast_Cleanup(du);
        du = ibp_diff(dv, var);
        v  = ibp_anti_try(u, var);
        if (!v) { ast_Cleanup(du); ast_Cleanup(A); ast_Cleanup(B); return NULL; }
        pcas_ast_t *tmp = u; u = dv; dv = tmp;
    }

    pcas_ast_t *uv   = ast_MakeBinary(OP_MULT, ast_Copy(u), ast_Copy(v));
    pcas_ast_t *vdu  = ast_MakeBinary(OP_MULT, ast_Copy(v), du);

    /* CRITICAL: simplify before recursing so the next IBP triggers cleanly */
    simplify(vdu, SIMP_NORMALIZE | SIMP_COMMUTATIVE | SIMP_RATIONAL | SIMP_EVAL | SIMP_LIKE_TERMS);

    pcas_ast_t *res = NULL;
    if (s_ibp_depth < s_ibp_max_depth) {
        s_ibp_depth++;
        pcas_ast_t *rest = ibp_anti_try(vdu, var);
        s_ibp_depth--;
        if (rest) {
            res = ast_MakeBinary(OP_ADD, uv,
                    ast_MakeBinary(OP_MULT, ast_MakeNumber(num_FromInt(-1)), rest));
            simplify(res, SIMP_NORMALIZE | SIMP_RATIONAL | SIMP_COMMUTATIVE | SIMP_EVAL | SIMP_LIKE_TERMS);
        } else {
            ast_Cleanup(uv);
        }
    }
    ast_Cleanup(A);
    ast_Cleanup(B);
    if (v) ast_Cleanup(v);
    return res;
}

/* Forward decl */
static pcas_ast_t *integrate_node(pcas_ast_t *expr, pcas_ast_t *var);

/* Anti-try helper: just call; non-NULL means “we did something” */
static pcas_ast_t *ibp_anti_try(pcas_ast_t *e, pcas_ast_t *var) {
    return integrate_node(e, var);
}

/* ---------- main integrator ---------- */
static pcas_ast_t *integrate_node(pcas_ast_t *expr, pcas_ast_t *var) {
    /* constants */
    if (is_constant_internal(expr, var)) {
        return ast_MakeBinary(OP_MULT, ast_Copy(expr), ast_Copy(var));
    }

    /* ∫ x dx */
    if (expr->type == NODE_SYMBOL && var->type == NODE_SYMBOL &&
        expr->op.symbol == var->op.symbol) {
        pcas_ast_t *pow2 = ast_MakeBinary(OP_POW, ast_Copy(expr), ast_MakeNumber(num_FromInt(2)));
        return ast_MakeBinary(OP_DIV, pow2, ast_MakeNumber(num_FromInt(2)));
    }

    if (expr->type == NODE_OPERATOR) {
        OperatorType op = optype(expr);

        /* Sum rule */
        if (op == OP_ADD) {
            pcas_ast_t *sum = ast_MakeOperator(OP_ADD);
            for (pcas_ast_t *ch = ast_ChildGet(expr, 0); ch != NULL; ch = ch->next) {
                pcas_ast_t *part = integrate_node(ch, var);
                if (!part) { ast_Cleanup(sum); return NULL; }
                ast_ChildAppend(sum, part);
            }
            return sum;
        }

        /* LOGS */
        if (op == OP_LOG) {
            pcas_ast_t *base = ast_ChildGet(expr, 0);
            pcas_ast_t *arg  = ast_ChildGet(expr, 1);

            /* ln(x) -> x ln x - x */
            if (base && base->type == NODE_SYMBOL && base->op.symbol == SYM_EULER &&
                arg && ast_Compare(arg, var)) {
                pcas_ast_t *lnx  = ast_MakeBinary(OP_LOG, ast_MakeSymbol(SYM_EULER), ast_Copy(var));
                pcas_ast_t *xlnx = ast_MakeBinary(OP_MULT, ast_Copy(var), lnx);
                return ast_MakeBinary(OP_ADD, xlnx,
                        ast_MakeBinary(OP_MULT, ast_MakeNumber(num_FromInt(-1)), ast_Copy(var)));
            }

            /* log_b(x) -> (x ln x - x) / ln b */
            if (arg && ast_Compare(arg, var) && base && is_constant_internal(base, var)) {
                pcas_ast_t *lnx  = ast_MakeBinary(OP_LOG, ast_MakeSymbol(SYM_EULER), ast_Copy(var));
                pcas_ast_t *xlnx = ast_MakeBinary(OP_MULT, ast_Copy(var), lnx);
                pcas_ast_t *num  = ast_MakeBinary(OP_ADD, xlnx,
                                   ast_MakeBinary(OP_MULT, ast_MakeNumber(num_FromInt(-1)), ast_Copy(var)));
                pcas_ast_t *lnb  = ast_MakeBinary(OP_LOG, ast_MakeSymbol(SYM_EULER), ast_Copy(base));
                return ast_MakeBinary(OP_DIV, num, lnb);
            }
        }

        /* ---------- Targeted: polynomial * trig (guaranteed IBP) ---------- */
        if (op == OP_MULT && s_ibp_enabled && s_ibp_depth < s_ibp_max_depth) {
            pcas_ast_t *poly = NULL, *trig = NULL, *other = NULL;
            unsigned nchild = ast_ChildLength(expr);

            for (pcas_ast_t *ch = ast_ChildGet(expr, 0); ch; ch = ch->next) {
                if (!poly && ch->type == NODE_OPERATOR && optype(ch) == OP_POW) {
                    pcas_ast_t *b = ast_ChildGet(ch, 0);
                    pcas_ast_t *p = ast_ChildGet(ch, 1);
                    if (b && ast_Compare(b, var) && p && p->type == NODE_NUMBER &&
                        mp_rat_compare_value(p->op.num, 1, 1) >= 0) {
                        poly = ch; continue;
                    }
                }
                if (!trig && ch->type == NODE_OPERATOR &&
                    (optype(ch) == OP_SIN || optype(ch) == OP_COS)) {
                    pcas_ast_t *a = ast_ChildGet(ch, 0);
                    if (a && ast_Compare(a, var)) { trig = ch; continue; }
                }
                other = ch;
            }

            if (poly && trig && (!other || is_constant_internal(other, var))) {
                pcas_ast_t *u  = ast_Copy(poly);
                pcas_ast_t *dv = ast_Copy(trig);

                pcas_ast_t *v = NULL;
                if (optype(trig) == OP_SIN) {
                    v = ast_MakeBinary(OP_MULT, ast_MakeNumber(num_FromInt(-1)),
                        ast_MakeUnary(OP_COS, ast_Copy(var)));
                } else {
                    v = ast_MakeUnary(OP_SIN, ast_Copy(var));
                }

                pcas_ast_t *du = ibp_diff(u, var);

                /* include any constant factor in v */
                if (nchild > 2) {
                    pcas_ast_t *const_k = NULL;
                    for (pcas_ast_t *ch = ast_ChildGet(expr, 0); ch; ch = ch->next) {
                        if (ch != poly && ch != trig && is_constant_internal(ch, var)) {
                            const_k = const_k ? ast_MakeBinary(OP_MULT, const_k, ast_Copy(ch))
                                              : ast_Copy(ch);
                        }
                    }
                    if (const_k) v = ast_MakeBinary(OP_MULT, const_k, v);
                }

                pcas_ast_t *uv  = ast_MakeBinary(OP_MULT, ast_Copy(u), ast_Copy(v));
                pcas_ast_t *vdu = ast_MakeBinary(OP_MULT, ast_Copy(v), du);

                /* CRITICAL: simplify v*du before recursing */
                simplify(vdu, SIMP_NORMALIZE | SIMP_COMMUTATIVE | SIMP_RATIONAL | SIMP_EVAL | SIMP_LIKE_TERMS);

                pcas_ast_t *res = NULL;
                if (s_ibp_depth < s_ibp_max_depth) {
                    s_ibp_depth++;
                    pcas_ast_t *rest = integrate_node(vdu, var);
                    s_ibp_depth--;
                    if (rest) {
                        res = ast_MakeBinary(OP_ADD, uv,
                              ast_MakeBinary(OP_MULT, ast_MakeNumber(num_FromInt(-1)), rest));
                        simplify(res, SIMP_NORMALIZE | SIMP_RATIONAL | SIMP_COMMUTATIVE | SIMP_EVAL | SIMP_LIKE_TERMS);
                        ast_Cleanup(v);
                        ast_Cleanup(u);
                        return res;
                    }
                }
                ast_Cleanup(uv);
                ast_Cleanup(v);
                ast_Cleanup(u);
                return NULL;
            }
        }

        /* Product: constant multiple rule first; then generic IBP at end */
        if (op == OP_MULT) {
            pcas_ast_t *const_factor = NULL;
            pcas_ast_t *nonconst_prod = NULL;

            for (pcas_ast_t *ch = ast_ChildGet(expr, 0); ch != NULL; ch = ch->next) {
                if (is_constant_internal(ch, var)) {
                    const_factor = const_factor
                        ? ast_MakeBinary(OP_MULT, const_factor, ast_Copy(ch))
                        : ast_Copy(ch);
                } else {
                    nonconst_prod = nonconst_prod
                        ? ast_MakeBinary(OP_MULT, nonconst_prod, ast_Copy(ch))
                        : ast_Copy(ch);
                }
            }

            if (nonconst_prod && const_factor) {
                pcas_ast_t *inside = integrate_node(nonconst_prod, var);
                if (!inside) { ast_Cleanup(const_factor); return NULL; }
                return ast_MakeBinary(OP_MULT, const_factor, inside);
            }
        }

        /* Powers & exponentials */
        if (op == OP_POW) {
            pcas_ast_t *base = ast_ChildGet(expr, 0);
            pcas_ast_t *expo = ast_ChildGet(expr, 1);

            /* (c*v)^n with exactly one variable factor v and constant n */
            if (base && base->type == NODE_OPERATOR && optype(base) == OP_MULT &&
                expo && is_constant_internal(expo, var)) {

                pcas_ast_t *ch, *const_prod = NULL, *var_factor = NULL;
                int var_count = 0;

                for (ch = ast_ChildGet(base, 0); ch != NULL; ch = ch->next) {
                    if (is_constant_internal(ch, var)) {
                        const_prod = const_prod
                            ? ast_MakeBinary(OP_MULT, const_prod, ast_Copy(ch))
                            : ast_Copy(ch);
                    } else {
                        var_count++;
                        var_factor = var_factor
                            ? ast_MakeBinary(OP_MULT, var_factor, ast_Copy(ch))
                            : ast_Copy(ch);
                    }
                }

                if (var_count == 1 && var_factor) {
                    pcas_ast_t *c_pow_n = const_prod
                        ? ast_MakeBinary(OP_POW, const_prod, ast_Copy(expo))
                        : ast_MakeNumber(num_FromInt(1));

                    if (simplifies_to_minus_one(expo)) {
                        pcas_ast_t *ln_v = ast_MakeBinary(OP_LOG, ast_MakeSymbol(SYM_EULER), ast_Copy(var_factor));
                        return ast_MakeBinary(OP_MULT, c_pow_n, ln_v);
                    } else {
                        pcas_ast_t *one = ast_MakeNumber(num_FromInt(1));
                        pcas_ast_t *n_plus_1 = ast_MakeBinary(OP_ADD, ast_Copy(expo), one);
                        pcas_ast_t *v_pow = ast_MakeBinary(OP_POW, ast_Copy(var_factor), ast_Copy(n_plus_1));
                        pcas_ast_t *num = ast_MakeBinary(OP_MULT, c_pow_n, v_pow);
                        return ast_MakeBinary(OP_DIV, num, n_plus_1);
                    }
                }
            }

            /* x^n (n constant) */
            if (base && expo &&
                ast_Compare(base, var) && is_constant_internal(expo, var)) {

                if (simplifies_to_minus_one(expo)) {
                    return ast_MakeBinary(OP_LOG, ast_MakeSymbol(SYM_EULER), ast_Copy(base));
                } else {
                    pcas_ast_t *one = ast_MakeNumber(num_FromInt(1));
                    pcas_ast_t *n1  = ast_MakeBinary(OP_ADD, ast_Copy(expo), one);
                    pcas_ast_t *pow = ast_MakeBinary(OP_POW, ast_Copy(base), ast_Copy(n1));
                    return ast_MakeBinary(OP_DIV, pow, n1);
                }
            }

            /* a^x where a is constant */
            if (base && expo && is_constant_internal(base, var) && ast_Compare(expo, var)) {
                pcas_ast_t *ln_a = ast_MakeBinary(OP_LOG, ast_MakeSymbol(SYM_EULER), ast_Copy(base));
                return ast_MakeBinary(OP_DIV, ast_Copy(expr), ln_a);
            }

            /* cos^2 / sin^2 */
            if (expo && expo->type == NODE_NUMBER && mp_rat_compare_value(expo->op.num, 2, 1) == 0) {
                if (base && base->type == NODE_OPERATOR) {
                    OperatorType bop = optype(base);
                    pcas_ast_t *arg = ast_ChildGet(base, 0);
                    if (arg && ast_Compare(arg, var)) {
                        if (bop == OP_COS) {
                            pcas_ast_t *x_over_2 =
                                ast_MakeBinary(OP_DIV, ast_Copy(var), ast_MakeNumber(num_FromInt(2)));
                            pcas_ast_t *two_x = ast_MakeBinary(OP_MULT, ast_MakeNumber(num_FromInt(2)), ast_Copy(var));
                            pcas_ast_t *sin2x = ast_MakeUnary(OP_SIN, two_x);
                            pcas_ast_t *sin_term =
                                ast_MakeBinary(OP_DIV, sin2x, ast_MakeNumber(num_FromInt(4)));
                            return ast_MakeBinary(OP_ADD, x_over_2, sin_term);
                        } else if (bop == OP_SIN) {
                            pcas_ast_t *x_over_2 =
                                ast_MakeBinary(OP_DIV, ast_Copy(var), ast_MakeNumber(num_FromInt(2)));
                            pcas_ast_t *two_x = ast_MakeBinary(OP_MULT, ast_MakeNumber(num_FromInt(2)), ast_Copy(var));
                            pcas_ast_t *sin2x = ast_MakeUnary(OP_SIN, two_x);
                            pcas_ast_t *sin_term =
                                ast_MakeBinary(OP_DIV, sin2x, ast_MakeNumber(num_FromInt(4)));
                            pcas_ast_t *neg_sin = ast_MakeBinary(OP_MULT, ast_MakeNumber(num_FromInt(-1)), sin_term);
                            return ast_MakeBinary(OP_ADD, x_over_2, neg_sin);
                        }
                    }
                }
            }
        }

        /* Trig basics */
        if (op == OP_SIN) {
            pcas_ast_t *arg = ast_ChildGet(expr, 0);
            if (arg && ast_Compare(arg, var)) {
                pcas_ast_t *cosx = ast_MakeUnary(OP_COS, ast_Copy(arg));
                return ast_MakeBinary(OP_MULT, ast_MakeNumber(num_FromInt(-1)), cosx);
            }
        }
        if (op == OP_COS) {
            pcas_ast_t *arg2 = ast_ChildGet(expr, 0);
            if (arg2 && ast_Compare(arg2, var)) {
                return ast_MakeUnary(OP_SIN, ast_Copy(arg2));
            }
        }

        /* LAST: generic IBP */
        if (s_ibp_enabled && op == OP_MULT && s_ibp_depth < s_ibp_max_depth) {
            pcas_ast_t *by_parts = ibp_try_once(expr, var);
            if (by_parts) return by_parts;
        }
    }

    return NULL; /* unsupported */
}

/* Public API: replace `e` with its antiderivative (in place) */
void antiderivative(pcas_ast_t *e, pcas_ast_t *respect_to) {
    if (!e || !respect_to) return;

    pcas_ast_t *res = integrate_node(e, respect_to);
    if (!res) {
        /* fallback: keep original */
        return;
    }
    replace_node(e, res);
    simplify(e, SIMP_NORMALIZE | SIMP_RATIONAL | SIMP_COMMUTATIVE | SIMP_EVAL | SIMP_LIKE_TERMS);
}
