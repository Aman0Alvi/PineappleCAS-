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
#include "cas.h"     /* for replace_node, simplify */
#include "identities.h"

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
    /* evaluate constants so  -1, (-2+1),  (-3/3)  etc. all reduce to NUMBER -1 */
    simplify(tmp, SIMP_EVAL | SIMP_RATIONAL | SIMP_NORMALIZE | SIMP_COMMUTATIVE);
    if (tmp->type == NODE_NUMBER && mp_rat_compare_value(tmp->op.num, -1, 1) == 0) {
        res = true;
    }
    ast_Cleanup(tmp);
    return res;
}

/* Build an AST for ∫ expr d(var). Caller must free the returned node. */
static pcas_ast_t *integrate_node(pcas_ast_t *expr, pcas_ast_t *var) {
    /* Constant rule: ∫ c dx = c·x */
    if (is_constant_internal(expr, var)) {
        return ast_MakeBinary(OP_MULT, ast_Copy(expr), ast_Copy(var));
    }

    /* ∫ x dx = x^2/2 */
    if (expr->type == NODE_SYMBOL && var->type == NODE_SYMBOL &&
        expr->op.symbol == var->op.symbol) {
        pcas_ast_t *pow2;
        pow2 = ast_MakeBinary(OP_POW,
               ast_Copy(expr), ast_MakeNumber(num_FromInt(2)));
        return ast_MakeBinary(OP_DIV, pow2, ast_MakeNumber(num_FromInt(2)));
    }

    /* Operators */
    if (expr->type == NODE_OPERATOR) {
        OperatorType op = optype(expr);

        /* Sum rule */
        if (op == OP_ADD) {
            pcas_ast_t *sum = ast_MakeOperator(OP_ADD);
            pcas_ast_t *ch;
            for (ch = ast_ChildGet(expr, 0); ch != NULL; ch = ch->next) {
                ast_ChildAppend(sum, integrate_node(ch, var));
            }
            return sum;
        }

        /* Constant multiple rule: pull constants out of a product */
        if (op == OP_MULT) {
            pcas_ast_t *const_factor = NULL;
            pcas_ast_t *nonconst_prod = NULL;
            pcas_ast_t *ch;

            for (ch = ast_ChildGet(expr, 0); ch != NULL; ch = ch->next) {
                if (is_constant_internal(ch, var)) {
                    if (const_factor) {
                        const_factor = ast_MakeBinary(OP_MULT, const_factor, ast_Copy(ch));
                    } else {
                        const_factor = ast_Copy(ch);
                    }
                } else {
                    if (nonconst_prod) {
                        nonconst_prod = ast_MakeBinary(OP_MULT, nonconst_prod, ast_Copy(ch));
                    } else {
                        nonconst_prod = ast_Copy(ch);
                    }
                }
            }

            if (const_factor && nonconst_prod) {
                pcas_ast_t *integrated = integrate_node(nonconst_prod, var);
                return ast_MakeBinary(OP_MULT, const_factor, integrated);
            }
        }

        /* Power rule / exponential */
        if (op == OP_POW) {
            pcas_ast_t *base = ast_ChildGet(expr, 0);
            pcas_ast_t *expo = ast_ChildGet(expr, 1);

            /* x^n where n is constant (n may be rational like 1/2, 3/2, etc.) */
            if (ast_Compare(base, var) && is_constant_internal(expo, var)) {
                /* special case: n == -1 -> ln(x) */
                if (simplifies_to_minus_one(expo)) {
                    return ast_MakeBinary(OP_LOG, ast_MakeSymbol(SYM_EULER), ast_Copy(base));
                } else {
                    /* general: x^(n+1)/(n+1) */
                    pcas_ast_t *one, *n_plus_1, *pow_node;
                    one = ast_MakeNumber(num_FromInt(1));
                    /* build (n + 1) once and reuse (deep-copied below) */
                    n_plus_1 = ast_MakeBinary(OP_ADD, ast_Copy(expo), one);
                    pow_node = ast_MakeBinary(OP_POW, ast_Copy(base), ast_Copy(n_plus_1));
                    return ast_MakeBinary(OP_DIV, pow_node, n_plus_1);
                }
            }

            /* a^x where a is constant */
            if (is_constant_internal(base, var) && ast_Compare(expo, var)) {
                /* ∫ a^x dx = a^x / ln(a) */
                pcas_ast_t *ln_a;
                ln_a = ast_MakeBinary(OP_LOG, ast_MakeSymbol(SYM_EULER), ast_Copy(base));
                return ast_MakeBinary(OP_DIV, ast_Copy(expr), ln_a);
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
    }

    /* unsupported: return a copy so caller can keep composing rules later */
    return ast_Copy(expr);
}

/* Public API: replace `e` with its antiderivative (in place) */
void antiderivative(pcas_ast_t *e, pcas_ast_t *respect_to) {
    pcas_ast_t *result;
    if (!e || !respect_to) return;
    result = integrate_node(e, respect_to);
    replace_node(e, result);
}
