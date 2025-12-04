#include "conic.h"
#include "cas.h"
#include "../parser.h"
#include <string.h>
#include <stdio.h>
#include <stdlib.h>

/* Forward declarations */
static void extract_all_coefficients(pcas_ast_t *expr, mp_rat *A, mp_rat *B, mp_rat *C, 
                                      mp_rat *D, mp_rat *E, mp_rat *F);
static void extract_coefficients_recursive(pcas_ast_t *expr, int negate, 
                                            mp_rat *A, mp_rat *B, mp_rat *C, 
                                            mp_rat *D, mp_rat *E, mp_rat *F);
static mp_rat extract_power_coeff(pcas_ast_t *term, Symbol var, int expected_pow);
static ConicType classify_type(mp_rat discriminant);
static mp_rat negate_rat(mp_rat val);
static mp_rat divide_rat(mp_rat num, mp_rat denom);
static void compute_canonical_params(ConicResult *result);

/*
 * Check if two AST nodes are equivalent
 */
__attribute__((unused))
static bool ast_nodes_equal(pcas_ast_t *a, pcas_ast_t *b) {
    if (a == NULL && b == NULL) return true;
    if (a == NULL || b == NULL) return false;
    
    if (a->type != b->type) return false;
    
    if (a->type == NODE_NUMBER) {
        return mp_rat_compare(a->op.num, b->op.num) == 0;
    } else if (a->type == NODE_SYMBOL) {
        return a->op.symbol == b->op.symbol;
    }
    
    return false;
}

/*
 * Extract the power of a variable in a term
 * Returns the coefficient if the term is of form coeff*X^pow or just X^pow, etc.
 * Returns NULL if term doesn't match the expected power
 */
static mp_rat extract_power_coeff(pcas_ast_t *term, Symbol var, int expected_pow) {
    if (term == NULL) return NULL;
    
    /* Single power: X^2 or Y^2 */
    if (isoptype(term, OP_POW)) {
        pcas_ast_t *base = ast_ChildGet(term, 0);
        pcas_ast_t *power = ast_ChildGet(term, 1);
        
        if (base && base->type == NODE_SYMBOL && base->op.symbol == var &&
            power && power->type == NODE_NUMBER &&
            mp_rat_compare_value(power->op.num, expected_pow, 1) == 0) {
            return num_FromInt(1);  /* Coefficient is 1 */
        }
        return NULL;
    }
    
    /* Single symbol: X or Y */
    if (expected_pow == 1 && term->type == NODE_SYMBOL && term->op.symbol == var) {
        return num_FromInt(1);  /* Coefficient is 1 */
    }
    
    /* Multiplication: coeff * X^pow or coeff * X, etc. */
    if (isoptype(term, OP_MULT)) {
        unsigned i;
        mp_rat coeff = num_FromInt(1);
        int found_var = 0;
        
        for (i = 0; i < ast_ChildLength(term); i++) {
            pcas_ast_t *child = ast_ChildGet(term, i);
            
            if (child->type == NODE_NUMBER) {
                /* Multiply coefficient */
                mp_rat temp = num_Copy(coeff);
                mp_rat_mul(temp, child->op.num, coeff);
                num_Cleanup(temp);
            } else if (child->type == NODE_SYMBOL && child->op.symbol == var && expected_pow == 1) {
                /* Found the variable to power 1 */
                if (found_var) {
                    num_Cleanup(coeff);
                    return NULL;  /* Multiple occurrences of var */
                }
                found_var = 1;
            } else if (isoptype(child, OP_POW)) {
                pcas_ast_t *base = ast_ChildGet(child, 0);
                pcas_ast_t *power = ast_ChildGet(child, 1);
                
                if (base && base->type == NODE_SYMBOL && base->op.symbol == var &&
                    power && power->type == NODE_NUMBER &&
                    mp_rat_compare_value(power->op.num, expected_pow, 1) == 0) {
                    /* Found the variable to expected power */
                    if (found_var) {
                        num_Cleanup(coeff);
                        return NULL;  /* Multiple occurrences */
                    }
                    found_var = 1;
                } else {
                    /* Wrong power or wrong variable */
                    num_Cleanup(coeff);
                    return NULL;
                }
            } else if (child->type == NODE_NUMBER) {
                /* Already handled above */
                continue;
            } else {
                /* Unknown term type */
                num_Cleanup(coeff);
                return NULL;
            }
        }
        
        if (found_var) {
            return coeff;
        }
        num_Cleanup(coeff);
        return NULL;
    }
    
    /* Constant term */
    if (expected_pow == 0 && term->type == NODE_NUMBER) {
        return num_Copy(term->op.num);
    }
    
    return NULL;
}

/*
 * Recursively extract coefficients from an expression tree
 * Handles OP_ADD by traversing all children (subtraction is represented as ADD with -1 * term)
 */
static void extract_coefficients_recursive(pcas_ast_t *expr, int negate, 
                                            mp_rat *A, mp_rat *B, mp_rat *C, 
                                            mp_rat *D, mp_rat *E, mp_rat *F) {
    if (expr == NULL) return;
    
    /* Handle addition (parser converts subtraction to ADD with -1 mult) */
    if (isoptype(expr, OP_ADD)) {
        unsigned i;
        for (i = 0; i < ast_ChildLength(expr); i++) {
            pcas_ast_t *term = ast_ChildGet(expr, i);
            extract_coefficients_recursive(term, negate, A, B, C, D, E, F);
        }
        return;
    }
    
    /* Try to extract coefficients for each power combination */
    mp_rat coeff = NULL;
    
    /* Try Ax^2 */
    coeff = extract_power_coeff(expr, SYM_X, 2);
    if (coeff != NULL) {
        if (negate) {
            mp_rat neg = negate_rat(coeff);
            mp_rat_add(*A, neg, *A);
            num_Cleanup(neg);
        } else {
            mp_rat_add(*A, coeff, *A);
        }
        num_Cleanup(coeff);
        return;
    }
    
    /* Try Cy^2 */
    coeff = extract_power_coeff(expr, SYM_Y, 2);
    if (coeff != NULL) {
        if (negate) {
            mp_rat neg = negate_rat(coeff);
            mp_rat_add(*C, neg, *C);
            num_Cleanup(neg);
        } else {
            mp_rat_add(*C, coeff, *C);
        }
        num_Cleanup(coeff);
        return;
    }
    
    /* Try Dx (x to power 1) */
    coeff = extract_power_coeff(expr, SYM_X, 1);
    if (coeff != NULL) {
        if (negate) {
            mp_rat neg = negate_rat(coeff);
            mp_rat_add(*D, neg, *D);
            num_Cleanup(neg);
        } else {
            mp_rat_add(*D, coeff, *D);
        }
        num_Cleanup(coeff);
        return;
    }
    
    /* Try Ey (y to power 1) */
    coeff = extract_power_coeff(expr, SYM_Y, 1);
    if (coeff != NULL) {
        if (negate) {
            mp_rat neg = negate_rat(coeff);
            mp_rat_add(*E, neg, *E);
            num_Cleanup(neg);
        } else {
            mp_rat_add(*E, coeff, *E);
        }
        num_Cleanup(coeff);
        return;
    }
    
    /* Try constant F */
    if (expr->type == NODE_NUMBER) {
        mp_rat const_val = num_Copy(expr->op.num);
        if (negate) {
            mp_rat neg = negate_rat(const_val);
            mp_rat_add(*F, neg, *F);
            num_Cleanup(neg);
        } else {
            mp_rat_add(*F, const_val, *F);
        }
        num_Cleanup(const_val);
        return;
    }
    
    /* For Bxy, we'd need to check for x*y specifically, but we'll ignore that for now */
}

/*
 * Extract all coefficients from the polynomial: Ax^2 + Bxy + Cy^2 + Dx + Ey + F
 */
static void extract_all_coefficients(pcas_ast_t *expr, mp_rat *A, mp_rat *B, mp_rat *C, 
                                      mp_rat *D, mp_rat *E, mp_rat *F) {
    *A = num_FromInt(0);
    *B = num_FromInt(0);
    *C = num_FromInt(0);
    *D = num_FromInt(0);
    *E = num_FromInt(0);
    *F = num_FromInt(0);
    
    if (expr == NULL) return;
    
    extract_coefficients_recursive(expr, 0, A, B, C, D, E, F);
}

/*
 * Classify conic type based on discriminant B^2 - 4AC
 */
static ConicType classify_type(mp_rat discriminant) {
    int cmp = mp_rat_compare_value(discriminant, 0, 1);
    
    if (cmp < 0) {
        /* B^2 - 4AC < 0 => Ellipse or Circle */
        return CONIC_ELLIPSE;
    } else if (cmp == 0) {
        /* B^2 - 4AC = 0 => Parabola */
        return CONIC_PARABOLA;
    } else {
        /* B^2 - 4AC > 0 => Hyperbola */
        return CONIC_HYPERBOLA;
    }
}

/*
 * Helper: Format a rational number as a string with given precision
 */
__attribute__((unused))
static char *format_rational(mp_rat val, int precision) {
    return num_ToString(val, precision);
}

/*
 * Helper: Negate a rational number
 */
static mp_rat negate_rat(mp_rat val) {
    mp_rat neg = num_Copy(val);
    mp_rat zero = num_FromInt(0);
    mp_rat_sub(zero, neg, neg);
    num_Cleanup(zero);
    return neg;
}

/*
 * Helper: Divide two rational numbers
 */
__attribute__((unused))
static mp_rat divide_rat(mp_rat num, mp_rat denom) {
    mp_rat result = num_Copy(num);
    mp_rat_div(result, denom, result);
    return result;
}

/*
 * Complete the square for: Ax^2 + Bxy + Cy^2 + Dx + Ey + F = rhs
 * Computes center (h, k) and axes parameters for canonical form.
 * (Currently simplified for circles/ellipses/hyperbolas with B=0)
 */
pcas_ast_t *conic_CompleteSquare(mp_rat A, mp_rat B, mp_rat C, mp_rat D, mp_rat E, mp_rat F) {
    /* For now, return a simple representation: Ax^2 + Cy^2 + ... = 0 */
    /* Full implementation would complete the square algebraically */
    
    (void)A; (void)B; (void)C; (void)D; (void)E; (void)F; /* Suppress unused parameter warnings */
    
    pcas_ast_t *result = ast_MakeNumber(num_FromInt(0));
    return result;
}

/*
 * Compute canonical form parameters for ellipse/hyperbola
 * Stores center (h, k) and axes lengths (a, b) in result
 */
static void compute_canonical_params(ConicResult *result) {
    /* For equations with B=0 (no xy term):
     * Ax^2 + Bxy + Cy^2 + Dx + Ey + F = 0  (after moving RHS)
     * 
     * Complete the square:
     * A(x^2 + D/A*x) + C(y^2 + E/C*y) + F = 0
     * A((x + D/2A)^2 - (D/2A)^2) + C((y + E/2C)^2 - (E/2C)^2) + F = 0
     * A(x + D/2A)^2 + C(y + E/2C)^2 = A(D/2A)^2 + C(E/2C)^2 - F
     * 
     * For standard form (x-h)^2/a^2 + (y-k)^2/b^2 = 1:
     * Divide both sides by RHS value:
     * A(x-h)^2/RHS + C(y-k)^2/RHS = 1
     * So: a^2 = RHS/A, b^2 = RHS/C
     * 
     * For parabolas (B^2 - 4AC = 0):
     * If A != 0 and C = 0: (y-k)^2 = 4p(x-h)  [opens left/right]
     * If A = 0 and C != 0: (x-h)^2 = 4p(y-k)  [opens up/down]
     * where p = focal parameter (distance from vertex to focus)
     */
    
    /* Check if B is non-zero (rotated conic) */
    int b_is_zero = mp_rat_compare_value(result->B, 0, 1) == 0;
    
    if (!b_is_zero) {
        /* For rotated conics, just set defaults */
        result->center_h = num_FromInt(0);
        result->center_k = num_FromInt(0);
        result->a = num_FromInt(0);
        result->b = num_FromInt(0);
        return;
    }
    
    /* Check for degenerate cases */
    int a_is_zero = mp_rat_compare_value(result->A, 0, 1) == 0;
    int c_is_zero = mp_rat_compare_value(result->C, 0, 1) == 0;
    
    if (a_is_zero && c_is_zero) {
        result->center_h = num_FromInt(0);
        result->center_k = num_FromInt(0);
        result->a = num_FromInt(0);
        result->b = num_FromInt(0);
        return;
    }
    
    /* Special handling for parabolas */
    if (result->type == CONIC_PARABOLA) {
        if (!a_is_zero && c_is_zero) {
            /* Parabola: (y-k)^2 = 4p(x-h)  (opens left/right) */
            /* From: Ax^2 + Dx + Ey + F = 0
             * Complete square: A(x + D/2A)^2 + Ey + F - A(D/2A)^2 = 0
             * A(x + D/2A)^2 = -Ey - F + A(D/2A)^2
             * (y - k)^2 = 4p(x - h) where k = -E/(2C) but C=0...
             * Need different approach: y = -A(x-h)^2/E + k_offset
             * Actually: E*y = -A(x-h)^2 + constant
             * (x-h)^2 = -E/A*(y - k)
             * So: (y-k)^2 = -A/E*(x-h) but form should be (y-k)^2 = 4p(x-h)
             * Therefore: 4p = -A/E, so p = -A/(4E)
             */
            
            /* Vertex h coordinate: h = -D/(2A) */
            mp_rat two_A = num_FromInt(2);
            mp_rat_mul(two_A, result->A, two_A);
            result->center_h = num_Copy(result->D);
            mp_rat neg = negate_rat(result->center_h);
            num_Cleanup(result->center_h);
            result->center_h = neg;
            mp_rat_div(result->center_h, two_A, result->center_h);
            num_Cleanup(two_A);
            
            /* Vertex k coordinate: from Ax^2 + Dx + Ey + F = 0 at x=h
             * Ah^2 + Dh + Ey + F = 0 => E*y = -A*h^2 - D*h - F => y = (-A*h^2 - D*h - F)/E
             */
            if (!mp_rat_compare_value(result->E, 0, 1) == 0) {
                mp_rat numerator = num_FromInt(0);
                
                mp_rat ah2 = num_Copy(result->A);
                mp_rat_mul(ah2, result->center_h, ah2);
                mp_rat_mul(ah2, result->center_h, ah2);
                mp_rat_add(numerator, ah2, numerator);
                
                mp_rat dh = num_Copy(result->D);
                mp_rat_mul(dh, result->center_h, dh);
                mp_rat_add(numerator, dh, numerator);
                
                mp_rat_add(numerator, result->F, numerator);
                
                mp_rat neg_num = negate_rat(numerator);
                num_Cleanup(numerator);
                
                result->center_k = num_Copy(neg_num);
                mp_rat_div(result->center_k, result->E, result->center_k);
                
                num_Cleanup(neg_num);
                num_Cleanup(ah2);
                num_Cleanup(dh);
            } else {
                result->center_k = num_FromInt(0);
            }
            
            /* Focal parameter p: from (y-k)^2 = 4p(x-h)
             * Original form: Ax^2 + Dx + Ey + F = 0
             * After completing square: A(x-h)^2 = -Ey - F + A*h^2 + D*h
             *                          (x-h) = (-E*y - F + A*h^2 + D*h) / A
             * Rearrange: E*y = -A(x-h)^2 + (A*h^2 + D*h - F)
             *            y - k = (-A/E)(x-h)^2 + const
             * But we want (y-k)^2 = 4p(x-h), so we solve differently:
             * From Ax^2 + Dx + Ey + F = 0, the coefficient of x is A
             * (y-k)^2 = -E/A*(x-h), so 4p = -E/A => p = -E/(4A)
             */
            mp_rat four_A = num_FromInt(4);
            mp_rat_mul(four_A, result->A, four_A);
            result->a = num_Copy(result->E);  /* Using 'a' to store p */
            mp_rat neg_E = negate_rat(result->a);
            num_Cleanup(result->a);
            result->a = neg_E;
            mp_rat_div(result->a, four_A, result->a);
            num_Cleanup(four_A);
            
            result->b = num_FromInt(0);  /* Not used for parabola */
            
        } else if (a_is_zero && !c_is_zero) {
            /* Parabola: (x-h)^2 = 4p(y-k)  (opens up/down) */
            
            /* Vertex h coordinate: h = -D/(2A) but A=0, so from Cy^2 + Ey + F = 0 at y=k
             * Need to find x at vertex. From Cy^2 + Dx + Ey + F = 0
             * D*x = -C*y^2 - E*y - F => x = (-C*y^2 - E*y - F)/D (if D != 0)
             * Or if D=0, vertex x = 0
             */
            if (!mp_rat_compare_value(result->D, 0, 1) == 0) {
                /* h = 0, but we can compute from the equation if needed */
                result->center_h = num_FromInt(0);
            } else {
                result->center_h = num_FromInt(0);
            }
            
            /* Vertex k coordinate: k = -E/(2C) */
            mp_rat two_C = num_FromInt(2);
            mp_rat_mul(two_C, result->C, two_C);
            result->center_k = num_Copy(result->E);
            mp_rat neg = negate_rat(result->center_k);
            num_Cleanup(result->center_k);
            result->center_k = neg;
            mp_rat_div(result->center_k, two_C, result->center_k);
            num_Cleanup(two_C);
            
            /* Focal parameter p: (x-h)^2 = 4p(y-k)
             * From Cy^2 + Dx + Ey + F = 0: C(y-k)^2 + D*x = const after completing square
             * (y-k)^2 = (const - D*x)/C => D*x = const - C(y-k)^2
             * x = (const - C(y-k)^2)/D, so 4p = -C/D => p = -C/(4D) (if D != 0)
             */
            if (!mp_rat_compare_value(result->D, 0, 1) == 0) {
                mp_rat four_D = num_FromInt(4);
                mp_rat_mul(four_D, result->D, four_D);
                result->a = num_Copy(result->C);  /* Using 'a' to store p */
                mp_rat neg_C = negate_rat(result->a);
                num_Cleanup(result->a);
                result->a = neg_C;
                mp_rat_div(result->a, four_D, result->a);
                num_Cleanup(four_D);
            } else {
                result->a = num_FromInt(0);
            }
            
            result->b = num_FromInt(0);  /* Not used for parabola */
        }
        return;  /* Skip ellipse/hyperbola computation for parabolas */
    }
    
    /* Compute center coordinates */
    if (!a_is_zero) {
        /* h = -D / (2A) */
        mp_rat two_A = num_FromInt(2);
        mp_rat_mul(two_A, result->A, two_A);
        result->center_h = num_Copy(result->D);
        mp_rat neg = negate_rat(result->center_h);
        num_Cleanup(result->center_h);
        result->center_h = neg;
        mp_rat_div(result->center_h, two_A, result->center_h);
        num_Cleanup(two_A);
    } else {
        result->center_h = num_FromInt(0);
    }
    
    if (!c_is_zero) {
        /* k = -E / (2C) */
        mp_rat two_C = num_FromInt(2);
        mp_rat_mul(two_C, result->C, two_C);
        result->center_k = num_Copy(result->E);
        mp_rat neg = negate_rat(result->center_k);
        num_Cleanup(result->center_k);
        result->center_k = neg;
        mp_rat_div(result->center_k, two_C, result->center_k);
        num_Cleanup(two_C);
    } else {
        result->center_k = num_FromInt(0);
    }
    
    /* For ellipse/hyperbola, compute a and b from standard form */
    if (!a_is_zero && !c_is_zero) {
        /* After completing the square, we have:
         * A(x-h)^2 + C(y-k)^2 = RHS_adjusted
         * 
         * RHS_adjusted = A*h^2 + C*k^2 - F
         * (Note: F already has RHS subtracted from original, so -F brings RHS back)
         */
        
        mp_rat rhs_adj = num_FromInt(0);
        
        /* Add A*h^2 */
        if (!a_is_zero) {
            mp_rat term = num_Copy(result->A);
            mp_rat_mul(term, result->center_h, term);
            mp_rat_mul(term, result->center_h, term);
            mp_rat_add(rhs_adj, term, rhs_adj);
            num_Cleanup(term);
        }
        
        /* Add C*k^2 */
        if (!c_is_zero) {
            mp_rat term = num_Copy(result->C);
            mp_rat_mul(term, result->center_k, term);
            mp_rat_mul(term, result->center_k, term);
            mp_rat_add(rhs_adj, term, rhs_adj);
            num_Cleanup(term);
        }
        
        /* Subtract F (which has RHS already subtracted) */
        mp_rat neg_f = negate_rat(result->F);
        mp_rat_add(rhs_adj, neg_f, rhs_adj);
        num_Cleanup(neg_f);
        
        /* Now compute a^2 = rhs_adj / A and b^2 = rhs_adj / C 
         * For hyperbolas, these might be negative; we take absolute values
         * to get the actual denominators for the standard form */
        result->a = num_Copy(rhs_adj);
        mp_rat_div(result->a, result->A, result->a);
        
        /* Take absolute value for a^2 */
        int a_is_negative = mp_rat_compare_value(result->a, 0, 1) < 0;
        if (a_is_negative) {
            mp_rat neg = negate_rat(result->a);
            num_Cleanup(result->a);
            result->a = neg;
        }
        
        result->b = num_Copy(rhs_adj);
        mp_rat_div(result->b, result->C, result->b);
        
        /* Take absolute value for b^2 */
        int b_is_negative = mp_rat_compare_value(result->b, 0, 1) < 0;
        if (b_is_negative) {
            mp_rat neg = negate_rat(result->b);
            num_Cleanup(result->b);
            result->b = neg;
        }
        
        num_Cleanup(rhs_adj);
    }
}

/*
 * Main function: Classify a conic section
 */
ConicResult *conic_Classify(pcas_ast_t *expression, mp_rat rhs_value) {
    ConicResult *result = (ConicResult *)malloc(sizeof(ConicResult));
    if (result == NULL) {
        return NULL;
    }
    
    memset(result, 0, sizeof(ConicResult));
    
    /* Extract coefficients from the expression
     * General form: Ax^2 + Bxy + Cy^2 + Dx + Ey + F = RHS
     * We rearrange to: Ax^2 + Bxy + Cy^2 + Dx + Ey + (F-RHS) = 0
     */
    
    extract_all_coefficients(expression, &result->A, &result->B, &result->C, 
                            &result->D, &result->E, &result->F);
    
    /* Store original RHS for canonical form computation */
    result->rhs_original = num_Copy(rhs_value);
    
    /* Adjust F by subtracting RHS (move RHS to left side: equation = 0) */
    mp_rat_sub(result->F, rhs_value, result->F);
    
    /* Calculate discriminant: B^2 - 4AC */
    result->discriminant = num_Copy(result->B);
    mp_rat_mul(result->discriminant, result->B, result->discriminant);
    
    mp_rat four_AC = num_FromInt(4);
    mp_rat_mul(four_AC, result->A, four_AC);
    mp_rat_mul(four_AC, result->C, four_AC);
    
    mp_rat_sub(result->discriminant, four_AC, result->discriminant);
    num_Cleanup(four_AC);
    
    /* Classify the conic type */
    result->type = classify_type(result->discriminant);
    
    /* Compute canonical form parameters */
    compute_canonical_params(result);
    
    /* Set type name and formula info */
    switch (result->type) {
        case CONIC_CIRCLE:
            strcpy(result->type_name, "Circle");
            break;
        case CONIC_ELLIPSE:
            strcpy(result->type_name, "Ellipse");
            break;
        case CONIC_PARABOLA:
            strcpy(result->type_name, "Parabola");
            break;
        case CONIC_HYPERBOLA:
            strcpy(result->type_name, "Hyperbola");
            break;
        case CONIC_DEGENERATE:
            strcpy(result->type_name, "Degenerate");
            break;
        default:
            strcpy(result->type_name, "Invalid");
            break;
    }
    
    /* Complete the square to get canonical form */
    result->canonical_form = conic_CompleteSquare(result->A, result->B, result->C, 
                                                   result->D, result->E, result->F);
    
    return result;
}

/*
 * Clean up a ConicResult structure
 */
void conic_ResultCleanup(ConicResult *result) {
    if (result == NULL) {
        return;
    }
    
    num_Cleanup(result->A);
    num_Cleanup(result->B);
    num_Cleanup(result->C);
    num_Cleanup(result->D);
    num_Cleanup(result->E);
    num_Cleanup(result->F);
    num_Cleanup(result->discriminant);
    num_Cleanup(result->center_h);
    num_Cleanup(result->center_k);
    num_Cleanup(result->a);
    num_Cleanup(result->b);
    num_Cleanup(result->c_dist);
    
    if (result->canonical_form != NULL) {
        ast_Cleanup(result->canonical_form);
    }
    
    free(result);
}
