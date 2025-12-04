#ifndef CONIC_H_
#define CONIC_H_

#include "../ast.h"

/* Conic section types */
typedef enum {
    CONIC_CIRCLE,
    CONIC_ELLIPSE,
    CONIC_PARABOLA,
    CONIC_HYPERBOLA,
    CONIC_DEGENERATE,
    CONIC_INVALID
} ConicType;

/* Structure to hold conic classification results */
typedef struct {
    ConicType type;
    
    /* Coefficients of general form: Ax^2 + Bxy + Cy^2 + Dx + Ey + F = 0 */
    mp_rat A, B, C, D, E, F;
    
    /* Original RHS value before moving to left side */
    mp_rat rhs_original;
    
    /* Discriminant B^2 - 4AC (used to classify conic) */
    mp_rat discriminant;
    
    /* Center of conic (h, k) */
    mp_rat center_h, center_k;
    
    /* For ellipse/hyperbola: semi-major axis length a, semi-minor axis length b */
    mp_rat a, b;
    
    /* For ellipse/hyperbola: distance from center to focus */
    mp_rat c_dist;
    
    /* For circles: radius */
    mp_rat radius;
    
    /* For parabolas: focal parameter p */
    mp_rat focal_param;
    
    /* For parabolas, ellipses, hyperbolas: focus coordinates (focus_x, focus_y) */
    /* For parabolas with vertical axis: focus_y = center_k + focal_param */
    /* For parabolas with horizontal axis: focus_x = center_h + focal_param */
    mp_rat focus_x, focus_y;
    
    /* For parabolas: directrix equation (stored as offset) */
    mp_rat directrix_offset;
    
    /* For hyperbolas: asymptote slopes (m1, m2) */
    mp_rat asymp_m1, asymp_m2;
    
    /* Canonical form: expression after completing the square */
    pcas_ast_t *canonical_form;
    
    /* String description of the conic type */
    char type_name[32];
} ConicResult;

/*
 * Classifies a conic section from a general two-variable polynomial equation.
 * 
 * The input expression should be a polynomial in x and y.
 * The function will extract coefficients of the general form:
 *   Ax^2 + Bxy + Cy^2 + Dx + Ey + F = 0
 * where F is the right-hand side value (e.g., if input is Ax^2 + ... = RHS,
 * all terms are moved to left and RHS becomes -F).
 *
 * Returns a ConicResult structure with classification and canonical form.
 * Caller is responsible for cleaning up result->canonical_form with ast_Cleanup().
 */
ConicResult *conic_Classify(pcas_ast_t *expression, mp_rat rhs_value);

/*
 * Completes the square for a polynomial and returns the canonical form.
 * Input should have been extracted as coefficients.
 * Returns an AST representing the canonical form (e.g., (x-h)^2 + (y-k)^2 = r^2).
 */
pcas_ast_t *conic_CompleteSquare(mp_rat A, mp_rat B, mp_rat C, mp_rat D, mp_rat E, mp_rat F);

/* Frees a ConicResult structure */
void conic_ResultCleanup(ConicResult *result);

#endif
