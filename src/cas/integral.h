#ifndef INTEGRAL_H_
#define INTEGRAL_H_

#include "../ast.h"

/*
 * Computes the antiderivative (indefinite integral) of an expression with
 * respect to a given variable. See integral.c for the implementation details.
 *
 * Parameters:
 *  e          - the AST node to integrate; upon return it will contain the integral
 *  respect_to - the variable with respect to which the integral is taken
 */
void antiderivative(pcas_ast_t *e, pcas_ast_t *respect_to);
void integral_set_ibp_enabled(bool on);
#endif /* INTEGRAL_H_ */
