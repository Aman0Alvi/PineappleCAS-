#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "src/ast.h"
#include "src/imath/imrat.h"
#include "src/parser.h"
#include "src/cas/cas.h"

int main() {
    pcas_error_t err;
    
    /* Test case 1: Simple ellipse equation */
    printf("=== Test 1: Y1 = 9x^2-54x-19 ===\n");
    pcas_ast_t *expr1 = parse_from_string("9*X^2-54*X-19", &err);
    if (expr1 == NULL) {
        printf("Parse error: %s\n", error_text[err]);
        return 1;
    }
    
    /* Simplify it */
    simplify(expr1, SIMP_NORMALIZE | SIMP_COMMUTATIVE | SIMP_RATIONAL);
    
    printf("Expression parsed and simplified\n");
    printf("AST type: %d (0=number, 1=symbol, 2=operator)\n", expr1->type);
    if (expr1->type == NODE_OPERATOR) {
        printf("Operator type: %d (0=ADD, 1=MULT, etc)\n", expr1->op.operator.type);
        printf("Number of children: %u\n", ast_ChildLength(expr1));
        
        for (unsigned i = 0; i < ast_ChildLength(expr1); i++) {
            pcas_ast_t *child = ast_ChildGet(expr1, i);
            printf("  Child %u: type=%d", i, child->type);
            if (child->type == NODE_NUMBER) {
                char *numstr = num_ToString(child->op.num, 10);
                printf(" (number: %s)", numstr);
                free(numstr);
            } else if (child->type == NODE_OPERATOR) {
                printf(" (operator: %d)", child->op.operator.type);
            } else if (child->type == NODE_SYMBOL) {
                printf(" (symbol: %c)", child->op.symbol);
            }
            printf("\n");
        }
    }
    
    ast_Cleanup(expr1);
    
    /* Test case 2: RHS equation */
    printf("\n=== Test 2: Y2 = 100-50y-25y^2 ===\n");
    pcas_ast_t *expr2 = parse_from_string("100-50*Y-25*Y^2", &err);
    if (expr2 == NULL) {
        printf("Parse error: %s\n", error_text[err]);
        return 1;
    }
    
    simplify(expr2, SIMP_NORMALIZE | SIMP_COMMUTATIVE | SIMP_RATIONAL);
    
    printf("Expression parsed and simplified\n");
    printf("AST type: %d\n", expr2->type);
    if (expr2->type == NODE_OPERATOR) {
        printf("Operator type: %d (0=ADD, 1=MULT, etc)\n", expr2->op.operator.type);
        printf("Number of children: %u\n", ast_ChildLength(expr2));
        
        for (unsigned i = 0; i < ast_ChildLength(expr2); i++) {
            pcas_ast_t *child = ast_ChildGet(expr2, i);
            printf("  Child %u: type=%d", i, child->type);
            if (child->type == NODE_NUMBER) {
                char *numstr = num_ToString(child->op.num, 10);
                printf(" (number: %s)", numstr);
                free(numstr);
            } else if (child->type == NODE_OPERATOR) {
                printf(" (operator: %d, %u children)", child->op.operator.type, ast_ChildLength(child));
                
                /* Print grandchildren */
                for (unsigned j = 0; j < ast_ChildLength(child); j++) {
                    pcas_ast_t *gchild = ast_ChildGet(child, j);
                    printf("\n    Grandchild %u: type=%d", j, gchild->type);
                    if (gchild->type == NODE_NUMBER) {
                        char *numstr = num_ToString(gchild->op.num, 10);
                        printf(" (number: %s)", numstr);
                        free(numstr);
                    } else if (gchild->type == NODE_SYMBOL) {
                        printf(" (symbol: %c)", gchild->op.symbol);
                    }
                }
            } else if (child->type == NODE_SYMBOL) {
                printf(" (symbol: %c)", child->op.symbol);
            }
            printf("\n");
        }
    }
    
    ast_Cleanup(expr2);
    
    /* Test case 3: Combined equation Y1 - Y2 = 0 */
    printf("\n=== Test 3: Combined Y1 + (-1)*Y2 ===\n");
    pcas_ast_t *lhs = parse_from_string("9*X^2-54*X-19", &err);
    pcas_ast_t *rhs = parse_from_string("100-50*Y-25*Y^2", &err);
    
    if (lhs && rhs) {
        simplify(lhs, SIMP_NORMALIZE | SIMP_COMMUTATIVE | SIMP_RATIONAL);
        simplify(rhs, SIMP_NORMALIZE | SIMP_COMMUTATIVE | SIMP_RATIONAL);
        
        pcas_ast_t *neg_rhs = ast_MakeBinary(OP_MULT, ast_MakeNumber(num_FromInt(-1)), rhs);
        pcas_ast_t *full_eq = ast_MakeBinary(OP_ADD, lhs, neg_rhs);
        
        simplify(full_eq, SIMP_NORMALIZE | SIMP_COMMUTATIVE | SIMP_RATIONAL);
        
        printf("Combined equation simplified\n");
        printf("AST type: %d\n", full_eq->type);
        if (full_eq->type == NODE_OPERATOR) {
            printf("Operator type: %d (0=ADD, 1=MULT, etc)\n", full_eq->op.operator.type);
            printf("Number of children: %u\n", ast_ChildLength(full_eq));
            
            for (unsigned i = 0; i < ast_ChildLength(full_eq); i++) {
                pcas_ast_t *child = ast_ChildGet(full_eq, i);
                printf("  Child %u: type=%d", i, child->type);
                if (child->type == NODE_NUMBER) {
                    char *numstr = num_ToString(child->op.num, 10);
                    printf(" (number: %s)", numstr);
                    free(numstr);
                } else if (child->type == NODE_OPERATOR) {
                    printf(" (operator: %d)", child->op.operator.type);
                } else if (child->type == NODE_SYMBOL) {
                    printf(" (symbol: %c)", child->op.symbol);
                }
                printf("\n");
            }
        }
        
        ast_Cleanup(full_eq);
    }
    
    printf("\n=== Done ===\n");
    return 0;
}
