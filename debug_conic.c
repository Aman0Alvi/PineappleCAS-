#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* We'll simulate the conic calculation manually to debug */

int main() {
    printf("=== Conic Calculation Debug for Example 2 ===\n\n");
    
    /* Original equation: 9x^2 - 54x - 19 = 100 - 50y - 25y^2
     * Rearrange to LHS = 0: 9x^2 - 54x - 19 - 100 + 50y + 25y^2 = 0
     * Simplify: 9x^2 - 54x + 50y + 25y^2 - 119 = 0
     * 
     * In form: Ax^2 + Cy^2 + Dx + Ey + F = 0
     * A = 9
     * C = 25 (positive, not negative!)
     * D = -54
     * E = 50
     * F = -119
     */
    
    double A = 9.0;
    double C = 25.0;  /* IMPORTANT: C is POSITIVE */
    double D = -54.0;
    double E = 50.0;
    double F = -119.0;
    
    printf("Coefficients extracted from: 9x^2 - 54x + 50y + 25y^2 - 119 = 0\n");
    printf("A = %.1f\n", A);
    printf("C = %.1f\n", C);
    printf("D = %.1f\n", D);
    printf("E = %.1f\n", E);
    printf("F = %.1f\n\n", F);
    
    /* Complete the square */
    double h = -D / (2.0 * A);
    double k = -E / (2.0 * C);
    
    printf("Center coordinates:\n");
    printf("h = -D/(2A) = -(-54)/(2*9) = 54/18 = %.1f\n", h);
    printf("k = -E/(2C) = -(50)/(2*25) = -50/50 = %.1f\n\n", k);
    
    /* After completing the square:
     * A(x-h)^2 + C(y-k)^2 = -F + A*h^2 + C*k^2
     * 
     * rhs_adj = -F + A*h^2 + C*k^2
     */
    
    double rhs_adj = -F + A * h * h + C * k * k;
    
    printf("RHS after completing the square:\n");
    printf("rhs_adj = -F + A*h^2 + C*k^2\n");
    printf("        = -(-119) + 9*(3)^2 + 25*(-1)^2\n");
    printf("        = 119 + 9*9 + 25*1\n");
    printf("        = 119 + 81 + 25\n");
    printf("        = %.1f\n\n", rhs_adj);
    
    /* So we have: 9(x-3)^2 + 25(y+1)^2 = 225
     * Divide by 225: (x-3)^2/25 + (y+1)^2/9 = 1
     */
    
    double a_squared = rhs_adj / A;
    double b_squared = rhs_adj / C;
    
    printf("Standard form denominators:\n");
    printf("a^2 = rhs_adj / A = 225 / 9 = %.1f\n", a_squared);
    printf("b^2 = rhs_adj / C = 225 / 25 = %.1f\n\n", b_squared);
    
    printf("CORRECT ANSWER:\n");
    printf("Standard form: (x-3)^2/25 + (y+1)^2/9 = 1\n");
    printf("a^2 = 25, b^2 = 9\n");
    printf("Type: Ellipse\n\n");
    
    printf("ISSUE FOUND:\n");
    printf("The problem is that the code is treating the RHS value incorrectly.\n");
    printf("The user input shows Y2 = 100 - 50y - 25y^2\n");
    printf("This means the equation should be treated as:\n");
    printf("LHS = Y1 = 9x^2 - 54x - 19\n");
    printf("RHS = Y2 = 100 - 50y - 25y^2\n");
    printf("\n");
    printf("When we compute LHS - RHS = 0:\n");
    printf("(9x^2 - 54x - 19) - (100 - 50y - 25y^2) = 0\n");
    printf("9x^2 - 54x - 19 - 100 + 50y + 25y^2 = 0\n");
    printf("9x^2 + 25y^2 - 54x + 50y - 119 = 0\n");
    
    return 0;
}
