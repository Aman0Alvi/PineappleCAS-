#!/usr/bin/env python3
"""
Simulation of the fixed coefficient extraction.

The key insight: When we build the full_equation AST as:
  OP_ADD(expression, OP_MULT(NUMBER(-1), rhs_expression))
  
And THEN simplify it all together, the simplification should 
properly distribute the -1 through all terms in rhs_expression.

For Example 2:
  Y1 = 9*x^2 - 54*x - 19
  Y2 = 100 - 50*y - 25*y^2
  
  full_equation = Y1 + (-1)*Y2
                = (9*x^2 - 54*x - 19) + (-1)*(100 - 50*y - 25*y^2)
                = (9*x^2 - 54*x - 19) + (-100 + 50*y + 25*y^2)  [after distributing -1]
                
  After SIMP_EVAL | SIMP_LIKE_TERMS:
                = 9*x^2 - 54*x + 50*y + 25*y^2 + (-19 - 100)
                = 9*x^2 - 54*x + 50*y + 25*y^2 - 119
                = 9*x^2 + 25*y^2 - 54*x + 50*y - 119
"""

print("=" * 70)
print("TESTING FIX FOR CONIC SECTION FORMULA FORM")
print("=" * 70)

print("\nExample 2: 9x² - 54x - 19 = 100 - 50y - 25y²")
print("\nBefore fix:")
print("  Y3 formula showed: (x-3)²/6793.333 + (y+1)²/2445.6")
print("  (These were completely wrong!)")

print("\nAfter fix:")
print("  Expected: (x-3)²/25 + (y+1)²/9 = 1")

print("\n" + "=" * 70)
print("ANALYSIS OF THE FIX")
print("=" * 70)

print("""
The problem was in gui.c execute_conic() function:

OLD CODE (WRONG):
  1. Parse and simplify Y1 separately
  2. Parse and simplify Y2 separately
  3. Create full_equation = Y1 + (-1)*Y2_simplified
  4. Simplify the full_equation
  
  Issue: Y1 and Y2 are simplified BEFORE combination,
  so when we multiply Y2 by -1, the simplifier might not
  properly distribute the negation across all terms.

NEW CODE (CORRECT):
  1. Parse Y1 (don't simplify yet)
  2. Parse Y2 (don't simplify yet)
  3. Create full_equation = Y1 + (-1)*Y2
  4. Simplify the ENTIRE full_equation at once
  
  This way, the simplifier sees the full structure and can
  properly distribute the -1 through all terms in Y2.
""")

print("=" * 70)
print("MATHEMATICAL VERIFICATION")
print("=" * 70)

A = 9
C = 25
D = -54
E = 50
F = -119

print(f"\nAfter simplification, extracted coefficients should be:")
print(f"  A = {A} (coefficient of x²)")
print(f"  C = {C} (coefficient of y²)")
print(f"  D = {D} (coefficient of x)")
print(f"  E = {E} (coefficient of y)")
print(f"  F = {F} (constant term)")

h = -D / (2*A)
k = -E / (2*C)
print(f"\nCenter: ({h}, {k})")

rhs_adj = -F + A*h**2 + C*k**2
a_sq = rhs_adj / A
b_sq = rhs_adj / C

print(f"\nRHS adjustment: {rhs_adj}")
print(f"a² = {a_sq}")
print(f"b² = {b_sq}")

print(f"\n✓ Expected Y3 formula:")
print(f"  (x-3)²/{int(a_sq)} + (y+1)²/{int(b_sq)} = 1")
print(f"  (Both numerators and denominators correct!)")
