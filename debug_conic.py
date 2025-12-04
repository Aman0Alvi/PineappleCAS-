#!/usr/bin/env python3
"""
Debug test to understand what coefficients should be extracted.

Y1 = 9x^2 - 54x - 19
Y2 = 100 - 50y - 25y^2

The calculator combines them as: LHS - RHS = 0
(9x^2 - 54x - 19) - (100 - 50y - 25y^2) = 0
9x^2 - 54x - 19 - 100 + 50y + 25y^2 = 0
9x^2 + 25y^2 - 54x + 50y + (-19 - 100) = 0
9x^2 + 25y^2 - 54x + 50y - 119 = 0

So the extracted coefficients should be:
A = 9 (coefficient of x^2)
B = 0 (coefficient of xy)
C = 25 (coefficient of y^2)
D = -54 (coefficient of x)
E = 50 (coefficient of y)
F = -119 (constant term)

But the calculator is showing weird denominators like 6793.333333
which equals 20380/3 or something similar.

Let's see if there's a computational issue...
"""

# Completed square form:
A = 9
C = 25
D = -54
E = 50
F = -119

h = -D / (2 * A)
k = -E / (2 * C)

print(f"Center: ({h}, {k})")

# After completing the square:
# A(x-h)^2 + C(y-k)^2 = rhs_adj
rhs_adj = -F + A * h**2 + C * k**2
print(f"rhs_adj = {rhs_adj}")

a_squared = rhs_adj / A
b_squared = rhs_adj / C

print(f"a^2 = {a_squared}")
print(f"b^2 = {b_squared}")

print("\nExpected Y3 formula:")
print(f"(x-3)^2/{a_squared} + (y+1)^2/{b_squared} = 1")
print(f"Which simplifies to: (x-3)^2/25 + (y+1)^2/9 = 1")

print("\nWhat we're actually getting:")
print("(x-3)^2/6793.333333 + (y+1)^2/2445.600000")

print("\nLet's figure out what values would give us those denominators...")
mystery_a2 = 6793.333333
mystery_b2 = 2445.600000

print(f"\nIf a^2 = {mystery_a2}, then a^2 * A should give us something...")
print(f"{mystery_a2} * 9 = {mystery_a2 * 9}")
print(f"Hmm, that's not obviously wrong...")

# Wait, maybe the issue is in the calculation of rhs_adj?
# Let me check if F is being computed differently

# What if F is the ORIGINAL F before adjustment?
# Like if the code is extracting from the simplified full_equation
# but the F includes weird intermediate values?

# Actually, looking at the huge numbers, let me check if there's 
# a precision loss or floating point issue...

print(f"\n6793.333333 * 3 = {6793.333333 * 3}  (should be integer if it's a fraction)")
print(f"2445.6 * 5 = {2445.6 * 5}  (should be integer if it's a fraction)")

# Maybe these are decimal approximations of fractions with huge numerators?
print(f"\nTrying to find the fraction...")
from fractions import Fraction

frac_a = Fraction(6793.333333).limit_denominator(1000)
frac_b = Fraction(2445.600000).limit_denominator(1000)

print(f"a^2 as fraction: {frac_a}")
print(f"b^2 as fraction: {frac_b}")
