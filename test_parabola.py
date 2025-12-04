#!/usr/bin/env python3
"""
Test parabola coefficient extraction and canonical form
Example 4 from your homework: 2y + x - y^2 = 0
Standard form: y^2 - x - 2y = 0  =>  (y-1)^2 = x + 1  =>  (y-1)^2 = 1(x - (-1))
So vertex (h, k) = (-1, 1), 4p = 1, p = 1/4
"""

import math
from fractions import Fraction

def test_parabola_example_4():
    """Test parabola: 2y + x - y^2 = 0"""
    print("=" * 70)
    print("PARABOLA TEST: Example 4")
    print("=" * 70)
    print()
    print("Given equation: 2y + x - y^2 = 0")
    print("Rearranged:   -y^2 + x + 2y = 0")
    print("Or:           y^2 - x - 2y = 0")
    print()
    
    # Extract coefficients from y^2 - x - 2y = 0
    # General form: Ax^2 + Bxy + Cy^2 + Dx + Ey + F = 0
    # Here: 0*x^2 + 0*xy + 1*y^2 + (-1)*x + (-2)*y + 0 = 0
    
    A = Fraction(0)
    B = Fraction(0)
    C = Fraction(1)
    D = Fraction(-1)
    E = Fraction(-2)
    F = Fraction(0)
    
    print(f"Coefficients:")
    print(f"  A = {A}, B = {B}, C = {C}")
    print(f"  D = {D}, E = {E}, F = {F}")
    print()
    
    # Verify parabola: B^2 - 4AC = 0
    discriminant = B*B - 4*A*C
    print(f"Discriminant: B^2 - 4AC = {B}^2 - 4*{A}*{C} = {discriminant}")
    print(f"Result: {'PARABOLA ✓' if discriminant == 0 else 'NOT A PARABOLA ✗'}")
    print()
    
    # Parabola form: (x-h)^2 = 4p(y-k)  [opens up/down, since C != 0, A = 0]
    # From: Cy^2 + Dx + Ey + F = 0
    # Complete the square: C(y + E/2C)^2 + Dx + F - C(E/2C)^2 = 0
    
    # Vertex: h = 0 (if D=0) or computed from D; k = -E/(2C)
    
    if D != 0:
        # Need to solve for x when y = k
        # D*x = -C*k^2 - E*k - F => x = (-C*k^2 - E*k - F)/D
        pass
    
    # k = -E/(2C)
    k = -E / (2*C)
    print(f"Vertex k-coordinate: k = -E/(2C) = -({E})/(2*{C}) = {k}")
    
    # At vertex, substitute y = k into Cy^2 + Dx + Ey + F = 0
    # C*k^2 + D*x + E*k + F = 0
    # D*x = -C*k^2 - E*k - F
    if D != 0:
        h = -(C*k*k + E*k + F) / D
        print(f"Vertex h-coordinate: h = {h}")
    else:
        h = Fraction(0)
        print(f"Vertex h-coordinate: h = {h} (D=0)")
    
    print()
    print(f"Vertex: ({h}, {k})")
    print()
    
    # Focal parameter p: (x-h)^2 = 4p(y-k)
    # From Cy^2 + Dx + Ey + F = 0
    # We need: 4p = -C/D
    if D != 0:
        p = -C / (4*D)
        print(f"Focal parameter: p = -C/(4D) = -{C}/(4*{D}) = {p}")
        print(f"Standard form: (x - ({h}))^2 = 4*({p})*(y - ({k}))")
        print(f"Simplified:   (x + {-h})^2 = {4*p}*(y - {k})")
    else:
        print("Cannot compute focal parameter (D = 0)")
    
    print()
    print("-" * 70)
    print()

def test_parabola_rightward():
    """Test parabola opening to the right: y^2 - 4x + 2y + 5 = 0"""
    print("=" * 70)
    print("PARABOLA TEST: Opens Right (y-k)^2 = 4p(x-h)")
    print("=" * 70)
    print()
    print("Given equation: y^2 - 4x + 2y + 5 = 0")
    print()
    
    # Coefficients: 0*x^2 + 0*xy + 1*y^2 + (-4)*x + 2*y + 5 = 0
    A = Fraction(0)
    B = Fraction(0)
    C = Fraction(1)
    D = Fraction(-4)
    E = Fraction(2)
    F = Fraction(5)
    
    print(f"Coefficients:")
    print(f"  A = {A}, B = {B}, C = {C}")
    print(f"  D = {D}, E = {E}, F = {F}")
    print()
    
    # Verify parabola: B^2 - 4AC = 0
    discriminant = B*B - 4*A*C
    print(f"Discriminant: B^2 - 4AC = {discriminant}")
    print(f"Result: {'PARABOLA ✓' if discriminant == 0 else 'NOT A PARABOLA ✗'}")
    print()
    
    # Since A=0 and C!=0, form is (x-h)^2 = 4p(y-k)
    k = -E / (2*C)
    print(f"Vertex k-coordinate: k = -E/(2C) = -{E}/(2*{C}) = {k}")
    
    # At vertex, y = k:
    # 0*x^2 + D*x + E*k + F = 0 => D*x = -E*k - F => x = (-E*k - F)/D
    if D != 0:
        h = -(E*k + F) / D
        print(f"Vertex h-coordinate: h = -(E*k + F)/D = {h}")
        
        p = -C / (4*D)
        print(f"Focal parameter: p = -C/(4D) = -{C}/(4*{D}) = {p}")
    else:
        h = Fraction(0)
        p = Fraction(0)
        print("Cannot compute focal parameter (D = 0)")
    
    print()
    print(f"Vertex: ({h}, {k})")
    print(f"Standard form: (x - ({h}))^2 = 4*({p})*(y - ({k}))")
    print(f"Simplified:   (x - {h})^2 = {4*p}*(y - {k})")
    print()
    print("-" * 70)
    print()

if __name__ == "__main__":
    test_parabola_example_4()
    test_parabola_rightward()
    print("\nAll tests completed!")
