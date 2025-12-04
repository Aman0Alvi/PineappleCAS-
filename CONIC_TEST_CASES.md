# Conic Section Classifier - Test Cases for TI-84 Plus CE

## How to Test on Your Calculator

1. **Input the equations** into Y1 and Y2 using the Y= menu
2. **Run the Conic function** from the PineappleCAS menu
3. **Check the output** in Y3 and the console

---

## Test Case 1: Example 2 Ellipse (THE ONE YOU TESTED)
**Status:** ✓ VERIFIED WORKING

### Input:
- **Y1:** `9X^2-54X-19`
- **Y2:** `100-50Y-25Y^2`

### Expected Output:
- **Type:** Ellipse
- **Y3 Formula:** `(x-3)²/25 + (y+1)²/9 = 1`
- **Center:** (3, -1)
- **Denominators:** 25 and 9 (NOT weird decimals!)

---

## Test Case 2: Simple Circle
**Tests:** Basic circle classification, equal coefficients

### Input:
- **Y1:** `X^2+Y^2-2X-4Y`
- **Y2:** `0`

### Expected Output:
- **Type:** Circle
- **Y3 Formula:** `(x-1)² + (y-2)² = 5`
- **Center:** (1, 2)
- **Radius²:** 5

### Why This Test:
- Tests that A = C = 1 correctly identifies a circle
- Tests simple center translation
- No RHS value (equals 0)

---

## Test Case 3: Hyperbola
**Tests:** Mixed-sign coefficients, absolute value handling

### Input:
- **Y1:** `X^2-Y^2-1`
- **Y2:** `0`

### Expected Output:
- **Type:** Hyperbola
- **Y3 Formula:** `x²/1 - y²/1 = 1`
- **Center:** (0, 0)
- **Denominators:** 1 and 1

### Why This Test:
- Tests hyperbola detection (B²-4AC > 0)
- Tests handling of negative C coefficient
- Tests that absolute values are used correctly

---

## Test Case 4: Translated Ellipse with Fractions
**Tests:** Larger coefficients, fractional results

### Input:
- **Y1:** `4X^2+9Y^2-16X+54Y+61`
- **Y2:** `0`

### Expected Output:
- **Type:** Ellipse
- **Y3 Formula:** `(x-2)²/9 + (y+3)²/4 = 1`
- **Center:** (2, -3)
- **Denominators:** 9 and 4

### Why This Test:
- Tests larger, non-unit coefficients
- Tests negative center y-coordinate
- Ensures fractions display correctly (9 and 4, not decimals)

---

## Test Case 5: Circle with Large Radius
**Tests:** Perfect square recognition, large coefficients

### Input:
- **Y1:** `X^2-6X+Y^2-8Y+21`
- **Y2:** `0`

### Expected Output:
- **Type:** Circle
- **Y3 Formula:** `(x-3)² + (y-4)² = 4`
- **Center:** (3, 4)
- **Radius²:** 4

### Why This Test:
- Tests perfect square detection
- Tests formula: (x-h)² + (y-k)² = r²
- Tests that coefficients work with completion of square

---

## Test Case 6: Parabola (BONUS - If Implemented)
**Status:** Currently outputs "Parabola: (y-k)²=4p(x-h)" as placeholder

### Input:
- **Y1:** `Y^2-4X`
- **Y2:** `0`

### Expected Output (if parabola is implemented):
- **Type:** Parabola
- **Vertex:** (0, 0)

### Notes:
- Parabola support in formula form is a TODO item
- Current implementation just displays the generic form

---

## Manual Verification Steps

After each test:

1. **Check Y3** - Look at the formula displayed
   - Verify numerators are correct: (x-h)², (y-k)²
   - Verify denominators are FRACTIONS, not decimals
   - Example: Should see `25` not `25.0` or `24.999999`

2. **Check Console Output** - Should show:
   - `Type: [Conic Type]`
   - `A=[value] C=[value] D=[value]`
   - `E=[value] F=[value]`

3. **Verify Math** - Use the center and denominators to confirm:
   - Center: (h, k) = (-D/(2A), -E/(2C))
   - Verify by hand that completing the square gives the right RHS

---

## What Makes This Fix Important

The previous version showed denominators like:
- `6793.333333` instead of `25`
- `2445.600000` instead of `9`

This fix ensures:
- ✓ Proper equation combination (Y1 - Y2 = 0)
- ✓ Correct coefficient extraction
- ✓ Accurate center calculation
- ✓ Proper absolute value handling for mixed-sign conics
- ✓ Clean fraction display (not decimal approximations)

---

## Quick Reference: Expected Values by Type

| Type | Condition | Formula |
|------|-----------|---------|
| Circle | A = C, B = 0 | (x-h)² + (y-k)² = r² |
| Ellipse | B² - 4AC < 0 | (x-h)²/a² + (y-k)²/b² = 1 |
| Parabola | B² - 4AC = 0 | (y-k)² = 4p(x-h) or (x-h)² = 4p(y-k) |
| Hyperbola | B² - 4AC > 0 | (x-h)²/a² - (y-k)²/b² = 1 |
