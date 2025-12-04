# Conic Section Formula Form Fix - Final Summary

## Problem
The calculator was outputting formulas with completely wrong denominators:
- **Observed:** `(x-3)²/6793.333... + (y+1)²/2445.6...`
- **Expected:** `(x-3)²/25 + (y+1)²/9 = 1`

## Root Cause
The issue was in `src/calc/gui.c` in the `execute_conic()` function.

**Wrong approach:**
1. Parse and simplify Y1 separately → `9x² - 54x - 19`
2. Parse and simplify Y2 separately → `100 - 50y - 25y²`
3. Create AST: `LHS + (-1)*RHS_simplified`
4. Simplify the combined equation

**Problem:** When Y1 and Y2 were simplified separately before combining, the multiplication by -1 and subsequent simplification didn't properly distribute the negation through all terms in the simplified Y2 expression. This caused the coefficient extraction to extract incorrect values.

**Correct approach:**
1. Parse Y1 (no premature simplification)
2. Parse Y2 (no premature simplification)  
3. Create AST: `LHS + (-1)*RHS` with raw parsed expressions
4. Simplify the ENTIRE combined equation at once

This allows the simplifier to see the full structure and properly distribute the -1 through all terms, then combine like terms correctly.

## Changes Made

### 1. `/workspaces/PineappleCAS-/src/calc/gui.c` - `execute_conic()` function
**Lines 1115-1156:** Restructured to:
- Parse both Y1 and Y2 without pre-simplification
- Build the full equation AST first: `Y1 + (-1)*Y2`
- Simplify the complete equation all at once
- Pass `rhs_value = 0` to `conic_Classify()` since RHS is already in the equation

### 2. `/workspaces/PineappleCAS-/src/cas/conic.c` - `conic_Classify()` function
**Lines 419-470:** Added debug output to console to show extracted coefficients:
```c
[CONIC DEBUG] Extracted: A=9, C=25, D=-54, E=50, F=-119
```

This helps verify that correct coefficients are being extracted.

## Verification

For the test case: `9x² - 54x - 19 = 100 - 50y - 25y²`

**Expected results after fix:**
- Extracted coefficients: A=9, C=25, D=-54, E=50, F=-119
- Center: (3, -1)
- RHS adjustment: 225
- a² = 25, b² = 9
- Y3 formula: `(x-3)²/25 + (y+1)²/9 = 1` ✓

## Build Output
Successfully built on 2025-12-04:
```
[success] bin/PCAS.8xp, 54876 bytes. (zx7 compressed 59.08%)
```

## How to Test
1. Transfer the new PCAS.8xp to your calculator
2. Input Y1 = `9X^2-54X-19`
3. Input Y2 = `100-50Y-25Y^2`
4. Run the Conic function
5. Check Y3 - should show `(x-3)²/25 + (y+1)²/9 = 1`
6. Console output should show: `[CONIC DEBUG] Extracted: A=9, C=25, D=-54, E=50, F=-119`
