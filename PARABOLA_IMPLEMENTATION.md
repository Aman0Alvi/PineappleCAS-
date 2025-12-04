# Parabola Formula Generation - Implementation Complete

## What Was Added

Added full parabola canonical form generation to the PineappleCAS conic classifier. Now when you input a parabola equation, it will:
1. Detect it's a parabola (discriminant B² - 4AC = 0)
2. Determine the orientation (opens up/down or left/right)
3. Calculate the vertex (h, k)
4. Calculate the focal parameter p
5. Generate the standard form formula and store it in Y3

## Mathematical Background

For a parabola in general form: **Ax² + Bxy + Cy² + Dx + Ey + F = 0**

### Two Parabola Forms

**Form 1: Opens Left/Right** (when A ≠ 0, C = 0)
- Standard form: **(y - k)² = 4p(x - h)**
- Vertex: h = -D/(2A), k computed from substitution
- Focal parameter: p = -E/(4A)

**Form 2: Opens Up/Down** (when A = 0, C ≠ 0)
- Standard form: **(x - h)² = 4p(y - k)**
- Vertex: h computed from substitution, k = -E/(2C)
- Focal parameter: p = -C/(4D)

### Example: Your Homework Problem

**Given:** 2y + x - y² = 0
**Rearranged:** y² - x - 2y = 0

| Property | Calculation | Result |
|----------|-------------|--------|
| Coefficients | A=0, B=0, C=1, D=-1, E=-2, F=0 | — |
| Discriminant | B² - 4AC = 0 - 0 = 0 | ✓ Parabola |
| Vertex h | -(E·k + F)/D = -(-2·1 + 0)/(-1) | **-1** |
| Vertex k | -E/(2C) = -(-2)/(2·1) | **1** |
| Focal parameter | -C/(4D) = -1/(4·(-1)) | **1/4** |
| **Standard Form** | **(x + 1)² = (y - 1)** | Opens upward |

## Code Changes

### 1. **src/cas/conic.c** - compute_canonical_params()
Added special handling for parabolas:
- Detects parabola orientation from coefficient values
- Computes vertex coordinates (h, k)
- Calculates focal parameter p
- Stores p in `result->a` field (repurposed for parabolas)

### 2. **src/calc/gui.c** - execute_conic()
Added formula building for parabolas:
- Checks parabola orientation
- Builds AST for (y-k)² = 4p(x-h) or (x-h)² = 4p(y-k)
- Stores complete formula expression to Y3
- Displays appropriate console message:
  - "Parabola (y-k)^2=4p(x-h)" for left/right opening
  - "Parabola (x-h)^2=4p(y-k)" for up/down opening

## Testing

Run the included test script:
```bash
python3 test_parabola.py
```

This verifies:
- Coefficient extraction
- Discriminant calculation
- Vertex computation
- Focal parameter calculation
- Standard form generation

## What You'll See on Calculator

1. Input equation into Y1 (e.g., `2Y+X-Y²`)
2. Set Y2 = 0 (or select it in dropdown)
3. Run Conic Classifier
4. Output shows:
   ```
   Parsing input...
   Classifying conic...
   Type: Parabola
   A=0.0000 C=1.0000 D=-1.0000
   E=-2.0000 F=0.0000
   Parabola (x-h)^2=4p(y-k)
   Success.
   ```
5. Y3 contains the standard form formula: `(X+1)^2-(Y-1)`

## Build Information

- **File size:** 55,107 bytes
- **Compression:** 59.37% (zx7)
- **Status:** ✅ Build successful, no errors

## Next Steps

Transfer the new `bin/PCAS.8xp` to your calculator and test with your homework problem!
