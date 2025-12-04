# Parabola Test Cases for Calculator

## Test 1: Parabola Opening Upward (Your Example)

**Equation:** `2Y + X - Y² = 0`

### Setup
- Y1: `2Y + X - Y²`
- Y2: `0`

### Expected Output
```
Type: Parabola
A=0.0000 C=1.0000 D=-1.0000
E=-2.0000 F=0.0000
Parabola (x-h)^2=4p(y-k)
Success.
```

### Y3 Formula
`(X+1)²-(Y-1)` 
which equals 0 in standard form

### Vertex
- h = -1
- k = 1
- p = 1/4
- **Standard form: (x + 1)² = (y - 1)**

---

## Test 2: Parabola Opening Downward

**Equation:** `Y² - X + 4Y + 3 = 0`

### Setup
- Y1: `Y² - X + 4Y + 3`
- Y2: `0`

### Vertex Calculation
- Coefficients: A=0, C=1, D=-1, E=4, F=3
- k = -E/(2C) = -4/2 = -2
- h = -(E·k + F)/D = -(4·(-2) + 3)/(-1) = -(-8+3)/(-1) = -(-5)/(-1) = -5
- p = -C/(4D) = -1/(4·(-1)) = 1/4

### Expected Output
```
Type: Parabola
A=0.0000 C=1.0000 D=-1.0000
E=4.0000 F=3.0000
Parabola (x-h)^2=4p(y-k)
Success.
```

### Y3 Formula
`(X+5)²-(Y+2)`

### Standard Form
**(x + 5)² = (y + 2)** (opens upward)

---

## Test 3: Parabola Opening Right

**Equation:** `Y² - 4X + 2Y + 5 = 0`

### Setup
- Y1: `Y² - 4X + 2Y + 5`
- Y2: `0`

### Vertex Calculation
- Coefficients: A=0, C=1, D=-4, E=2, F=5
- k = -E/(2C) = -2/2 = -1
- h = -(E·k + F)/D = -(2·(-1) + 5)/(-4) = -(-2+5)/(-4) = -(3)/(-4) = 3/4
- p = -C/(4D) = -1/(4·(-4)) = 1/16

### Expected Output
```
Type: Parabola
A=0.0000 C=1.0000 D=-4.0000
E=2.0000 F=5.0000
Parabola (x-h)^2=4p(y-k)
Success.
```

### Y3 Formula
`(X-3/4)² - (Y+1)`

### Standard Form
**(x - 3/4)² = 1/4(y + 1)** (opens upward)

---

## Test 4: Parabola Opening Left

**Equation:** `4Y² - X + 8Y + 3 = 0`

Rearranged: `X = 4Y² + 8Y + 3`

### Setup
- Y1: `4Y² - X + 8Y + 3`
- Y2: `0`

### Vertex Calculation
- Coefficients: A=0, B=0, C=4, D=-1, E=8, F=3
- k = -E/(2C) = -8/8 = -1
- h = -(E·k + F)/D = -(8·(-1) + 3)/(-1) = -(-8+3)/(-1) = -(-5)/(-1) = -5
- p = -C/(4D) = -4/(4·(-1)) = 1

### Expected Output
```
Type: Parabola
A=0.0000 C=4.0000 D=-1.0000
E=8.0000 F=3.0000
Parabola (x-h)^2=4p(y-k)
Success.
```

### Standard Form
**(x + 5)² = 4(y + 1)** (opens upward)

---

## Verification

After testing each case on your calculator:
1. Check the conic type is correctly identified as "Parabola"
2. Verify the coefficients match the expected values (with small rounding)
3. Confirm Y3 contains the standard form formula
4. Check that the formula simplifies correctly
5. Graph Y3 to visually verify the parabola shape

All coefficients should match to 4 decimal places, confirming correct coefficient extraction and mathematical computation.
