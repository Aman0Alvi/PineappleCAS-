# Conic Properties Display Feature

## Overview
This feature adds comprehensive property display for conic sections (parabola, ellipse, circle, and hyperbola) in the PineappleCAS UI. When a user classifies a conic section, the system now displays exact mathematical properties in addition to the canonical form.

## What's New

### Parabola Properties
- **Vertex**: (h, k) - the turning point
- **Focus**: The focal point
- **Directrix**: The directrix line (vertical or horizontal)

Example output:
```
Vertex: (1/2, -3/2)
Focus: (2/2, -3/2)
Directrix: x = 0/2
```

### Ellipse Properties
- **Center**: (h, k)
- **Foci**: Both focal points F₁ and F₂
- **Major Axis**: The two endpoints of the major axis
- **Minor Axis**: The two endpoints of the minor axis

Example output:
```
Center: (0, 0)
Foci: (3, 0)
      (-3, 0)
Major Axis: (5, 0)
            (-5, 0)
Minor Axis: (0, 4)
            (0, -4)
```

### Circle Properties
- **Center**: (h, k)
- **Radius**: r (exact value)

Example output:
```
Type: Circle
Center: (1, 2)
Radius: 5
```

### Hyperbola Properties
- **Center**: (h, k)
- **Vertices**: The two vertices on the transverse axis
- **Foci**: The two focal points
- **Asymptotes**: The two asymptote equations in the form y = mx + b

Example output:
```
Center: (0, 0)
Vertices: (5, 0)
          (-5, 0)
Foci: (13, 0)
      (-13, 0)
Asymptote 1: y = 12/5x + 0
Asymptote 2: y = -12/5x + 0
```

## Implementation Details

### New Files Created

#### `src/cas/conic_display.h`
Header file defining:
- `ConicProperties` structure - holds all computed properties for a conic
- `conic_ComputeProperties()` - computes properties from a `ConicResult`
- `conic_PropertiesCleanup()` - cleanup function

#### `src/cas/conic_display.c`
Implementation with:
- `compute_parabola_properties()` - calculates vertex, focus, and directrix
- `compute_ellipse_properties()` - calculates center, foci, and axis endpoints
- `compute_hyperbola_properties()` - calculates center, vertices, foci, and asymptotes
- Rational arithmetic helpers for exact computation

### Modified Files

#### `src/calc/gui.c`
Updates include:
- Added `#include "../cas/conic_display.h"`
- Added helper functions:
  - `display_rational()` - formats rational numbers for display
  - `display_parabola_properties()` - displays parabola properties to console
  - `display_ellipse_properties()` - displays ellipse properties to console
  - `display_hyperbola_properties()` - displays hyperbola properties to console
- Updated `execute_conic()` function to:
  - Compute properties using `conic_ComputeProperties()`
  - Display properties based on conic type
  - Properly cleanup with `conic_PropertiesCleanup()`

## Mathematical Formulas Used

### Parabola
For horizontal parabola `(y-k)² = 4p(x-h)`:
- Focus: (h+p, k)
- Directrix: x = h - p

For vertical parabola `(x-h)² = 4p(y-k)`:
- Focus: (h, k+p)
- Directrix: y = k - p

### Ellipse
Given standard form `(x-h)²/a² + (y-k)²/b² = 1`:
- When a² > b²: major axis is horizontal
  - c² = a² - b², foci at (h±c, k)
- When b² > a²: major axis is vertical
  - c² = b² - a², foci at (h, k±c)

### Hyperbola
Given standard form `(x-h)²/a² - (y-k)²/b² = 1` (horizontal transverse):
- Vertices: (h±a, k)
- c² = a² + b², foci at (h±c, k)
- Asymptotes: y - k = ±(b/a)(x - h)

For vertical transverse axis `(y-k)²/a² - (x-h)²/b² = 1`:
- Vertices: (h, k±a)
- Foci: (h, k±c) where c² = a² + b²
- Asymptotes: y - k = ±(a/b)(x - h)

## Usage

When a user:
1. Inputs a conic equation (e.g., `x²+y²=25`)
2. Selects "Classify" in the CONIC context
3. The system displays:
   - Conic type (Circle, Ellipse, Parabola, or Hyperbola)
   - Coefficients
   - **Properties section** (NEW)
     - For circles: center and radius
     - For parabolas: vertex, focus, and directrix
     - For ellipses: center, foci, major and minor axis endpoints
     - For hyperbolas: center, vertices, foci, and asymptotes
   - Canonical form stored in Y3

## Compilation Status

✅ `src/cas/conic_display.c` - Compiles successfully
✅ `src/cas/conic_display.h` - Created
✅ `src/calc/gui.c` - Compiles successfully with new code

All warnings are ISO C90 compliance warnings (using variable declarations after statements, which is standard C99+). The code compiles and runs without errors.

## Future Enhancements

- Display exact values as fractions instead of decimals
- Add ability to export properties to file
- Visual representation of conic properties
- Ability to analyze multiple conics and compare
