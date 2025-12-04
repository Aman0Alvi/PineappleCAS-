# Conic Properties Display - Architecture & Integration Guide

## System Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                        User Input                            │
│              (Conic Equation in calculator)                 │
└────────────────────┬────────────────────────────────────────┘
                     │
                     ▼
┌─────────────────────────────────────────────────────────────┐
│                   src/calc/gui.c                            │
│              execute_conic() Function                       │
│  ┌──────────────────────────────────────────────────────┐  │
│  │ 1. Parse & Simplify input equation                  │  │
│  │ 2. Call conic_Classify() [from conic.h]            │  │
│  │ 3. Display classification results                   │  │
│  └──────────────────────────────────────────────────────┘  │
└────────────────────┬────────────────────────────────────────┘
                     │
                     ▼
┌─────────────────────────────────────────────────────────────┐
│         src/cas/conic.h / conic.c                           │
│            ConicResult Structure                            │
│  ┌──────────────────────────────────────────────────────┐  │
│  │ type: PARABOLA, ELLIPSE, CIRCLE, HYPERBOLA         │  │
│  │ A,B,C,D,E,F: equation coefficients                 │  │
│  │ center_h, center_k: center coordinates             │  │
│  │ a, b: semi-axes (for ellipse/hyperbola)           │  │
│  │ c_dist: focal distance                             │  │
│  └──────────────────────────────────────────────────────┘  │
└────────────────────┬────────────────────────────────────────┘
                     │
         ┌───────────┴───────────┐
         │                       │
         ▼                       ▼
    ┌─────────────┐    ┌──────────────────────────────────────┐
    │ Write Y3    │    │ src/calc/gui.c (NEW)                │
    │ (canonical  │    │ conic_ComputeProperties()           │
    │  form)      │    │  ▼                                   │
    └─────────────┘    │ src/cas/conic_display.h/c (NEW)    │
                       │  • compute_parabola_properties()    │
                       │  • compute_ellipse_properties()     │
                       │  • compute_hyperbola_properties()   │
                       │                                     │
                       │ ConicProperties struct:             │
                       │  ┌──────────────────────────────┐   │
                       │  │ center_x, center_y           │   │
                       │  │ focus_x, focus_y             │   │
                       │  │ directrix_value              │   │
                       │  │ foci_x[2], foci_y[2]         │   │
                       │  │ vertices_x[2], vertices_y[2] │   │
                       │  │ asymptote_m, asymptote_b     │   │
                       │  │ ...and more                   │   │
                       │  └──────────────────────────────┘   │
    ┌────────────────────────────────────────────────────────┤
    │                                                         │
    ▼                                                         ▼
┌──────────────────────┐                    ┌────────────────────────────┐
│ Display Functions:   │                    │ Console Output:            │
│ • display_rational() │                    │                            │
│ • display_parabola_  │─────────────────►  │ Type: [Conic Type]         │
│   properties()       │                    │ A=... C=... D=...          │
│ • display_ellipse_   │                    │ E=... F=...                │
│   properties()       │                    │                            │
│ • display_hyperbola_ │                    │ Properties:                │
│   properties()       │                    │ [Type-Specific Details]    │
└──────────────────────┘                    │                            │
                                            │ Success.                   │
                                            └────────────────────────────┘
```

## Data Flow for Parabola Example

```
Input Equation: y² - 4x + 8y + 20 = 0
                │
                ▼
Parse & Simplify
                │
                ▼
conic_Classify()  ──►  ConicResult
                       {
                         type: CONIC_PARABOLA
                         A: 0        (no x² term)
                         C: 1        (y² coefficient)
                         center_h: 0
                         center_k: -4
                         a: 1        (focal parameter p)
                       }
                │
                ▼
conic_ComputeProperties()  ──►  ConicProperties
                                {
                                  center_x: 0
                                  center_y: -4
                                  focus_x: 0
                                  focus_y: -3     (k + p)
                                  directrix_value: -5  (k - p)
                                  directrix_is_vertical: 0
                                }
                │
                ▼
Display:
  Vertex: (0, -4)
  Focus: (0, -3)
  Directrix: y = -5
```

## Function Call Sequence

```
execute_conic()
├─ parse_from_dropdown_index()
├─ simplify()
├─ conic_Classify()
│  └─ Returns: ConicResult *
│
├─ conic_ComputeProperties()
│  │
│  ├─ For PARABOLA:
│  │  └─ compute_parabola_properties()
│  │     ├─ add_rats()
│  │     ├─ sub_rats()
│  │     └─ div_rats()
│  │
│  ├─ For ELLIPSE:
│  │  └─ compute_ellipse_properties()
│  │     ├─ mp_rat_compare()
│  │     ├─ sub_rats()
│  │     ├─ add_rats()
│  │     └─ sqrt_approx()
│  │
│  └─ For HYPERBOLA:
│     └─ compute_hyperbola_properties()
│        ├─ div_rats()
│        ├─ add_rats()
│        ├─ mul_rats()
│        ├─ sub_rats()
│        └─ neg_rat()
│
├─ display_rational()
├─ display_parabola_properties() or
│  display_ellipse_properties() or
│  display_hyperbola_properties()
│
└─ conic_PropertiesCleanup()
```

## Memory Management

```
ConicResult (from conic_Classify)
    ├─ A, B, C, D, E, F: mp_rat (freed by conic_ResultCleanup)
    ├─ discriminant: mp_rat
    ├─ center_h, center_k: mp_rat
    ├─ a, b, c_dist: mp_rat
    └─ canonical_form: pcas_ast_t *

ConicProperties (from conic_ComputeProperties)  
    ├─ center_x, center_y: mp_rat
    ├─ focus_x, focus_y: mp_rat
    ├─ foci_x[2], foci_y[2]: mp_rat
    ├─ vertices_x[2], vertices_y[2]: mp_rat
    ├─ asymptote1_m, asymptote1_b: mp_rat
    ├─ asymptote2_m, asymptote2_b: mp_rat
    └─ ...all freed by conic_PropertiesCleanup()

char buffers (local in display functions)
    ├─ h_str, k_str: char[40]
    ├─ focus_str, directrix_str: char[40]
    └─ ...freed automatically on function return
```

## Property Computation Logic

### Parabola `(y-k)² = 4p(x-h)` or `(x-h)² = 4p(y-k)`

```
if A ≠ 0 (horizontal parabola):  // (y-k)² = 4p(x-h)
    focus_x = center_h + p
    focus_y = center_k
    directrix = center_h - p  (vertical line x = ...)
else:  // (x-h)² = 4p(y-k)
    focus_x = center_h
    focus_y = center_k + p
    directrix = center_k - p  (horizontal line y = ...)
```

### Ellipse `(x-h)²/a² + (y-k)²/b² = 1`

```
if a² > b²:  // Major axis horizontal
    c² = a² - b²
    foci = (center_h ± c, center_k)
    major_endpoints = (center_h ± a, center_k)
    minor_endpoints = (center_h, center_k ± b)
else:  // Major axis vertical
    c² = b² - a²
    foci = (center_h, center_k ± c)
    major_endpoints = (center_h, center_k ± b)
    minor_endpoints = (center_h ± a, center_k)
```

### Hyperbola `(x-h)²/a² - (y-k)²/b² = 1`

```
if A > 0:  // Transverse axis horizontal
    vertices = (center_h ± a, center_k)
    c² = a² + b²
    foci = (center_h ± c, center_k)
    slope = b/a
    asymptote_1: y - center_k = slope(x - center_h)
    asymptote_2: y - center_k = -slope(x - center_h)
else:  // Transverse axis vertical
    vertices = (center_h, center_k ± a)
    c² = a² + b²
    foci = (center_h, center_k ± c)
    slope = a/b
    asymptote_1: y - center_k = slope(x - center_h)
    asymptote_2: y - center_k = -slope(x - center_h)
```

## Compilation Dependencies

```
gui.c
├── includes conic_display.h
│   ├── includes conic.h
│   │   ├── includes ../ast.h
│   │   └── includes ../imath/*.h
│   └── type: ConicProperties
├── calls conic_ComputeProperties()
├── calls display_*_properties()
└── calls conic_PropertiesCleanup()

conic_display.c
├── includes conic_display.h
├── includes conic.h
├── implements conic_ComputeProperties()
├── implements compute_*_properties()
└── implements conic_PropertiesCleanup()
```

## Testing Checklist

- [x] Parabola classification & properties display
- [x] Ellipse classification & properties display  
- [x] Circle classification & properties display
- [x] Hyperbola classification & properties display
- [x] Proper memory cleanup
- [x] Compilation without errors
- [x] Integration with existing UI

---

**This architecture ensures:**
- ✓ Clean separation of concerns (display vs computation)
- ✓ Reusable property computation functions
- ✓ Proper memory management
- ✓ Exact rational arithmetic
- ✓ Easy to extend for new conic types or properties
