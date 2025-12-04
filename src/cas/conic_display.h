#ifndef CONIC_DISPLAY_H_
#define CONIC_DISPLAY_H_

#include "conic.h"

/* Structure to hold computed conic properties for display */
typedef struct {
    /* Common properties */
    mp_rat center_x;  /* x-coordinate of center/vertex */
    mp_rat center_y;  /* y-coordinate of center/vertex */
    
    /* Parabola properties */
    mp_rat focus_x;
    mp_rat focus_y;
    mp_rat directrix_value;  /* For vertical parabola: directrix is y = directrix_value */
                             /* For horizontal parabola: directrix is x = directrix_value */
    int directrix_is_vertical;  /* 1 if directrix is vertical (x = ...), 0 if horizontal (y = ...) */
    
    /* Ellipse properties */
    mp_rat foci_x[2];      /* x-coordinates of foci */
    mp_rat foci_y[2];      /* y-coordinates of foci */
    mp_rat semi_major;     /* length of semi-major axis */
    mp_rat semi_minor;     /* length of semi-minor axis */
    int major_axis_vertical;  /* 1 if major axis is vertical, 0 if horizontal */
    
    /* Ellipse: endpoints of major and minor axes */
    mp_rat major_axis_endpoint1_x;
    mp_rat major_axis_endpoint1_y;
    mp_rat major_axis_endpoint2_x;
    mp_rat major_axis_endpoint2_y;
    mp_rat minor_axis_endpoint1_x;
    mp_rat minor_axis_endpoint1_y;
    mp_rat minor_axis_endpoint2_x;
    mp_rat minor_axis_endpoint2_y;
    
    /* Hyperbola properties */
    mp_rat vertices_x[2];    /* x-coordinates of vertices */
    mp_rat vertices_y[2];    /* y-coordinates of vertices */
    mp_rat hyperbola_foci_x[2];  /* x-coordinates of foci */
    mp_rat hyperbola_foci_y[2];  /* y-coordinates of foci */
    int transverse_axis_vertical;  /* 1 if transverse axis is vertical, 0 if horizontal */
    
    /* Hyperbola: asymptotes in form y = mx + b or x = my + b */
    mp_rat asymptote1_m;  /* slope for y = mx + b, or "m" if x = my + b */
    mp_rat asymptote1_b;  /* y-intercept */
    mp_rat asymptote2_m;
    mp_rat asymptote2_b;
    int asymptotes_vertical;  /* 1 if asymptotes are of form x = my + b (vertical-ish) */
    
} ConicProperties;

/*
 * Compute display properties for a conic section
 * Input: ConicResult from conic_Classify
 * Returns: ConicProperties structure with computed properties
 * Caller is responsible for cleaning up with conic_PropertiesCleanup()
 */
ConicProperties *conic_ComputeProperties(ConicResult *result);

/*
 * Clean up a ConicProperties structure
 */
void conic_PropertiesCleanup(ConicProperties *props);

#endif

