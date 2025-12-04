#include "conic_display.h"
#include "conic.h"
#include <stdlib.h>
#include <string.h>

static void compute_parabola(ConicResult *r, ConicProperties *p) {
    p->center_x = num_Copy(r->center_h);
    p->center_y = num_Copy(r->center_k);
    p->focus_x = num_Copy(r->center_h);
    mp_rat_add(p->focus_x, r->a, p->focus_x);
    p->focus_y = num_Copy(r->center_k);
    p->directrix_value = num_Copy(r->center_h);
    mp_rat_sub(p->directrix_value, r->a, p->directrix_value);
    p->directrix_is_vertical = mp_rat_compare_value(r->A, 0, 1) != 0 ? 1 : 0;
}

static void compute_ellipse(ConicResult *r, ConicProperties *p) {
    p->center_x = num_Copy(r->center_h);
    p->center_y = num_Copy(r->center_k);
    p->semi_major = num_Copy(r->a);
    p->semi_minor = num_Copy(r->b);
    p->foci_x[0] = num_Copy(r->center_h);
    p->foci_x[1] = num_Copy(r->center_h);
    p->foci_y[0] = num_Copy(r->center_k);
    p->foci_y[1] = num_Copy(r->center_k);
    p->major_axis_endpoint1_x = num_Copy(r->center_h);
    p->major_axis_endpoint1_y = num_Copy(r->center_k);
    p->major_axis_endpoint2_x = num_Copy(r->center_h);
    p->major_axis_endpoint2_y = num_Copy(r->center_k);
    p->minor_axis_endpoint1_x = num_Copy(r->center_h);
    p->minor_axis_endpoint1_y = num_Copy(r->center_k);
    p->minor_axis_endpoint2_x = num_Copy(r->center_h);
    p->minor_axis_endpoint2_y = num_Copy(r->center_k);
}

static void compute_hyperbola(ConicResult *r, ConicProperties *p) {
    p->center_x = num_Copy(r->center_h);
    p->center_y = num_Copy(r->center_k);
    p->vertices_x[0] = num_Copy(r->center_h);
    p->vertices_x[1] = num_Copy(r->center_h);
    p->vertices_y[0] = num_Copy(r->center_k);
    p->vertices_y[1] = num_Copy(r->center_k);
    p->hyperbola_foci_x[0] = num_Copy(r->center_h);
    p->hyperbola_foci_x[1] = num_Copy(r->center_h);
    p->hyperbola_foci_y[0] = num_Copy(r->center_k);
    p->hyperbola_foci_y[1] = num_Copy(r->center_k);
    p->asymptote1_m = num_Copy(r->a);
    p->asymptote1_b = num_Copy(r->center_k);
    p->asymptote2_m = num_Copy(r->a);
    p->asymptote2_b = num_Copy(r->center_k);
}

ConicProperties *conic_ComputeProperties(ConicResult *result) {
    if (result == NULL) {
        return NULL;
    }
    
    ConicProperties *props = (ConicProperties *)malloc(sizeof(ConicProperties));
    if (props == NULL) {
        return NULL;
    }
    
    memset(props, 0, sizeof(ConicProperties));
    
    switch (result->type) {
        case CONIC_CIRCLE:
            props->center_x = num_Copy(result->center_h);
            props->center_y = num_Copy(result->center_k);
            props->semi_major = num_Copy(result->a);
            props->semi_minor = num_Copy(result->a);
            break;
        case CONIC_PARABOLA:
            compute_parabola(result, props);
            break;
        case CONIC_ELLIPSE:
            compute_ellipse(result, props);
            break;
        case CONIC_HYPERBOLA:
            compute_hyperbola(result, props);
            break;
        default:
            break;
    }
    
    return props;
}

void conic_PropertiesCleanup(ConicProperties *props) {
    if (props == NULL) {
        return;
    }
    
    num_Cleanup(props->center_x);
    num_Cleanup(props->center_y);
    num_Cleanup(props->focus_x);
    num_Cleanup(props->focus_y);
    num_Cleanup(props->directrix_value);
    num_Cleanup(props->foci_x[0]);
    num_Cleanup(props->foci_x[1]);
    num_Cleanup(props->foci_y[0]);
    num_Cleanup(props->foci_y[1]);
    num_Cleanup(props->semi_major);
    num_Cleanup(props->semi_minor);
    num_Cleanup(props->major_axis_endpoint1_x);
    num_Cleanup(props->major_axis_endpoint1_y);
    num_Cleanup(props->major_axis_endpoint2_x);
    num_Cleanup(props->major_axis_endpoint2_y);
    num_Cleanup(props->minor_axis_endpoint1_x);
    num_Cleanup(props->minor_axis_endpoint1_y);
    num_Cleanup(props->minor_axis_endpoint2_x);
    num_Cleanup(props->minor_axis_endpoint2_y);
    num_Cleanup(props->vertices_x[0]);
    num_Cleanup(props->vertices_x[1]);
    num_Cleanup(props->vertices_y[0]);
    num_Cleanup(props->vertices_y[1]);
    num_Cleanup(props->hyperbola_foci_x[0]);
    num_Cleanup(props->hyperbola_foci_x[1]);
    num_Cleanup(props->hyperbola_foci_y[0]);
    num_Cleanup(props->hyperbola_foci_y[1]);
    num_Cleanup(props->asymptote1_m);
    num_Cleanup(props->asymptote1_b);
    num_Cleanup(props->asymptote2_m);
    num_Cleanup(props->asymptote2_b);
    
    free(props);
}
