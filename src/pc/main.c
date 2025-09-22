/*
    PineappleCAS: the multi-purpose CAS specifically for the TI-84+ CE

    Authors:
    Nathan Farlow
*/

#ifdef COMPILE_PC

#include <stdlib.h>
#include <stdio.h>
#include <time.h>

#include <string.h>
#include <limits.h>  /* for INT_MIN */

#include "../ast.h"
#include "../parser.h"

#include "../dbg.h"

#include "../cas/cas.h"
#include "../cas/integral.h"  /* antiderivative() */

#include "tests.h"

void display_help() {
    printf("Usage: ./pineapple [operation] [args]\n");
    printf("Valid operations include:\n");
    printf("\ttest [file]\t\t\tRuns all tests in file\n");
    printf("\tsimplify [expression]\t\tSimplifies expression. Also evaluates constants.\n");
    printf("\tgcd [expression1] [expression2]\tPrints the GCD of the two expressions\n");
    printf("\tfactor [expression]\t\tFactors expression\n");
    printf("\texpand [expression]\t\tExpands expression\n");
    printf("\tderivative [expression] [respect to] [(optional) eval at]\n");
    printf("\tantideriv [expression] [respect to]\tComputes an antiderivative (indefinite integral)\n");
}

/*Trim null terminated string*/
uint8_t *trim(char *input, unsigned *len) {
    unsigned i, trimmed_len = 0, trim_index = 0;
    uint8_t *trimmed;

    for(i = 0; i < strlen(input) + 1; i++) {
        if(input[i] != ' ' && input[i] != '\t')
            trimmed_len++;
    }

    trimmed = (uint8_t*)malloc(trimmed_len * sizeof(uint8_t));

    for(i = 0; i < strlen(input) + 1; i++) {
        if(input[i] != ' ' && input[i] != '\t')
            trimmed[trim_index++] = (uint8_t)input[i];
    }

    *len = trimmed_len - 1; /*Don't include null byte*/

    return trimmed;
}

/* =========================
 * Degree-based sorting helpers (used only by CLI antideriv)
 * ========================= */

/* Return a small integer value if n is an exact small integer in [-32, 32], else INT_MIN */
static int small_int_value_if_integer(pcas_ast_t *n) {
    int k;
    if (!n || n->type != NODE_NUMBER) return INT_MIN;
    for (k = -32; k <= 32; ++k) {
        if (mp_rat_compare_value(n->op.num, k, 1) == 0) return k;
    }
    return INT_MIN;
}

/* Recursively compute a crude "degree" of expr w.r.t. var. */
static int degree_wrt(pcas_ast_t *expr, pcas_ast_t *var) {
    OperatorType op;
    pcas_ast_t *ch;
    int d, best, acc, n;

    if (!expr) return 0;

    if (expr->type == NODE_SYMBOL) {
        if (ast_Compare(expr, var)) return 1;
        return 0;
    }
    if (expr->type == NODE_NUMBER) return 0;

    if (expr->type != NODE_OPERATOR) return 0;

    op = optype(expr);

    if (op == OP_ADD) {
        best = INT_MIN;
        for (ch = ast_ChildGet(expr, 0); ch != NULL; ch = ch->next) {
            d = degree_wrt(ch, var);
            if (d > best) best = d;
        }
        if (best == INT_MIN) best = 0;
        return best;
    }

    if (op == OP_MULT) {
        acc = 0;
        for (ch = ast_ChildGet(expr, 0); ch != NULL; ch = ch->next) {
            d = degree_wrt(ch, var);
            acc += d;
        }
        return acc;
    }

    /* >>> ADD THIS BLOCK <<< */
    if (op == OP_DIV) {
        pcas_ast_t *num, *den;
        int dn, dd;
        num = ast_ChildGet(expr, 0);
        den = ast_ChildGet(expr, 1);
        dn = degree_wrt(num, var);
        dd = degree_wrt(den, var);
        if (dd == 0) return dn;   /* constant denom -> same degree as numerator */
        return dn - dd;           /* general heuristic */
    }
    /* <<< END NEW BLOCK <<< */

    if (op == OP_POW) {
        pcas_ast_t *base = ast_ChildGet(expr, 0);
        pcas_ast_t *expo = ast_ChildGet(expr, 1);
        if (ast_Compare(base, var)) {
            n = small_int_value_if_integer(expo);
            if (n != INT_MIN) return n;          /* x^n -> n */
            return 2;                             /* x^(something) -> rank above x */
        }
        d = degree_wrt(base, var);
        if (d == 0) {
            if (degree_wrt(expo, var) != 0) return 1;
            return 0;
        }
        return d + 1;
    }

    /* For unary funcs like sin/cos/ln/... just propagate the argument's degree */
    if (is_op_function(op)) {
        pcas_ast_t *arg = ast_ChildGet(expr, 0);
        return degree_wrt(arg, var);
    }

    return 0;
}

/* Sort children of a single OP_ADD node by descending degree wrt var. */
static void sort_one_sum_desc_by_degree(pcas_ast_t *sum, pcas_ast_t *var) {
    pcas_ast_t *ch;
    pcas_ast_t **arr;
    int *deg;
    int i, j, nchildren = 0;

    if (!sum || sum->type != NODE_OPERATOR || optype(sum) != OP_ADD) return;

    /* count children */
    for (ch = ast_ChildGet(sum, 0); ch != NULL; ch = ch->next) nchildren++;
    if (nchildren <= 1) return;

    arr = (pcas_ast_t**)malloc(sizeof(pcas_ast_t*) * nchildren);
    deg = (int*)malloc(sizeof(int) * nchildren);

    /* fill arrays */
    i = 0;
    for (ch = ast_ChildGet(sum, 0); ch != NULL; ch = ch->next) {
        arr[i] = ch;
        deg[i] = degree_wrt(ch, var);
        i++;
    }

    /* insertion sort by descending degree; stable on equal degrees */
    for (i = 1; i < nchildren; ++i) {
        pcas_ast_t *save_node = arr[i];
        int save_deg = deg[i];
        j = i - 1;
        while (j >= 0 && deg[j] < save_deg) {
            arr[j + 1] = arr[j];
            deg[j + 1] = deg[j];
            j--;
        }
        arr[j + 1] = save_node;
        deg[j + 1] = save_deg;
    }

    /* Rebuild a new sum with children in the desired order (using copies) */
    {
        pcas_ast_t *sorted = ast_MakeOperator(OP_ADD);
        void replace_node(pcas_ast_t*, pcas_ast_t*); /* from simplify.c */
        for (i = 0; i < nchildren; ++i) {
            ast_ChildAppend(sorted, ast_Copy(arr[i]));
        }
        replace_node(sum, sorted);
    }

    free(arr);
    free(deg);
}

/* Recursively sort every OP_ADD inside e by descending degree wrt var */
static void sort_all_sums_desc_by_degree(pcas_ast_t *e, pcas_ast_t *var) {
    pcas_ast_t *ch;
    if (!e) return;
    if (e->type == NODE_OPERATOR) {
        for (ch = ast_ChildGet(e, 0); ch != NULL; ch = ch->next) {
            sort_all_sums_desc_by_degree(ch, var);
        }
        if (optype(e) == OP_ADD) {
            sort_one_sum_desc_by_degree(e, var);
        }
    }
}

/* =========================
 * End degree-based sorting helpers
 * ========================= */

int run_gcd(int argc, char **argv) {

    uint8_t *trimmed_a, *trimmed_b;
    unsigned trimmed_a_len, trimmed_b_len;

    pcas_error_t err;
    pcas_ast_t *a, *b, *g;

    uint8_t *output;
    unsigned output_len;

    if(argc <= 3) {
        display_help();
        return -1;
    }

    trimmed_a = trim(argv[2], &trimmed_a_len);

    printf("Parsing \"%s\"\n", trimmed_a);

    a = parse(trimmed_a, trimmed_a_len, str_table, &err);

    printf("%s\n", error_text[err]);

    if(err != E_SUCCESS || a == NULL)
        return -1;

    simplify(a, SIMP_ALL);

    trimmed_b = trim(argv[3], &trimmed_b_len);

    printf("Parsing \"%s\"\n", trimmed_b);

    b = parse(trimmed_b, trimmed_b_len, str_table, &err);

    printf("%s\n", error_text[err]);

    if(err != E_SUCCESS || b == NULL)
        return -1;

    simplify(b, SIMP_ALL);

    printf("Computing gcd...\n\n");

    g = gcd(a, b);

    simplify(g, SIMP_ALL);
    simplify_canonical_form(g, CANONICAL_ALL);

    dbg_print_tree(g, 4);

    printf("\n");

    output = export_to_binary(g, &output_len, str_table, &err);

    if(err == E_SUCCESS && output != NULL) {
        printf("Output: ");
        printf("%.*s\n", output_len, output);

        free(output);
    }

    free(trimmed_a);
    free(trimmed_b);

    ast_Cleanup(a);
    ast_Cleanup(b);
    ast_Cleanup(g);

    return 0;
}
extern bool simplify_periodic(pcas_ast_t *e);
int run_simplify(int argc, char **argv) {

    uint8_t *trimmed;
    unsigned trimmed_len;

    pcas_error_t err;
    pcas_ast_t *e;

    uint8_t *output;
    unsigned output_len;

    if(argc <= 2) {
        display_help();
        return -1;
    }

    trimmed = trim(argv[2], &trimmed_len);

    printf("Parsing \"%s\"\n", trimmed);

    e = parse(trimmed, trimmed_len, str_table, &err);

    printf("%s\n", error_text[err]);

    if(err == E_SUCCESS && e != NULL) {

        printf("\n");
        dbg_print_tree(e, 4);

        printf("\n");

        printf("Simplifying...\n\n");

        simplify(e, SIMP_ALL);
        simplify_canonical_form(e, CANONICAL_ALL);

        dbg_print_tree(e, 4);

        printf("\n");

        output = export_to_binary(e, &output_len, str_table, &err);

        if(err == E_SUCCESS && output != NULL) {
            printf("Output: ");
            printf("%.*s\n", output_len, output);

            free(output);
        }

    }

    free(trimmed);
    ast_Cleanup(e);

    return 0;
}

int run_factor(int argc, char **argv) {
uint8_t *trimmed;
    unsigned trimmed_len;

    pcas_error_t err;
    pcas_ast_t *e;

    uint8_t *output;
    unsigned output_len;

    if(argc <= 2) {
        display_help();
        return -1;
    }

    trimmed = trim(argv[2], &trimmed_len);

    printf("Parsing \"%s\"\n", trimmed);

    e = parse(trimmed, trimmed_len, str_table, &err);

    printf("%s\n", error_text[err]);

    if(err == E_SUCCESS && e != NULL) {

        printf("\n");
        dbg_print_tree(e, 4);

        printf("\n");

        printf("Simplifying...\n\n");

        simplify(e, SIMP_ALL);

        dbg_print_tree(e, 4);

        printf("\n");

        printf("Factoring...\n\n");

        factor(e, FAC_ALL);

        /*simplify(e, SIMP_ALL);*/
        simplify_canonical_form(e, CANONICAL_ALL);

        dbg_print_tree(e, 4);
        printf("\n");

        output = export_to_binary(e, &output_len, str_table, &err);

        if(err == E_SUCCESS && output != NULL) {
            printf("Output: ");
            printf("%.*s\n", output_len, output);

            free(output);
        }

    }

    free(trimmed);
    ast_Cleanup(e);

    return 0;
}

int run_expand(int argc, char **argv) {

    uint8_t *trimmed;
    unsigned trimmed_len;

    pcas_error_t err;
    pcas_ast_t *e;

    uint8_t *output;
    unsigned output_len;

    if(argc <= 2) {
        display_help();
        return -1;
    }

    trimmed = trim(argv[2], &trimmed_len);

    printf("Parsing \"%s\"\n", trimmed);

    e = parse(trimmed, trimmed_len, str_table, &err);

    printf("%s\n", error_text[err]);

    if(err == E_SUCCESS && e != NULL) {

        printf("\n");
        dbg_print_tree(e, 4);

        printf("\n");

        printf("Simplifying...\n\n");

        simplify(e, SIMP_ALL);

        dbg_print_tree(e, 4);

        printf("\n");

        printf("Expanding...\n\n");

        simplify(e, SIMP_NORMALIZE | SIMP_COMMUTATIVE | SIMP_RATIONAL);
        expand(e, EXP_ALL);
        simplify(e, SIMP_NORMALIZE | SIMP_COMMUTATIVE | SIMP_RATIONAL | SIMP_LIKE_TERMS | SIMP_EVAL);
        simplify_canonical_form(e, CANONICAL_ALL ^ CANONICAL_COMBINE_POWERS);

        dbg_print_tree(e, 4);
        printf("\n");

        output = export_to_binary(e, &output_len, str_table, &err);

        if(err == E_SUCCESS && output != NULL) {
            printf("Output: ");
            printf("%.*s\n", output_len, output);

            free(output);
        }

    }

    free(trimmed);
    ast_Cleanup(e);

    return 0;
}

int run_test(int argc, char **argv) {
    unsigned len, i, failed = 0, passed = 0;
    test_t **arr;

    clock_t delta;

    if(argc < 3) {
        display_help();
        return -1;
    }

    arr = test_Load(argv[2], &len);

    if(arr == NULL) {
        printf("Could not load test file.\n");
        return -1;
    }

    printf("Running tests...\n");

    delta = clock();
    for(i = 0; i < len; i++) {
        test_t *t = arr[i];
        printf("Running test %d/%d on line %d... ", i + 1, len, t->line);
        if(!test_Run(t)) {
            puts("[FAIL]");
            failed++;
        } else {
            puts("[OK]");
            passed++;
        }
    }
    delta = clock() - delta;

    test_CleanupArr(arr, len);

    printf("Finished in %li microseconds.\n", delta / (CLOCKS_PER_SEC / 1000));
    printf("Passed: %u/%u, Failed: %u/%u\n", passed, len, failed, len);

    if(failed == 0) {
        printf("All tests passed!\n");
        return 0;
    }

    return -1;
}

int run_derivative(int argc, char **argv) {

    uint8_t *trimmed;
    unsigned trimmed_len;

    pcas_error_t err;
    pcas_ast_t *e = NULL, *respect_to = NULL, *at = NULL;

    if(argc <= 3) {
        display_help();
        return -1;
    }

    trimmed = trim(argv[2], &trimmed_len);
    printf("Parsing \"%s\"\n", trimmed);
    e = parse(trimmed, trimmed_len, str_table, &err);
    printf("%s\n", error_text[err]);
    free(trimmed);

    if(err == E_SUCCESS) {
        trimmed = trim(argv[3], &trimmed_len);
        printf("Parsing \"%s\"\n", trimmed);
        respect_to = parse(trimmed, trimmed_len, str_table, &err);
        printf("%s\n", error_text[err]);
        free(trimmed);
    }

    if(err == E_SUCCESS) {

        if(argc >= 5) {
            trimmed = trim(argv[4], &trimmed_len);
            printf("Parsing \"%s\"\n", trimmed);
            at = parse(trimmed, trimmed_len, str_table, &err);
            printf("%s\n", error_text[err]);
            free(trimmed);
        } else {
            at = ast_Copy(respect_to);
        }

    }

    if(err == E_SUCCESS && e != NULL && respect_to != NULL && at != NULL) {

        printf("\n");
        dbg_print_tree(e, 4);

        printf("\n");

        printf("Simplifying...\n\n");

        simplify(e, SIMP_ALL);

        dbg_print_tree(e, 4);

        printf("\n");

        printf("Taking derivative...\n");

        derivative(e, respect_to, at);

        printf("Simplifying...\n\n");

        simplify(e, SIMP_ALL);
        simplify_canonical_form(e, CANONICAL_ALL);

        dbg_print_tree(e, 4);
        printf("\n");

        /* print result */
        {
            uint8_t *output2;
            unsigned output_len2;
            output2 = export_to_binary(e, &output_len2, str_table, &err);
            if(err == E_SUCCESS && output2 != NULL) {
                printf("Output: ");
                printf("%.*s\n", output_len2, output2);
                free(output2);
            }
        }
    }

    ast_Cleanup(e);
    ast_Cleanup(respect_to);
    ast_Cleanup(at);

    return 0;
}

/* Antiderivative CLI with degree-sorted sum printing */
int run_antideriv(int argc, char **argv) {

    uint8_t *trimmed;
    unsigned trimmed_len;

    pcas_error_t err;
    pcas_ast_t *e = NULL, *respect_to = NULL;

    uint8_t *output;
    unsigned output_len;

    if(argc <= 3) {
        display_help();
        return -1;
    }

    /* parse expression */
    trimmed = trim(argv[2], &trimmed_len);
    printf("Parsing \"%s\"\n", trimmed);
    e = parse(trimmed, trimmed_len, str_table, &err);
    printf("%s\n", error_text[err]);
    free(trimmed);

    /* parse variable */
    if(err == E_SUCCESS) {
        trimmed = trim(argv[3], &trimmed_len);
        printf("Parsing \"%s\"\n", trimmed);
        respect_to = parse(trimmed, trimmed_len, str_table, &err);
        printf("%s\n", error_text[err]);
        free(trimmed);
    }

    if(err == E_SUCCESS && e != NULL && respect_to != NULL) {

        printf("\n");
        dbg_print_tree(e, 4);

        printf("\n");

        printf("Simplifying...\n\n");

        simplify(e, SIMP_ALL);

        dbg_print_tree(e, 4);

        printf("\n");

        printf("Taking antiderivative...\n");

        antiderivative(e, respect_to);

        printf("Simplifying...\n\n");

        /* Normal simplify + canonicalize */
        simplify(e, SIMP_ALL);
        simplify_canonical_form(e, CANONICAL_ALL);

        /* Now sort all sums by descending degree for nicer printing */
        sort_all_sums_desc_by_degree(e, respect_to);

        dbg_print_tree(e, 4);
        printf("\n");

        output = export_to_binary(e, &output_len, str_table, &err);

        if(err == E_SUCCESS && output != NULL) {
            printf("Output: ");
            printf("%.*s\n", output_len, output);

            free(output);
        }

    }

    ast_Cleanup(e);
    ast_Cleanup(respect_to);

    return 0;
}

int main(int argc, char **argv) {
    int ret;

    if(argc > 1) {
        if(!strcmp(argv[1], "test"))            ret = run_test(argc, argv);
        else if(!strcmp(argv[1], "simplify"))   ret = run_simplify(argc, argv);
        else if(!strcmp(argv[1], "gcd"))        ret = run_gcd(argc, argv);
        else if(!strcmp(argv[1], "factor"))     ret = run_factor(argc, argv);
        else if(!strcmp(argv[1], "expand"))     ret = run_expand(argc, argv);
        else if(!strcmp(argv[1], "derivative")) ret = run_derivative(argc, argv);
        else if(!strcmp(argv[1], "antideriv"))  ret = run_antideriv(argc, argv);
        else {
            display_help();
            return -1;
        }
        id_UnloadAll();
        return ret;
    }

    display_help();
    return -1;
}

#else
typedef int make_iso_compilers_happy;
#endif
