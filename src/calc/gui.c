#ifndef COMPILE_PC

#include "gui.h"

#include <tice.h>
#include <fileioc.h>

#include <graphx.h>
#include <keypadc.h>

#include <string.h>

#include "../parser.h"
#include "../cas/cas.h"
#include "../cas/identities.h"
#include "../cas/derivative.h"
#include "../cas/integral.h"
#include "../cas/conic.h"
#include "../cas/conic_display.h"

#include "interface.h"

void draw_string_centered(char *text, int x, int y) {
    unsigned len;
    len = gfx_GetStringWidth(text);

    gfx_SetTextBGColor(COLOR_TRANSPARENT);
    gfx_SetTextFGColor(COLOR_TEXT);

    gfx_PrintStringXY(text, x - len / 2, y);
}

void draw_background() {

    gfx_SetMonospaceFont(0);

    gfx_FillScreen(COLOR_BACKGROUND);

    gfx_SetTextTransparentColor(COLOR_TRANSPARENT);
    gfx_SetTextBGColor(COLOR_TRANSPARENT);
    gfx_SetTextFGColor(COLOR_TEXT);

    /*Outer border*/
    gfx_SetColor(COLOR_BLUE);
    gfx_Rectangle(1, 1, LCD_WIDTH - 2, LCD_HEIGHT - 2);
    gfx_HorizLine(1, LCD_HEIGHT - 21, LCD_WIDTH - 2);

    draw_string_centered("PineappleCAS v1.3 by Nathan Farlow", LCD_WIDTH / 2, LCD_HEIGHT - 14);

    draw_string_centered("Input", LCD_WIDTH / 4 + 20, 14);
    draw_string_centered("Output", LCD_WIDTH / 4 * 3 - 20, 14);

    /*Outer selection border*/
    gfx_Rectangle(10, 50, LCD_WIDTH - 20, 160);

    /*Function rectangle*/
    gfx_Rectangle(10 + 2, 50 + 2, 100, 160 - 4);
    draw_string_centered("Function", 10 + 2 + 100 / 2, 50 + 10);

    draw_string_centered("Options", 10 + 2 + 100 + (LCD_WIDTH - 10 - 10 - 2 - 100) / 2, 50 + 10);
}

typedef enum {
    GUI_LABEL,
    GUI_CHECKBOX,
    GUI_CHARSELECT,
    GUI_DROPDOWN,
    GUI_BUTTON
} GuiType;

/*I miss oop so much*/
typedef struct {

    GuiType type;

    int x, y, w, h;
    bool active;

    char *text;

    /*For checkboxes*/
    bool checked;
    /*For dropdowns*/
    unsigned index;
    /*for char select*/
    char character;

    /*For dropdowns*/
    unsigned selected_index;
} view_t;

#define NUM_DROPDOWN_ENTRIES 21
char *dropdown_entries[NUM_DROPDOWN_ENTRIES] = {
    "Y1", "Y2", "Y3", "Y4", "Y5", "Y6", "Y7", "Y8", "Y9", "Y0",
    "Str1", "Str2", "Str3", "Str4", "Str4", "Str6", "Str7", "Str8", "Str9", "Str0",
    "Ans"
};

#define NUM_IO 2
#define NUM_FUNCTION 7
#define NUM_SIMPLIFY 7
#define NUM_EVALUATE 5
#define NUM_EXPAND 3
#define NUM_DERIVATIVE 2
#define NUM_HELP 0
#define NUM_ANTIDERIVATIVE 3
#define NUM_CONIC 3

view_t *io_context[NUM_IO];
view_t *function_context[NUM_FUNCTION];
view_t *simplify_context[NUM_SIMPLIFY];
view_t *evaluate_context[NUM_EVALUATE];
view_t *expand_context[NUM_EXPAND];
view_t *derivative_context[NUM_DERIVATIVE];
view_t *help_context[1];
view_t *antiderivative_context[NUM_ANTIDERIVATIVE];
view_t *antideriv_ibp_checkbox;
view_t *button_antiderivative;
view_t *conic_context[NUM_CONIC];
view_t *conic_rhs_dropdown;
view_t *button_conic;

view_t *from_drop, *to_drop;

view_t *button_simplify;
view_t *button_evaluate;
view_t *button_expand;
view_t *button_derivative;

view_t *console_button;

typedef enum {
    CONTEXT_IO,
    CONTEXT_FUNCTION,
    CONTEXT_SIMPLIFY,
    CONTEXT_EVALUATE,
    CONTEXT_EXPAND,
    CONTEXT_DERIVATIVE,
    CONTEXT_ANTIDERIVATIVE,
    CONTEXT_CONIC,
    CONTEXT_HELP,
    NUM_CONTEXTS
} Context;

unsigned elements_in_context[NUM_CONTEXTS] = {
    NUM_IO,
    NUM_FUNCTION,
    NUM_SIMPLIFY,
    NUM_EVALUATE,
    NUM_EXPAND,
    NUM_DERIVATIVE,
    NUM_ANTIDERIVATIVE,
    NUM_CONIC,
    NUM_HELP
};

view_t **context_lookup[NUM_CONTEXTS] = {
    io_context, function_context, simplify_context,
    evaluate_context, expand_context, derivative_context,
    antiderivative_context, conic_context,
    help_context
};

Context current_context = CONTEXT_FUNCTION;
unsigned active_index = 0;
unsigned function_index = 0;

static void write_strN_ascii_gui(uint8_t N, const uint8_t *txt, unsigned len);
static uint8_t *rewrite_sqrt_to_pow_ascii_gui(const uint8_t *in, unsigned in_len, unsigned *out_len);
void draw_label(view_t *v) {
    gfx_PrintStringXY(v->text, v->x, v->y + v->h / 2 - TEXT_HEIGHT / 2);
}

void draw_checkbox(view_t *v) {
    gfx_SetColor(COLOR_PURPLE);
    gfx_Rectangle(v->x, v->y, v->w, v->h);

    if(v->checked) {
        gfx_FillRectangle(v->x + 2, v->y + 2, v->w - 4, v->h - 4);
    }

    if(v->text != NULL) {
        gfx_PrintStringXY(v->text, v->x + v->w + 4, v->y + v->h / 2 - TEXT_HEIGHT / 2);
    }
}

void draw_dropdown(view_t *v) {
    gfx_SetColor(COLOR_PURPLE);
    gfx_Rectangle(v->x, v->y, v->w, v->h);
    draw_string_centered(dropdown_entries[v->index], v->x + v->w / 2, v->y + v->h / 2 - TEXT_HEIGHT / 2);
}

void draw_button(view_t *v) {
    gfx_SetColor(COLOR_PURPLE);
    gfx_Rectangle(v->x, v->y, v->w, v->h);
    draw_string_centered(v->text, v->x + v->w / 2, v->y + v->h / 2 - TEXT_HEIGHT / 2);
}

void draw_charselect(view_t *v) {
    char buffer[2] = {0};
    gfx_SetColor(COLOR_PURPLE);
    gfx_Rectangle(v->x, v->y, v->w, v->h);

    buffer[0] = v->character;
    draw_string_centered(buffer, v->x + v->w / 2, v->y + v->h / 2 - TEXT_HEIGHT / 2);
}

void view_draw(view_t *v) {

    gfx_SetTextBGColor(COLOR_TRANSPARENT);
    gfx_SetTextFGColor(COLOR_TEXT);

    switch(v->type) {
    case GUI_LABEL:         draw_label(v);      break;
    case GUI_CHECKBOX:      draw_checkbox(v);   break;
    case GUI_DROPDOWN:      draw_dropdown(v);   break;
    case GUI_BUTTON:        draw_button(v);     break;
    case GUI_CHARSELECT:    draw_charselect(v); break;
    default: return;
    }

    if(v->active) {
        gfx_SetTextFGColor(COLOR_PURPLE);
        gfx_PrintStringXY(">", v->x - 10, v->y + v->h / 2 - TEXT_HEIGHT / 2);
    }
}

view_t *view_create(GuiType type, int x, int y, int w, int h, char *text) {
    view_t *v;
    v = calloc(1, sizeof(view_t));
    v->type = type;
    v->x = x;
    v->y = y;
    v->w = w;
    v->h = h;
    v->text = text;
    return v;
}

view_t *view_create_checkbox(int x, int y, char *text, bool checked) {
    view_t *v;
    v = view_create(GUI_CHECKBOX, x, y, 8, 8, text);
    v->checked = checked;
    return v;
}

view_t *view_create_button(int x, int y, char *text) {
    int width;
    width = gfx_GetStringWidth(text);
    return view_create(GUI_BUTTON, x - width / 2, y - TEXT_HEIGHT / 2, width + 8, 20, text);
}

view_t *view_create_dropdown(int x, int y, unsigned index) {
    view_t *v;
    v = view_create(GUI_DROPDOWN, x, y, 50, 20, NULL);
    v->index = index;
    return v;
}

view_t *view_create_label(int x, int y, char *text) {
    return view_create(GUI_LABEL, x, y, 0, 8, text);
}

view_t *view_create_charselect(int x, int y) {
    view_t *v;
    v = view_create(GUI_CHARSELECT, x, y, 16, 16, NULL);
    v->character = 'X';
    return v;
}

void draw_context(Context c) {
    unsigned i;

    gfx_SetColor(COLOR_BACKGROUND);

    switch(c) {
        case CONTEXT_IO:
            gfx_FillRectangle(5, 14 + 8, LCD_WIDTH - 10, 26);
            break;
        case CONTEXT_FUNCTION:
            gfx_FillRectangle(10 + 4, 70, 100 - 4, 120);
            break;
        default:
            gfx_FillRectangle(112, 70, 195, 138);
            break;
    }

    gfx_SetTextFGColor(COLOR_TEXT);
    if(c == CONTEXT_EVALUATE) {
        gfx_PrintStringXY("From: ", 124 + 25, 96 + 12 + 10 - TEXT_HEIGHT / 2);
        gfx_PrintStringXY("To: ", 124 + 25, 96 + 12 + 24 + 10 - TEXT_HEIGHT / 2);
    } else if(c == CONTEXT_CONIC) {
        gfx_PrintStringXY("RHS value: ", 124, 96 + 12 - TEXT_HEIGHT / 2);
    } else if(c == CONTEXT_HELP) {
        gfx_PrintStringXY("View https://github.com/", 115, 80 + 10 * 0);
        gfx_PrintStringXY("nathanfarlow/PineappleCAS", 115, 80 + 10 * 1);
        gfx_PrintStringXY("for usage instructions.", 115, 80 + 10 * 2);

        gfx_PrintStringXY("PineappleCAS uses the imath", 115, 80 + 10 * 4);
        gfx_PrintStringXY("library by Michael J.", 115, 80 + 10 * 5);
        gfx_PrintStringXY("Fromberger.", 115, 80 + 10 * 6);

        gfx_PrintStringXY("Thanks Adriweb and Mateo", 115, 80 + 10 * 8);
        gfx_PrintStringXY("for help and contributions", 115, 80 + 10 * 9);
        gfx_PrintStringXY("to this project.", 115, 80 + 10 * 10);
    } else if(c == CONTEXT_DERIVATIVE || c == CONTEXT_ANTIDERIVATIVE) {
        gfx_PrintStringXY("Respect to: ", 124, 80);
    }

    for(i = 0; i < elements_in_context[c]; i++) {
        view_draw(context_lookup[c][i]);
    }
}

bool console_drawn = false;
int console_index = 0;

void draw_console() {
    gfx_SetColor(COLOR_BACKGROUND);
    gfx_FillRectangle(LCD_WIDTH / 6, LCD_HEIGHT / 6, LCD_WIDTH - LCD_WIDTH / 3, LCD_HEIGHT - LCD_HEIGHT / 3);
    gfx_SetColor(COLOR_BLUE);
    gfx_Rectangle(LCD_WIDTH / 6, LCD_HEIGHT / 6, LCD_WIDTH - LCD_WIDTH / 3, LCD_HEIGHT - LCD_HEIGHT / 3);
    gfx_Rectangle(LCD_WIDTH / 6 + 2, LCD_HEIGHT / 6 + 2, LCD_WIDTH - LCD_WIDTH / 3 - 4, LCD_HEIGHT - LCD_HEIGHT / 3 - 30);

    view_draw(console_button);

    console_drawn = true;
    console_index = 0;  /* Reset text index when drawing new console */
}

void console_write(char *text) {
    if(!console_drawn)
        draw_console();

    gfx_PrintStringXY(text, LCD_WIDTH / 6 + 2 + 4, LCD_HEIGHT / 6 + 2 + 4 + console_index * TEXT_HEIGHT);

    console_index++;
}

void execute_simplify();
void execute_evaluate();
void execute_expand();
void execute_derivative();
void execute_antiderivative();
void execute_conic();

/*the key lookup tables for os_GetCSC()*/
const char alpha_table[] = {0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5C, 0x00, 0x57, 0x52, 0x4D, 0x48, 0x00, 0x00, 0x00, 0x40, 0x56, 0x51, 0x4C, 0x47, 0x00, 0x00, 0x00, 0x5A, 0x55, 0x50, 0x4B, 0x46, 0x43, 0x00, 0x00, 0x59, 0x54, 0x4F, 0x4A, 0x45, 0x42, 0x58, 0x00, 0x58, 0x53, 0x4E, 0x49, 0x44, 0x41, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00};

void handle_input(uint8_t key) {

    if(console_drawn) {
        if(console_button->active && key == sk_Enter) {
            draw_background();
            draw_context(CONTEXT_IO);
            draw_context(CONTEXT_FUNCTION);
            draw_context(current_context);

            console_button->active = false;
            console_drawn = false;
            console_index = 0;
        }
        return;
    }

    switch(current_context) {
    case CONTEXT_IO:
        if(key == sk_Down) {
            io_context[active_index]->active = false;

            current_context = CONTEXT_FUNCTION;
            active_index = 0;
            function_context[0]->active = true;

            draw_context(CONTEXT_IO);
            draw_context(CONTEXT_FUNCTION);
            draw_context(CONTEXT_SIMPLIFY);

        } else if(key == sk_Left && active_index == 1) {
            active_index = 0;
            io_context[1]->active = false;
            io_context[0]->active = true;
            draw_context(CONTEXT_IO);
        } else if(key == sk_Right && active_index == 0) {
            active_index = 1;
            io_context[0]->active = false;
            io_context[1]->active = true;
            draw_context(CONTEXT_IO);
        } else if(key == sk_Enter) {
            view_t *v;
            v = context_lookup[current_context][active_index];
            v->index = (v->index + 1) % NUM_DROPDOWN_ENTRIES;
            draw_context(current_context);
        } else if(key == sk_Up) {
            view_t *v;
            v = context_lookup[current_context][active_index];
            if(v->index == 0)
                v->index = NUM_DROPDOWN_ENTRIES - 1;
            else
                v->index--;
            draw_context(current_context);
        }

        break;
    case CONTEXT_FUNCTION:
        if((key == sk_Right || key == sk_Enter) && elements_in_context[CONTEXT_SIMPLIFY + active_index] > 0) {
            function_index = active_index;

            current_context = (Context)(CONTEXT_SIMPLIFY + active_index);
            function_context[active_index]->active = false;
            active_index = 0;
            context_lookup[current_context][active_index]->active = true;

            draw_context(CONTEXT_FUNCTION);
            draw_context(current_context);

            break;
        }
    default: {
        view_t *v;
        v = context_lookup[current_context][active_index];

        if(key == sk_Up) {
            if(active_index == 0) {
                context_lookup[current_context][active_index]->active = false;
                active_index = 0;
                io_context[active_index]->active = true;
                draw_context(current_context);
                current_context = CONTEXT_IO;
                draw_context(CONTEXT_IO);
                break;
            }

            context_lookup[current_context][active_index]->active = false;
            active_index--;
            context_lookup[current_context][active_index]->active = true;
            draw_context(current_context);

            if(current_context == CONTEXT_FUNCTION)
                draw_context((Context)(CONTEXT_SIMPLIFY + active_index));
        } else if(key == sk_Down) {
            if(active_index == elements_in_context[current_context] - 1)
                break;
            context_lookup[current_context][active_index]->active = false;
            active_index++;
            context_lookup[current_context][active_index]->active = true;
            draw_context(current_context);

            if(current_context == CONTEXT_FUNCTION)
                draw_context((Context)(CONTEXT_SIMPLIFY + active_index));
        } else if(key == sk_Left && current_context != CONTEXT_FUNCTION) {
            context_lookup[current_context][active_index]->active = false;
            draw_context(current_context);
            active_index = function_index;
            current_context = CONTEXT_FUNCTION;
            context_lookup[current_context][active_index]->active = true;
            draw_context(CONTEXT_FUNCTION);
        } else if(key == sk_Enter) {
            switch(v->type) {
            case GUI_CHECKBOX:
                v->checked = !v->checked;

                /* NEW: if this is our IBP checkbox, toggle the integrator */
                if (v == antideriv_ibp_checkbox) {
                    integral_set_ibp_enabled(v->checked);
                }

                draw_context(current_context);
                break;
            case GUI_DROPDOWN:
                v->index = (v->index + 1) % NUM_DROPDOWN_ENTRIES;
                draw_context(current_context);
                break;
            case GUI_BUTTON:
                if(v == button_simplify)        execute_simplify();
                else if(v == button_evaluate)   execute_evaluate();
                else if(v == button_expand)     execute_expand();
                else if(v == button_derivative) execute_derivative();
                else if(v == button_antiderivative) execute_antiderivative();
                else if(v == button_conic)      execute_conic();
                break;
            default:
                break;
            }

        } else {
            if(v->type == GUI_CHARSELECT) {
                char val;
                val = alpha_table[key];

                if(val != 0) {
                    v->character = val;
                    draw_context(current_context);
                }
            }
        }
    }

        break;
    }
}


void gui_Init() {
    io_context[0] = from_drop = view_create_dropdown(LCD_WIDTH / 4 + 20 - 25, 14 + 8 + 4, 0);
    io_context[1] = to_drop = view_create_dropdown(LCD_WIDTH / 4 * 3 - 20 - 25, 14 + 8 + 4, 1);

    function_context[0] = view_create_label(26, 80,  "Simplify");
    function_context[1] = view_create_label(26, 96,  "Evaluate");
    function_context[2] = view_create_label(26, 112, "Expand");
    function_context[3] = view_create_label(26, 128, "Derivative");
    function_context[4] = view_create_label(26, 144, "Antiderivative");
    function_context[5] = view_create_label(26, 160, "Conic");
    function_context[6] = view_create_label(26, 176, "Help");

    simplify_context[0] = view_create_checkbox(124, 80 + 12 * 0, "Basic identities", true);
    simplify_context[1] = view_create_checkbox(124, 80 + 12 * 1, "Trig identities", true);
    simplify_context[2] = view_create_checkbox(124, 80 + 12 * 2, "Hyperbolic identities", true);
    simplify_context[3] = view_create_checkbox(124, 80 + 12 * 3, "Complex identities", true);
    simplify_context[4] = view_create_checkbox(124, 80 + 12 * 4, "Evaluate trig", true);
    simplify_context[5] = view_create_checkbox(124, 80 + 12 * 5, "Evaluate inverse trig", true);
    simplify_context[6] = button_simplify = view_create_button(10 + 2 + 100 + (LCD_WIDTH - 10 - 10 - 2 - 100) / 2, 184, "Simplify");

    evaluate_context[0] = view_create_checkbox(124, 80, "Evaluate constants", true);
    evaluate_context[1] = view_create_checkbox(124, 80 + 12, "Substitue expression:", false);
    evaluate_context[2] = view_create_dropdown(124 + 80, 96 + 12, 10);
    evaluate_context[3] = view_create_dropdown(124 + 80, 96 + 12 + 24, 11);
    evaluate_context[4] = button_evaluate = view_create_button(10 + 2 + 100 + (LCD_WIDTH - 10 - 10 - 2 - 100) / 2, 184, "Evaluate");

    expand_context[0] = view_create_checkbox(124, 80 + 12 * 0, "Expand multiplication", true);
    expand_context[1] = view_create_checkbox(124, 80 + 12 * 1, "Expand powers", true);
    expand_context[2] = button_expand = view_create_button(10 + 2 + 100 + (LCD_WIDTH - 10 - 10 - 2 - 100) / 2, 184, "Expand");

    derivative_context[0] = view_create_charselect(124 + 90, 80 - (16 - TEXT_HEIGHT) / 2);
    derivative_context[1] = button_derivative = view_create_button(10 + 2 + 100 + (LCD_WIDTH - 10 - 10 - 2 - 100) / 2, 184, "Differentiate");

    /* === Antiderivative context: character picker, IBP checkbox, button === */
    antiderivative_context[0] = view_create_charselect(124 + 90, 80 - (16 - TEXT_HEIGHT) / 2);
    antideriv_ibp_checkbox    = view_create_checkbox(124, 80 + 12 * 1, "Use integration by parts (IBP)", false);
    antiderivative_context[1] = antideriv_ibp_checkbox;
    antiderivative_context[2] = button_antiderivative = view_create_button(10 + 2 + 100 + (LCD_WIDTH - 10 - 10 - 2 - 100) / 2, 184, "Antideriv");

    /* === Conic context: right-hand side value input, output form selection, button === */
    conic_context[0] = view_create_label(124, 80, "Classify conic section");
    conic_rhs_dropdown = view_create_dropdown(124 + 90, 96 + 12 - 10, 0);
    conic_context[1] = conic_rhs_dropdown;
    conic_context[2] = button_conic = view_create_button(10 + 2 + 100 + (LCD_WIDTH - 10 - 10 - 2 - 100) / 2, 184, "Classify");

    console_button = view_create_button(LCD_WIDTH / 2, LCD_HEIGHT - LCD_HEIGHT / 6 - 20, "Close");

    current_context = CONTEXT_FUNCTION;
    active_index = 0;
    function_context[0]->active = true;
}


void gui_Cleanup() {
    unsigned i, j;

    for(i = 0; i < NUM_CONTEXTS; i++) {
        for(j = 0; j < elements_in_context[i]; j++) {
            free(context_lookup[i][j]);
        }
    }

    free(console_button);

    id_UnloadAll();
}

void gui_Run() {

    gui_Init();

    os_ClrHome();
    gfx_Begin();

    draw_background();
    draw_context(CONTEXT_IO);
    draw_context(CONTEXT_FUNCTION);
    draw_context(CONTEXT_SIMPLIFY);

    while(true) {
        uint8_t key;
        key = os_GetCSC();

        if(key == sk_Clear)
            break;

        handle_input(key);
    }

    gfx_End();

    gui_Cleanup();
}

void compile(pcas_id_t *arr, unsigned len) {
    unsigned i;
    for(i = 0; i < len; i++) {
        id_Load(&arr[i]);
    }
}

void compile_general() {
    static bool compiled = false;

    if(!compiled) {
        console_write("Compiling basic ids...");
        compile(id_general, ID_NUM_GENERAL);
        compiled = true;
    }
}

void compile_trig() {
    static bool compiled = false;

    if(!compiled) {
        console_write("Compiling trig ids...");
        compile(id_trig_identities, ID_NUM_TRIG_IDENTITIES);
        compiled = true;
    }
}

void compile_trig_constants() {
    static bool compiled = false;

    if(!compiled) {
        console_write("Compiling trig const ids...");
        compile(id_trig_constants, ID_NUM_TRIG_CONSTANTS);
        compiled = true;
    }
}

void compile_trig_inv_constants() {
    static bool compiled = false;

    if(!compiled) {
        console_write("Compiling inv trig const ids...");
        compile(id_trig_inv_constants, ID_NUM_TRIG_INV_CONSTANTS);
        compiled = true;
    }
}

void compile_hyperbolic() {
    static bool compiled = false;

    if(!compiled) {
        console_write("Compiling hyperbolic ids...");
        compile(id_hyperbolic, ID_NUM_HYPERBOLIC);
        compiled = true;
    }
}

void compile_complex() {
    static bool compiled = false;

    if(!compiled) {
        console_write("Compiling complex ids...");
        compile(id_complex, ID_NUM_COMPLEX);
        compiled = true;
    }
}

void compile_derivative() {
    static bool compiled = false;

    if(!compiled) {
        console_write("Compiling derivative ids...");
        compile(id_derivative, ID_NUM_DERIV);
        compiled = true;
    }
}

void compile_all() {
    compile_general();
    compile_trig();
    compile_trig_constants();
    compile_hyperbolic();
    compile_complex();
}

char *token_table[21] = {
    ti_Y1, ti_Y2, ti_Y3, ti_Y4, ti_Y5, ti_Y6, ti_Y7, ti_Y8, ti_Y9, ti_Y0,
    ti_Str1, ti_Str2, ti_Str3, ti_Str4, ti_Str5, ti_Str6, ti_Str7, ti_Str8, ("\xAA\x8\0"), ("\xAA\x9\0"), /*ti_Str0 is misnamed and ti_Str9 does not exist in the current toolchain*/
    ti_Ans
};

pcas_ast_t *parse_from_dropdown_index(unsigned index, pcas_error_t *err) {
    return parse_from_tok((uint8_t*)token_table[index], err);
}

void write_to_dropdown_index(unsigned index, pcas_ast_t *expression, pcas_error_t *err) {
    write_to_tok((uint8_t*)token_table[index], expression, err);
}

void execute_simplify() {
    char buffer[50];

    pcas_ast_t *expression;
    pcas_error_t err;

    unsigned short flags = SIMP_NORMALIZE | SIMP_COMMUTATIVE | SIMP_RATIONAL | SIMP_EVAL | SIMP_DERIV | SIMP_LIKE_TERMS;

    if(simplify_context[0]->checked) {
        compile_general();
        flags |= SIMP_ID_GENERAL;
    }
    if(simplify_context[1]->checked) {
        compile_trig();
        flags |= SIMP_ID_TRIG;
    }
    if(simplify_context[2]->checked) {
        compile_hyperbolic();
        flags |= SIMP_ID_HYPERBOLIC;
    }
    if(simplify_context[3]->checked) {
        compile_complex();
        flags |= SIMP_ID_COMPLEX;
    }
    if(simplify_context[4]->checked) {
        compile_trig_constants();
        flags |= SIMP_ID_TRIG_CONSTANTS;
    }
    if(simplify_context[5]->checked) {
        compile_trig_inv_constants();
        flags |= SIMP_ID_TRIG_INV_CONSTANTS;
    }

    console_write("Parsing input...");

    expression = parse_from_dropdown_index(from_drop->index, &err);

    if(err == E_SUCCESS) {

        if(expression != NULL) {

            console_write("Simplifying...");

            simplify(expression, flags);
            simplify_canonical_form(expression, CANONICAL_ALL);

            console_write("Exporting...");

            write_to_dropdown_index(to_drop->index, expression, &err);

            ast_Cleanup(expression);

            if(err == E_SUCCESS) {
                console_write("Success.");
            } else {
                sprintf(buffer, "Failed. %s.", error_text[err]);
                console_write(buffer);
            }

        } else {
            console_write("Failed. Empty input.");
        }

    } else {
        sprintf(buffer, "Failed. %s.", error_text[err]);
        console_write(buffer);
        if(from_drop->index == 20)
            console_write("Make sure Ans is a string.");
    }

    console_button->active = true;
    view_draw(console_button);
}

void execute_evaluate() {
    char buffer[50];

    bool should_sub, should_eval;
    pcas_ast_t *expression;
    pcas_error_t err;

    should_eval = evaluate_context[0]->checked;
    should_sub = evaluate_context[1]->checked;

    console_write("Parsing input...");

    expression = parse_from_dropdown_index(from_drop->index, &err);

    if(err == E_SUCCESS) {

        if(expression != NULL) {

            simplify(expression, SIMP_NORMALIZE | SIMP_COMMUTATIVE | SIMP_RATIONAL);

            if(should_sub) {
                pcas_ast_t *sub_from, *sub_to;
                pcas_error_t err;

                console_write("Parsing sub from...");
                sub_from = parse_from_dropdown_index(evaluate_context[2]->index, &err);
                simplify(sub_from, SIMP_NORMALIZE | SIMP_COMMUTATIVE | SIMP_RATIONAL);

                if(err == E_SUCCESS) {

                    if(sub_from != NULL) {
                        console_write("Parsing sub to...");
                        sub_to = parse_from_dropdown_index(evaluate_context[3]->index, &err);
                        simplify(sub_to, SIMP_NORMALIZE | SIMP_COMMUTATIVE | SIMP_RATIONAL);

                        if(err == E_SUCCESS) {
                            if(sub_to != NULL) {
                                console_write("Substituting...");
                                substitute(expression, sub_from, sub_to);

                                ast_Cleanup(sub_from);
                                ast_Cleanup(sub_to);
                            } else {
                                console_write("Failed. Empty input.");
                            }
                        } else {
                            sprintf(buffer, "Failed. %s.", error_text[err]);
                            console_write(buffer);
                        }
                    } else {
                        console_write("Failed. Empty input.");
                    }

                } else {
                    sprintf(buffer, "Failed. %s.", error_text[err]);
                    console_write(buffer);
                    if(evaluate_context[3]->index == 20)
                        console_write("Make sure Ans is a string.");
                }
            }

            if(should_eval) {
                console_write("Evaluating constants..");
                eval(expression, EVAL_ALL);    
            }

            simplify(expression, SIMP_NORMALIZE | SIMP_COMMUTATIVE | SIMP_RATIONAL | SIMP_EVAL | SIMP_LIKE_TERMS);
            simplify_canonical_form(expression, CANONICAL_ALL);

            console_write("Exporting...");

            write_to_dropdown_index(to_drop->index, expression, &err);

            ast_Cleanup(expression);

            if(err == E_SUCCESS) {
                console_write("Success.");
            } else {
                sprintf(buffer, "Failed. %s.", error_text[err]);
                console_write(buffer);
            }

        } else {
            console_write("Failed. Empty input.");
        }

    } else {
        sprintf(buffer, "Failed. %s.", error_text[err]);
        console_write(buffer);
        if(from_drop->index == 20)
            console_write("Make sure Ans is a string.");
    }

    console_button->active = true;
    view_draw(console_button);
}

void execute_expand() {
    char buffer[50];

    pcas_ast_t *expression;
    pcas_error_t err;

    unsigned short flags = 0;

    if(expand_context[0]->checked) {
        flags |= EXP_DISTRIB_NUMBERS | EXP_DISTRIB_MULTIPLICATION | EXP_DISTRIB_ADDITION;
    }
    if(expand_context[1]->checked) {
        flags |= EXP_EXPAND_POWERS;
    }

    console_write("Parsing input...");

    expression = parse_from_dropdown_index(from_drop->index, &err);

    if(err == E_SUCCESS) {

        if(expression != NULL) {

            console_write("Expanding...");

            simplify(expression, SIMP_NORMALIZE | SIMP_COMMUTATIVE | SIMP_RATIONAL);
            expand(expression, flags);
            simplify(expression, SIMP_NORMALIZE | SIMP_COMMUTATIVE | SIMP_RATIONAL | (expand_context[0]->checked ? SIMP_LIKE_TERMS : 0) | SIMP_EVAL);
            simplify_canonical_form(expression, CANONICAL_ALL ^ CANONICAL_COMBINE_POWERS);

            console_write("Exporting...");

            write_to_dropdown_index(to_drop->index, expression, &err);

            ast_Cleanup(expression);

            if(err == E_SUCCESS) {
                console_write("Success.");
            } else {
                sprintf(buffer, "Failed. %s.", error_text[err]);
                console_write(buffer);
            }

        } else {
            console_write("Failed. Empty input.");
        }

    } else {
        sprintf(buffer, "Failed. %s.", error_text[err]);
        console_write(buffer);
        if(from_drop->index == 20)
            console_write("Make sure Ans is a string.");
    }

    console_button->active = true;
    view_draw(console_button);
}

void execute_derivative() {
    char buffer[50];

    pcas_ast_t *expression;
    pcas_error_t err;

    compile_derivative();
    
    console_write("Parsing input...");

    expression = parse_from_dropdown_index(from_drop->index, &err);

    if(err == E_SUCCESS) {

        if(expression != NULL) {
            pcas_ast_t *respect_to;
            char *theta = "theta";

            /*We treat the @ character as theta partially out of laziness*/
            if(derivative_context[0]->character == '@') {
                respect_to = parse((uint8_t*)theta, strlen(theta), str_table, &err);
            } else {
                respect_to = parse((uint8_t*)&derivative_context[0]->character, 1, str_table, &err);
            }

            console_write("Differentiating...");

            simplify(expression, SIMP_NORMALIZE | SIMP_COMMUTATIVE | SIMP_RATIONAL);

            /*Automatically takes care of embedded derivatives*/
            derivative(expression, respect_to, respect_to);

            simplify(expression, SIMP_NORMALIZE | SIMP_COMMUTATIVE | SIMP_RATIONAL | SIMP_EVAL | SIMP_LIKE_TERMS);
            simplify_canonical_form(expression, CANONICAL_ALL);

            console_write("Exporting...");

            write_to_dropdown_index(to_drop->index, expression, &err);

            ast_Cleanup(expression);

            if(err == E_SUCCESS) {
                console_write("Success.");
            } else {
                sprintf(buffer, "Failed. %s.", error_text[err]);
                console_write(buffer);
            }

        } else {
            console_write("Failed. Empty input.");
        }

    } else {
        sprintf(buffer, "Failed. %s.", error_text[err]);
        console_write(buffer);
        if(from_drop->index == 20)
            console_write("Make sure Ans is a string.");
    }

    console_button->active = true;
    view_draw(console_button);
}
#include <fileioc.h>  // already included above; fine to keep once

/* Build TI token for StrN (N = 0..9). Second byte is:
   0..8 => Str1..Str9, and 9 => Str0. */
static void build_str_token_gui(uint8_t N, uint8_t tok[4]) {
    tok[0] = 0xAAu;
    tok[2] = 0x00u;
    tok[3] = 0x00u;
    if (N == 0) tok[1] = 9;           /* Str0 */
    else        tok[1] = (uint8_t)(N - 1); /* Str1..Str9 */
}

/* Write raw bytes (already tokenized with ti_table) to StrN so the OS displays them nicely. */
static void write_strN_ascii_gui(uint8_t N, const uint8_t *bytes, unsigned len) {
    uint8_t tok[4];
    ti_var_t v;
    if (!bytes || !len) return;
    build_str_token_gui(N, tok);
    v = ti_OpenVar((char*)tok, "w", OS_TYPE_STR);
    if (v) { ti_Write(bytes, len, 1, v); ti_Close(v); }
}

/* Rewrite every "sqrt(<expr>)" into "(<expr>)^(1/2)" in an ASCII buffer. */
static uint8_t *rewrite_sqrt_to_pow_ascii_gui(const uint8_t *in, unsigned in_len, unsigned *out_len) {
    unsigned cap = in_len * 3 + 16;
    uint8_t *out = (uint8_t*)malloc(cap);
    unsigned oi = 0, i = 0;
    if (!out) { *out_len = 0; return NULL; }

    while (i < in_len) {
        if (i + 5 <= in_len &&
            in[i]=='s' && in[i+1]=='q' && in[i+2]=='r' && in[i+3]=='t' && in[i+4]=='(') {
            unsigned depth = 0, inner_start;
            i += 5; /* past "sqrt(" */
            if (oi + 1 >= cap) { cap *= 2; out = (uint8_t*)realloc(out, cap); }
            out[oi++] = '(';

            inner_start = i;
            for (; i < in_len; ++i) {
                uint8_t c = in[i];
                if (c=='(') depth++;
                else if (c==')') {
                    if (depth == 0) {
                        unsigned inner_len = i - inner_start;
                        if (oi + inner_len + 8 >= cap) { cap = oi + inner_len + 64; out = (uint8_t*)realloc(out, cap); }
                        memcpy(out + oi, in + inner_start, inner_len);
                        oi += inner_len;
                        out[oi++]=')'; out[oi++]='^'; out[oi++]='(';
                        out[oi++]='1'; out[oi++]='/'; out[oi++]='2'; out[oi++]=')';
                        i++; /* consume ')' */
                        break;
                    } else depth--;
                }
            }
        } else {
            if (oi + 1 >= cap) { cap *= 2; out = (uint8_t*)realloc(out, cap); }
            out[oi++] = in[i++];
        }
    }
    *out_len = oi;
    return out;
}


void execute_antiderivative() {
    char buffer[50];

    pcas_ast_t *expression;
    pcas_error_t err;

    console_write("Parsing input...");

    expression = parse_from_dropdown_index(from_drop->index, &err);

    if(err == E_SUCCESS) {

        if(expression != NULL) {
            pcas_ast_t *respect_to;
            char *theta = "theta";

            /* We treat the @ character as theta (same convention as derivative panel) */
            if(antiderivative_context[0]->character == '@') {
                respect_to = parse((uint8_t*)theta, strlen(theta), str_table, &err);
            } else {
                respect_to = parse((uint8_t*)&antiderivative_context[0]->character, 1, str_table, &err);
            }

            console_write("Integrating...");

            simplify(expression, SIMP_NORMALIZE | SIMP_COMMUTATIVE | SIMP_RATIONAL);

            antiderivative(expression, respect_to);

            simplify(expression, SIMP_NORMALIZE | SIMP_COMMUTATIVE | SIMP_RATIONAL | SIMP_EVAL | SIMP_LIKE_TERMS);
            simplify_canonical_form(expression, CANONICAL_ALL);

            console_write("Exporting...");

            write_to_dropdown_index(to_drop->index, expression, &err);

            ast_Cleanup(expression);
            ast_Cleanup(respect_to);

            if(err == E_SUCCESS) {
                console_write("Success.");
            } else {
                sprintf(buffer, "Failed. %s.", error_text[err]);
                console_write(buffer);
            }

        } else {
            console_write("Failed. Empty input.");
        }

    } else {
        sprintf(buffer, "Failed. %s.", error_text[err]);
        console_write(buffer);
        if(from_drop->index == 20)
            console_write("Make sure Ans is a string.");
    }

    console_button->active = true;
    view_draw(console_button);
}

void execute_conic() {
    char buffer[150];
    char h_str[50], k_str[50], a_str_val[50], b_str_val[50];
    pcas_ast_t *expression, *rhs_expression, *full_equation;
    pcas_error_t err;
    ConicResult *result;
    mp_rat rhs_value;

    /* Draw fresh console for output */
    draw_background();
    draw_context(CONTEXT_IO);
    draw_context(CONTEXT_FUNCTION);
    draw_context(current_context);
    console_drawn = false;
    console_write("Parsing input...");

    expression = parse_from_dropdown_index(from_drop->index, &err);

    if(err == E_SUCCESS) {

        if(expression != NULL) {

            console_write("Classifying conic...");

            /* Parse RHS expression from dropdown BEFORE simplifying LHS */
            rhs_expression = parse_from_dropdown_index(conic_rhs_dropdown->index, &err);
            
            /* Build full equation FIRST: LHS - RHS = 0 */
            if(rhs_expression != NULL) {
                /* Create full equation: LHS - RHS = 0 by adding LHS + (-1)*RHS */
                pcas_ast_t *neg_rhs = ast_MakeBinary(OP_MULT, ast_MakeNumber(num_FromInt(-1)), rhs_expression);
                full_equation = ast_MakeBinary(OP_ADD, expression, neg_rhs);
                
                /* Now simplify the ENTIRE combined equation to flatten and normalize */
                simplify(full_equation, SIMP_NORMALIZE | SIMP_COMMUTATIVE | SIMP_RATIONAL | SIMP_EVAL | SIMP_LIKE_TERMS);
                
                /* RHS is part of full equation now, so pass 0 as rhs_value */
                rhs_value = num_FromInt(0);
            } else {
                /* No RHS specified, treat as = 0 */
                full_equation = expression;
                simplify(full_equation, SIMP_NORMALIZE | SIMP_COMMUTATIVE | SIMP_RATIONAL | SIMP_EVAL | SIMP_LIKE_TERMS);
                rhs_value = num_FromInt(0);
            }

            /* Call the conic classifier with the full equation */
            result = conic_Classify(full_equation, rhs_value);

            if(result != NULL) {
                char *a_str, *c_str, *d_str, *e_str, *f_str;
                
                /* Output classification result */
                sprintf(buffer, "Type: %s", result->type_name);
                console_write(buffer);
                
                /* Display coefficients (compact format) */
                a_str = num_ToString(result->A, 4);
                c_str = num_ToString(result->C, 4);
                d_str = num_ToString(result->D, 4);
                e_str = num_ToString(result->E, 4);
                f_str = num_ToString(result->F, 4);
                
                sprintf(buffer, "A=%s C=%s D=%s", a_str, c_str, d_str);
                console_write(buffer);
                sprintf(buffer, "E=%s F=%s", e_str, f_str);
                console_write(buffer);
                
                /* Build and store canonical form as an AST in Y3 */
                pcas_ast_t *formula = NULL;
                
                if(result->type == CONIC_CIRCLE) {
                    /* (x-h)^2 + (y-k)^2 = r^2 */
                    mp_rat neg_h = num_Copy(result->center_h);
                    mp_rat temp = num_FromInt(-1);
                    mp_rat_mul(neg_h, temp, neg_h);
                    num_Cleanup(temp);
                    
                    mp_rat neg_k = num_Copy(result->center_k);
                    temp = num_FromInt(-1);
                    mp_rat_mul(neg_k, temp, neg_k);
                    num_Cleanup(temp);
                    
                    pcas_ast_t *x_term = ast_MakeBinary(OP_POW, 
                        ast_MakeBinary(OP_ADD, ast_MakeSymbol(SYM_X), 
                            ast_MakeNumber(neg_h)),
                        ast_MakeNumber(num_FromInt(2)));
                    pcas_ast_t *y_term = ast_MakeBinary(OP_POW,
                        ast_MakeBinary(OP_ADD, ast_MakeSymbol(SYM_Y),
                            ast_MakeNumber(neg_k)),
                        ast_MakeNumber(num_FromInt(2)));
                    formula = ast_MakeBinary(OP_ADD, x_term, y_term);
                    console_write("Circle formula in Y3");
                } else if(result->type == CONIC_ELLIPSE) {
                    /* (x-h)^2/a^2 + (y-k)^2/b^2 = 1 */
                    mp_rat neg_h = num_Copy(result->center_h);
                    mp_rat temp = num_FromInt(-1);
                    mp_rat_mul(neg_h, temp, neg_h);
                    num_Cleanup(temp);
                    
                    mp_rat neg_k = num_Copy(result->center_k);
                    temp = num_FromInt(-1);
                    mp_rat_mul(neg_k, temp, neg_k);
                    num_Cleanup(temp);
                    
                    /* result->a and result->b are already a^2 and b^2 */
                    /* Create numerators as (x-h)^2 and (y-k)^2 */
                    pcas_ast_t *x_num = ast_MakeBinary(OP_POW,
                        ast_MakeBinary(OP_ADD, ast_MakeSymbol(SYM_X),
                            ast_MakeNumber(neg_h)),
                        ast_MakeNumber(num_FromInt(2)));
                    pcas_ast_t *y_num = ast_MakeBinary(OP_POW,
                        ast_MakeBinary(OP_ADD, ast_MakeSymbol(SYM_Y),
                            ast_MakeNumber(neg_k)),
                        ast_MakeNumber(num_FromInt(2)));
                    
                    /* Divide numerators by a^2 and b^2 */
                    pcas_ast_t *x_term = ast_MakeBinary(OP_DIV, x_num,
                        ast_MakeNumber(num_Copy(result->a)));
                    pcas_ast_t *y_term = ast_MakeBinary(OP_DIV, y_num,
                        ast_MakeNumber(num_Copy(result->b)));
                    formula = ast_MakeBinary(OP_ADD, x_term, y_term);
                    console_write("Ellipse formula in Y3");
                } else if(result->type == CONIC_PARABOLA) {
                    /* Determine parabola orientation from coefficients:
                     * If A != 0 and C = 0: (y-k)^2 = 4p(x-h)  (opens left/right)
                     * If A = 0 and C != 0: (x-h)^2 = 4p(y-k)  (opens up/down)
                     */
                    char *a_str = num_ToString(result->A, 4);
                    char *c_str = num_ToString(result->C, 4);
                    
                    int a_nonzero = mp_rat_compare_value(result->A, 0, 1) != 0;
                    int c_nonzero = mp_rat_compare_value(result->C, 0, 1) != 0;
                    
                    if (a_nonzero && !c_nonzero) {
                        /* (y-k)^2 = 4p(x-h)  where p is in result->a */
                        mp_rat neg_h = num_Copy(result->center_h);
                        mp_rat temp = num_FromInt(-1);
                        mp_rat_mul(neg_h, temp, neg_h);
                        num_Cleanup(temp);
                        
                        mp_rat neg_k = num_Copy(result->center_k);
                        temp = num_FromInt(-1);
                        mp_rat_mul(neg_k, temp, neg_k);
                        num_Cleanup(temp);
                        
                        /* Build: (y-k)^2 */
                        pcas_ast_t *y_squared = ast_MakeBinary(OP_POW,
                            ast_MakeBinary(OP_ADD, ast_MakeSymbol(SYM_Y),
                                ast_MakeNumber(neg_k)),
                            ast_MakeNumber(num_FromInt(2)));
                        
                        /* Build: 4p */
                        mp_rat four_p = num_FromInt(4);
                        mp_rat_mul(four_p, result->a, four_p);
                        
                        /* Build: (x-h) */
                        pcas_ast_t *x_minus_h = ast_MakeBinary(OP_ADD, 
                            ast_MakeSymbol(SYM_X),
                            ast_MakeNumber(neg_h));
                        
                        /* Build: 4p(x-h) */
                        pcas_ast_t *rhs = ast_MakeBinary(OP_MULT, 
                            ast_MakeNumber(four_p),
                            x_minus_h);
                        
                        /* (y-k)^2 = 4p(x-h) */
                        formula = ast_MakeBinary(OP_ADD, y_squared, 
                            ast_MakeBinary(OP_MULT, ast_MakeNumber(num_FromInt(-1)), rhs));
                        console_write("Parabola (y-k)^2=4p(x-h)");
                        
                    } else if (!a_nonzero && c_nonzero) {
                        /* (x-h)^2 = 4p(y-k) */
                        mp_rat neg_h = num_Copy(result->center_h);
                        mp_rat temp = num_FromInt(-1);
                        mp_rat_mul(neg_h, temp, neg_h);
                        num_Cleanup(temp);
                        
                        mp_rat neg_k = num_Copy(result->center_k);
                        temp = num_FromInt(-1);
                        mp_rat_mul(neg_k, temp, neg_k);
                        num_Cleanup(temp);
                        
                        /* Build: (x-h)^2 */
                        pcas_ast_t *x_squared = ast_MakeBinary(OP_POW,
                            ast_MakeBinary(OP_ADD, ast_MakeSymbol(SYM_X),
                                ast_MakeNumber(neg_h)),
                            ast_MakeNumber(num_FromInt(2)));
                        
                        /* Build: 4p (result->a stores p) */
                        mp_rat four_p = num_FromInt(4);
                        mp_rat_mul(four_p, result->a, four_p);
                        
                        /* Build: (y-k) */
                        pcas_ast_t *y_minus_k = ast_MakeBinary(OP_ADD, 
                            ast_MakeSymbol(SYM_Y),
                            ast_MakeNumber(neg_k));
                        
                        /* Build: 4p(y-k) */
                        pcas_ast_t *rhs = ast_MakeBinary(OP_MULT, 
                            ast_MakeNumber(four_p),
                            y_minus_k);
                        
                        /* (x-h)^2 = 4p(y-k) */
                        formula = ast_MakeBinary(OP_ADD, x_squared, 
                            ast_MakeBinary(OP_MULT, ast_MakeNumber(num_FromInt(-1)), rhs));
                        console_write("Parabola (x-h)^2=4p(y-k)");
                    } else {
                        console_write("Parabola: degenerate");
                    }
                    
                    free(a_str);
                    free(c_str);
                } else if(result->type == CONIC_HYPERBOLA) {
                    /* (x-h)^2/a^2 - (y-k)^2/b^2 = 1 */
                    mp_rat neg_h = num_Copy(result->center_h);
                    mp_rat temp = num_FromInt(-1);
                    mp_rat_mul(neg_h, temp, neg_h);
                    num_Cleanup(temp);
                    
                    mp_rat neg_k = num_Copy(result->center_k);
                    temp = num_FromInt(-1);
                    mp_rat_mul(neg_k, temp, neg_k);
                    num_Cleanup(temp);
                    
                    pcas_ast_t *x_term = ast_MakeBinary(OP_DIV,
                        ast_MakeBinary(OP_POW,
                            ast_MakeBinary(OP_ADD, ast_MakeSymbol(SYM_X),
                                ast_MakeNumber(neg_h)),
                            ast_MakeNumber(num_FromInt(2))),
                        ast_MakeNumber(num_Copy(result->a)));
                    pcas_ast_t *y_term = ast_MakeBinary(OP_DIV,
                        ast_MakeBinary(OP_POW,
                            ast_MakeBinary(OP_ADD, ast_MakeSymbol(SYM_Y),
                                ast_MakeNumber(neg_k)),
                            ast_MakeNumber(num_FromInt(2))),
                        ast_MakeNumber(num_Copy(result->b)));
                    formula = ast_MakeBinary(OP_ADD, x_term, 
                        ast_MakeBinary(OP_MULT, ast_MakeNumber(num_FromInt(-1)), y_term));
                    console_write("Hyperbola formula in Y3");
                }
                
                /* Write formula to Y3 if we built one */
                if (formula != NULL) {
                    pcas_error_t write_err;
                    write_to_tok((uint8_t*)OS_VAR_Y3, formula, &write_err);
                    if (write_err != E_SUCCESS) {
                        console_write("Could not write to Y3");
                    }
                }
                
                free(a_str);
                free(c_str);
                free(d_str);
                free(e_str);
                free(f_str);

                ConicProperties *props = conic_ComputeProperties(result);
                if (props != NULL) {
                    char buf[40];
                    if (result->type == CONIC_PARABOLA) {
                        char *v = num_ToString(props->center_x, 4);
                        if (v) { sprintf(buffer, "Vertex x: %s", v); console_write(buffer); free(v); }
                        v = num_ToString(props->focus_x, 4);
                        if (v) { sprintf(buffer, "Focus x: %s", v); console_write(buffer); free(v); }
                    } else if (result->type == CONIC_ELLIPSE) {
                        char *v = num_ToString(props->semi_major, 4);
                        if (v) { sprintf(buffer, "Semi-major: %s", v); console_write(buffer); free(v); }
                    } else if (result->type == CONIC_HYPERBOLA) {
                        char *v = num_ToString(props->center_x, 4);
                        if (v) { sprintf(buffer, "Center x: %s", v); console_write(buffer); free(v); }
                    }
                    conic_PropertiesCleanup(props);
                }

                /* Clean up result */
                conic_ResultCleanup(result);
                console_write("Success.");
            } else {
                console_write("Failed. Classification error.");
            }

            /* Clean up */
            if(rhs_expression != NULL && full_equation != expression) {
                ast_Cleanup(full_equation);
            } else {
                ast_Cleanup(expression);
            }
            num_Cleanup(rhs_value);

        } else {
            console_write("Failed. Empty input.");
        }

    } else {
        sprintf(buffer, "Failed. %s.", error_text[err]);
        console_write(buffer);
        if(from_drop->index == 20)
            console_write("Make sure Ans is a string.");
    }

    console_button->active = true;
    view_draw(console_button);
}


#else
typedef int make_iso_compilers_happy;
#endif
