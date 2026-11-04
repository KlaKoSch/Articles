/*
 * Einfacher Forth-Simulator in C - auf 64-Bit umgestellt
 *
 * Übersetzen:  gcc -std=c99 -Wall -Wextra -o forth forth.c
 * Starten:     ./forth            (interaktiv)
 *              ./forth datei.fs   (Datei laden, danach interaktiv)
 *
 * Unterstützt:
 *   Arithmetik   + - * / mod negate abs min max
 *   Stack        dup drop swap over rot nip 2dup depth
 *   Vergleiche   = <> < > 0=   (wahr = -1, falsch = 0)
 *   Logik        and or xor invert
 *   Ausgabe      . .s cr emit ." text"
 *   Definitionen : name ... ;   (mit recurse für Rekursion)
 *   Kontrolle    if else then | begin until | begin while repeat | do loop (i)
 *   Speicher     variable constant create allot cells here @ ! +!
 *   Schleifen    i j   (Zähler der inneren bzw. äußeren do-Schleife)
 *   Sonstiges    1+ 1- <= >= 0< space spaces page ms
 *                ( Kommentar )  \ Zeilenkommentar  words  bye
 *
 * Ergänzungen für 64-Bit Version:
 *   see name     (Befehlsaufbau zeigen)
 *   dump         (addr len -- ) (Speicherinhalte ausgeben)
 *   u.           (Vorzeichenlose Ausgabe)
 *   info         (Gibt Speicheradressen und Größe von Dictionary, beiden Stacks und Speicher aus)
 *   Erweiterung für Zahlen - erkennt jetzt auch 0x..., 0... (Oktal), 0b... (Binär)
 */
#define _DEFAULT_SOURCE 1
#include <ctype.h>
#include <errno.h>
#include <setjmp.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#define STACK_MAX 256
#define DICT_MAX  512
#define CODE_MAX  256
#define NAME_LEN  32
#define TOK_LEN   64
#define CTRL_MAX  32
#define MAX_DEPTH 200
#define MEM_SIZE  4096

typedef long long cell;

enum { OP_LIT, OP_CALL, OP_JMP, OP_JZ, OP_DO, OP_LOOP, OP_STR };

typedef struct { int op; cell arg; } Instr;

typedef struct {
    char   name[NAME_LEN];
    void (*prim)(void);   /* != NULL: eingebautes Wort */
    Instr *code;          /* sonst: kompiliertes Wort  */
    int    len;
} Word;

static cell ds[STACK_MAX], rs[STACK_MAX];   /* Daten- und Rücksprungstack */
static int  dsp, rsp;

static cell mem[MEM_SIZE];            /* Forth-Speicher, Adresse = Zellenindex */
static int  here_ptr;

static Word dict[DICT_MAX];
static int  dict_n;

static jmp_buf err_env;
static int depth, running = 1, compiling;

static Instr cur[CODE_MAX];                 /* Definition im Aufbau */
static int   cur_len;
static char  cur_name[NAME_LEN];
static int   cstack[CTRL_MAX], csp;         /* Kontrollstack beim Kompilieren */

static const char *src;                     /* aktuelle Eingabeposition */

/* ---------- Fehlerbehandlung und Stacks ---------- */

static void fail(const char *msg) {
    printf("Fehler: %s\n", msg);
    longjmp(err_env, 1);
}

static void push(cell v) {
    if (dsp >= STACK_MAX) fail("Datenstack voll");
    ds[dsp++] = v;
}
static cell pop(void) {
    if (dsp <= 0) fail("Datenstack leer");
    return ds[--dsp];
}
static void rpush(cell v) {
    if (rsp >= STACK_MAX) fail("Rücksprungstack voll");
    rs[rsp++] = v;
}
static void cpush(int v) {
    if (csp >= CTRL_MAX) fail("Kontrollstrukturen zu tief verschachtelt");
    cstack[csp++] = v;
}
static int cpop(void) {
    if (csp <= 0) fail("Kontrollstruktur ohne Gegenstück");
    return cstack[--csp];
}

/* ---------- Primitive Wörter ---------- */

static void p_add(void)    { cell b = pop(), a = pop(); push(a + b); }
static void p_sub(void)    { cell b = pop(), a = pop(); push(a - b); }
static void p_mul(void)    { cell b = pop(), a = pop(); push(a * b); }
static void p_div(void)    { cell b = pop(), a = pop(); if (!b) fail("Division durch 0"); push(a / b); }
static void p_mod(void)    { cell b = pop(), a = pop(); if (!b) fail("Division durch 0"); push(a % b); }
static void p_negate(void) { push(-pop()); }
static void p_abs(void)    { cell a = pop(); push(a < 0 ? -a : a); }
static void p_min(void)    { cell b = pop(), a = pop(); push(a < b ? a : b); }
static void p_max(void)    { cell b = pop(), a = pop(); push(a > b ? a : b); }

static void p_dup(void)    { cell a = pop(); push(a); push(a); }
static void p_drop(void)   { pop(); }
static void p_swap(void)   { cell b = pop(), a = pop(); push(b); push(a); }
static void p_over(void)   { cell b = pop(), a = pop(); push(a); push(b); push(a); }
static void p_rot(void)    { cell c = pop(), b = pop(), a = pop(); push(b); push(c); push(a); }
static void p_nip(void)    { cell b = pop(); pop(); push(b); }
static void p_2dup(void)   { cell b = pop(), a = pop(); push(a); push(b); push(a); push(b); }
static void p_depth(void)  { push(dsp); }

static void p_eq(void)     { cell b = pop(), a = pop(); push(a == b ? -1 : 0); }
static void p_ne(void)     { cell b = pop(), a = pop(); push(a != b ? -1 : 0); }
static void p_lt(void)     { cell b = pop(), a = pop(); push(a <  b ? -1 : 0); }
static void p_gt(void)     { cell b = pop(), a = pop(); push(a >  b ? -1 : 0); }
static void p_zeroeq(void) { push(pop() == 0 ? -1 : 0); }

static void p_and(void)    { cell b = pop(), a = pop(); push(a & b); }
static void p_or(void)     { cell b = pop(), a = pop(); push(a | b); }
static void p_xor(void)    { cell b = pop(), a = pop(); push(a ^ b); }
static void p_invert(void) { push(~pop()); }

static void p_dot(void)    { printf("%lld ", pop()); }
static void p_udot(void)   { printf("%llu ", pop()); }
static void p_cr(void)     { putchar('\n'); }
static void p_emit(void)   { putchar((int)pop()); }
static void p_dots(void) {
    printf("<%d> ", dsp);
    for (int i = 0; i < dsp; i++) printf("%lld ", ds[i]);
}
static void p_i(void) {
    if (rsp < 1) fail("i außerhalb einer do-Schleife");
    push(rs[rsp - 1]);
}
static void p_words(void) {
    for (int i = 0; i < dict_n; i++) printf("%s ", dict[i].name);
    putchar('\n');
}
static void p_j(void) {
    if (rsp < 4) fail("j benötigt zwei verschachtelte do-Schleifen");
    push(rs[rsp - 3]);
}

static void p_inc(void)    { push(pop() + 1); }
static void p_dec(void)    { push(pop() - 1); }
static void p_le(void)     { cell b = pop(), a = pop(); push(a <= b ? -1 : 0); }
static void p_ge(void)     { cell b = pop(), a = pop(); push(a >= b ? -1 : 0); }
static void p_zerolt(void) { push(pop() < 0 ? -1 : 0); }

static void check_addr(cell a) { if (a < 0 || a >= MEM_SIZE) fail("Ungültige Adresse"); }
static void p_fetch(void)  { cell a = pop(); check_addr(a); push(mem[a]); }
static void p_store(void)  { cell a = pop(), v = pop(); check_addr(a); mem[a] = v; }
static void p_pstore(void) { cell a = pop(), v = pop(); check_addr(a); mem[a] += v; }
static void do_allot(cell n) {
    if (n < 0 || here_ptr + n > MEM_SIZE) fail("Speicher voll");
    here_ptr += (int)n;
}
static void p_allot(void)  { do_allot(pop()); }
static void p_here(void)   { push(here_ptr); }
static void p_cells(void)  { /* Adressen sind Zellenindizes: nichts zu tun */ }

static void p_space(void)  { putchar(' '); }
static void p_spaces(void) { cell n = pop(); while (n-- > 0) putchar(' '); }
static void p_page(void) {
    if (isatty(fileno(stdout))) printf("\033[2J\033[H");   /* Bildschirm löschen */
    else putchar('\n');
}
static void p_ms(void) {
    cell n = pop();
    fflush(stdout);
    if (n > 0) usleep((useconds_t)(n * 1000));
}

static void p_dump(void) {
    long long l = pop();
    long long a = pop();
    unsigned char c, *addr = (unsigned char *)a;
    printf("Dump %llu / %llu (0x%llX / 0x%llX):", a, l, a, l);
    for (int i = 0; i < l; i++) {
        if((i%8)==0) printf("\r\n");
        c = *(addr++);
        printf(" %3u (0x%02X - ", c, c);
        if((c <= 0x20) | (c == 127)) c = 0x20;
        printf("%1c)", c);
    }
}

static void p_info(void) {
    printf("Dictionary  at %llu (0x%llX) - %u Entry\r\n", &dict[0], &dict[0], dict_n);
    printf("Datastack   at %llu (0x%llX) - %u Entry\r\n", &ds[0], &ds[0], dsp);
    printf("Returnstack at %llu (0x%llX) - %u Entry\r\n", &rs[0], &rs[0], rsp);
    printf("Memory      at %llu (0x%llX) - %u Entry\r\n", &mem[0], &mem[0], here_ptr);
}

static void p_bye(void)    { running = 0; }

/* ---------- Wörterbuch ---------- */

static void add_prim(const char *name, void (*fn)(void)) {
    strncpy(dict[dict_n].name, name, NAME_LEN - 1);
    dict[dict_n].prim = fn;
    dict_n++;
}

static int find_word(const char *name) {
    for (int i = dict_n - 1; i >= 0; i--)
        if (strcmp(dict[i].name, name) == 0) return i;
    return -1;
}

/* Legt ein Wort an, das nur eine Konstante auf den Stack legt
   (Grundlage für variable, constant und create). */
static void define_literal(const char *name, cell value) {
    if (dict_n >= DICT_MAX) fail("Wörterbuch voll");
    Word *w = &dict[dict_n++];
    memset(w, 0, sizeof *w);
    strncpy(w->name, name, NAME_LEN - 1);
    w->len = 1;
    w->code = malloc(sizeof(Instr));
    w->code[0].op = OP_LIT;
    w->code[0].arg = value;
}

static void init_dict(void) {
    add_prim("+", p_add);       add_prim("-", p_sub);
    add_prim("*", p_mul);       add_prim("/", p_div);
    add_prim("mod", p_mod);     add_prim("negate", p_negate);
    add_prim("abs", p_abs);     add_prim("min", p_min);
    add_prim("max", p_max);
    add_prim("dup", p_dup);     add_prim("drop", p_drop);
    add_prim("swap", p_swap);   add_prim("over", p_over);
    add_prim("rot", p_rot);     add_prim("nip", p_nip);
    add_prim("2dup", p_2dup);   add_prim("depth", p_depth);
    add_prim("=", p_eq);        add_prim("<>", p_ne);
    add_prim("<", p_lt);        add_prim(">", p_gt);
    add_prim("0=", p_zeroeq);
    add_prim("and", p_and);     add_prim("or", p_or);
    add_prim("xor", p_xor);     add_prim("invert", p_invert);
    add_prim(".", p_dot);       add_prim(".s", p_dots);
    add_prim("cr", p_cr);       add_prim("emit", p_emit);
    add_prim("i", p_i);         add_prim("words", p_words);
    add_prim("j", p_j);
    add_prim("1+", p_inc);      add_prim("1-", p_dec);
    add_prim("<=", p_le);       add_prim(">=", p_ge);
    add_prim("0<", p_zerolt);
    add_prim("@", p_fetch);     add_prim("!", p_store);
    add_prim("+!", p_pstore);   add_prim("allot", p_allot);
    add_prim("here", p_here);   add_prim("cells", p_cells);
    add_prim("space", p_space); add_prim("spaces", p_spaces);
    add_prim("page", p_page);   add_prim("ms", p_ms);
    add_prim("bye", p_bye);
    add_prim("dump", p_dump);   add_prim("u.", p_udot);
    add_prim("info", p_info);
}

/* ---------- Ausführung ---------- */

static void exec_word(const Word *w) {
    if (w->prim) { w->prim(); return; }
    if (++depth > MAX_DEPTH) fail("Rekursionstiefe überschritten");

    int ip = 0;
    while (ip < w->len) {
        Instr ins = w->code[ip++];
        switch (ins.op) {
        case OP_LIT:  push(ins.arg); break;
        case OP_CALL: exec_word(&dict[ins.arg]); break;
        case OP_JMP:  ip = (int)ins.arg; break;
        case OP_JZ:   if (pop() == 0) ip = (int)ins.arg; break;
        case OP_DO: {                       /* ( limit start -- ) */
            cell start = pop(), limit = pop();
            rpush(limit); rpush(start);
            break;
        }
        case OP_LOOP: {
            cell idx = rs[rsp - 1] + 1;
            if (idx >= rs[rsp - 2]) rsp -= 2;
            else { rs[rsp - 1] = idx; ip = (int)ins.arg; }
            break;
        }
        case OP_STR:  fputs((const char *)(intptr_t)ins.arg, stdout); break;
        }
    }
    depth--;
}

/* ---------- Kompilieren ---------- */

static void emit_instr(int op, cell arg) {
    if (cur_len >= CODE_MAX) fail("Definition zu lang");
    cur[cur_len].op = op;
    cur[cur_len].arg = arg;
    cur_len++;
}

static void finish_definition(void) {
    if (csp != 0) fail("Kontrollstruktur nicht geschlossen");
    if (dict_n >= DICT_MAX) fail("Wörterbuch voll");
    Word *w = &dict[dict_n++];
    memset(w, 0, sizeof *w);
    strncpy(w->name, cur_name, NAME_LEN - 1);
    w->len  = cur_len;
    w->code = malloc(sizeof(Instr) * (cur_len ? cur_len : 1));
    memcpy(w->code, cur, sizeof(Instr) * cur_len);
    compiling = 0;
}

static void compile_token(const char *tok) {
    cell n;
    char *end;

    if      (!strcmp(tok, ";"))      finish_definition();
    else if (!strcmp(tok, "if"))     { cpush(cur_len); emit_instr(OP_JZ, 0); }
    else if (!strcmp(tok, "else"))   {
        int j = cpop();
        cpush(cur_len); emit_instr(OP_JMP, 0);
        cur[j].arg = cur_len;
    }
    else if (!strcmp(tok, "then"))   cur[cpop()].arg = cur_len;
    else if (!strcmp(tok, "begin"))  cpush(cur_len);
    else if (!strcmp(tok, "until"))  emit_instr(OP_JZ, cpop());
    else if (!strcmp(tok, "while"))  { cpush(cur_len); emit_instr(OP_JZ, 0); }
    else if (!strcmp(tok, "repeat")) {
        int w = cpop(), b = cpop();
        emit_instr(OP_JMP, b);
        cur[w].arg = cur_len;
    }
    else if (!strcmp(tok, "do"))     { emit_instr(OP_DO, 0); cpush(cur_len); }
    else if (!strcmp(tok, "loop"))   emit_instr(OP_LOOP, cpop());
    else if (!strcmp(tok, "recurse")) emit_instr(OP_CALL, dict_n); /* Index des Wortes nach ';' */
    else {
        int idx = find_word(tok);
        if (idx >= 0) { emit_instr(OP_CALL, idx); return; }
        errno = 0;
        n = strtol(tok, &end, 10);
        if (end == tok || *end) { printf("Fehler: Unbekanntes Wort '%s'\n", tok); longjmp(err_env, 1); }
        emit_instr(OP_LIT, n);
    }
}

/* ---------- Interpretieren ---------- */

static void interpret_token(const char *tok) {
    char *end;
    int idx = find_word(tok);
    if (idx >= 0) { exec_word(&dict[idx]); return; }

    errno = 0;
    long long n = strtoll(tok, &end, 0);  // Abwandlung: 0 => 0x für Hex, auch 0b (Basis 2) oder 0 (Basis 8) erlaubt, sonst Basis 10
    if (end == tok || *end) { printf("Fehler: Unbekanntes Wort '%s'\n", tok); longjmp(err_env, 1); }
    push(n);
}

static int next_token(char *buf) {
    while (*src && isspace((unsigned char)*src)) src++;
    if (!*src) return 0;
    int n = 0;
    while (*src && !isspace((unsigned char)*src)) {
        if (n < TOK_LEN - 1) buf[n++] = *src;
        src++;
    }
    buf[n] = '\0';
    return 1;
}

static void interpret_line(const char *line) {
    char tok[TOK_LEN];
    src = line;

    while (next_token(tok)) {
        for (char *p = tok; *p; p++) *p = (char)tolower((unsigned char)*p);

        if (!strcmp(tok, "\\")) break;                      /* Zeilenkommentar */
        if (!strcmp(tok, "(")) {                            /* Kommentar bis ')' */
            const char *e = strchr(src, ')');
            if (!e) fail("')' fehlt");
            src = e + 1;
            continue;
        }
        if (!strcmp(tok, ".\"")) {                          /* ." text" */
            if (*src) src++;
            const char *e = strchr(src, '"');
            if (!e) fail("'\"' fehlt");
            size_t len = (size_t)(e - src);
            char *s = malloc(len + 1);
            memcpy(s, src, len); s[len] = '\0';
            src = e + 1;
            if (compiling) emit_instr(OP_STR, (cell)(intptr_t)s);   /* bleibt bewusst allokiert */
            else { fputs(s, stdout); free(s); }
            continue;
        }
        if (!compiling && (!strcmp(tok, "variable") || !strcmp(tok, "constant") ||
                           !strcmp(tok, "create"))) {
            int kind = !strcmp(tok, "variable") ? 0 : !strcmp(tok, "constant") ? 1 : 2;
            if (!next_token(tok)) fail("Name fehlt");
            for (char *p = tok; *p; p++) *p = (char)tolower((unsigned char)*p);
            if (kind == 0)      { define_literal(tok, here_ptr); do_allot(1); }
            else if (kind == 1) define_literal(tok, pop());
            else                define_literal(tok, here_ptr);
            continue;
        }
        if (!compiling && !strcmp(tok, ":")) {
            if (!next_token(tok)) fail("Name nach ':' fehlt");
            for (char *p = tok; *p; p++) *p = (char)tolower((unsigned char)*p);
            strncpy(cur_name, tok, NAME_LEN - 1);
            cur_name[NAME_LEN - 1] = '\0';
            compiling = 1; cur_len = 0; csp = 0;
            continue;
        }
/* Debug-Erweiterung SEE */
        if (!compiling && !strcmp(tok, "see")) {
            if (!next_token(tok)) fail("Name nach 'see' fehlt");
            for (char *p = tok; *p; p++) *p = (char)tolower((unsigned char)*p);
            int idx = find_word(tok);
            if (idx >= 0) {
                Word *w = &dict[idx];
                printf("Num: %3u (0x%llX), Prim: %llu (0x%llX), Instr: %llu (0x%llX), Len: %u\r\n", idx, &dict[idx], w->prim, w->prim, w->code, w->code, w->len);
                Instr *inst = w->code;
                for(int i = 0; i < (w->len); i++) {
                    printf(" %u - %llu\r\n", inst->op, inst->arg);
                    inst++;
                }
               return;
            }
            else fail("Unbekanntes Wort");
            continue;
        }
/* End Debug-Erweiterung SEE */
        if (compiling) compile_token(tok);
        else           interpret_token(tok);
    }
}

/* ---------- Hauptprogramm ---------- */

static void repl(FILE *f, int tty) {
    char line[512];
    while (running && fgets(line, sizeof line, f)) {
        if (setjmp(err_env)) {            /* Fehler: Zustand zurücksetzen */
            dsp = rsp = csp = depth = 0;
            compiling = 0;
        } else {
            interpret_line(line);
        }
        if (tty && running && !compiling) puts(" ok");
    }
}

int main(int argc, char **argv) {
    int tty = isatty(fileno(stdin));
    init_dict();

    if (argc > 1) {                       /* Datei laden */
        FILE *f = fopen(argv[1], "r");
        if (!f) { perror(argv[1]); return 1; }
        repl(f, 0);
        fclose(f);
        if (!tty) return 0;
    }
    if (tty && running) puts("Mini-Forth. 'words' zeigt alle Wörter, 'bye' beendet.");
    repl(stdin, tty);
    return 0;
}
