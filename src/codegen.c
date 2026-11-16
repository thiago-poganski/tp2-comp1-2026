#include <ctype.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "codegen.h"
#include "microc_mapa.h"
#include "util.h"

/* ------------------------------------------------------------------ */
/* Emissao de texto                                                   */
/* ------------------------------------------------------------------ */

typedef struct {
    FILE *f;
    int nivel;          /* nivel de indentacao (4 espacos por nivel) */
} Emissor;

/* Emite uma linha indentada; fmt segue printf. */
static void emit(Emissor *em, const char *fmt, ...)
{
    int i;
    va_list ap;
    for (i = 0; i < em->nivel; i++)
        fputs("    ", em->f);
    va_start(ap, fmt);
    vfprintf(em->f, fmt, ap);
    va_end(ap);
    fputc('\n', em->f);
}

/* Emite linhas fixas, sem interpretar '%'. A lista termina em NULL. */
static void emit_linhas(FILE *f, const char *const *linhas)
{
    for (; *linhas != NULL; linhas++) {
        fputs(*linhas, f);
        fputc('\n', f);
    }
}

/* Texto dentro de comentario C: evita fechar o comentario por engano. */
static void emitir_comentario(FILE *f, const char *s)
{
    for (; *s != '\0'; s++) {
        if (s[0] == '*' && s[1] == '/') {
            fputs("* /", f);
            s++;
        } else if (*s == '\n') {
            fputc(' ', f);
        } else {
            fputc(*s, f);
        }
    }
}

/* String C entre aspas, com escapes. */
static void emitir_string_c(FILE *f, const char *s)
{
    fputc('"', f);
    for (; *s != '\0'; s++) {
        unsigned char c = (unsigned char) *s;
        if (c == '"' || c == '\\')
            fprintf(f, "\\%c", c);
        else if (c == '\n')
            fputs("\\n", f);
        else if (c == '\t')
            fputs("\\t", f);
        else if (c < 32 || c > 126)
            fprintf(f, "\\%03o", c);
        else
            fputc(c, f);
    }
    fputc('"', f);
}

/* ------------------------------------------------------------------ */
/* Nomes dos tokens no codigo gerado                                  */
/* ------------------------------------------------------------------ */

static const char *const nomes_simbolos[][2] = {
    { "+", "MAIS" }, { "-", "MENOS" }, { "*", "VEZES" }, { "/", "BARRA" },
    { "%", "PORCENTO" }, { "(", "ABRE_PAR" }, { ")", "FECHA_PAR" },
    { "[", "ABRE_COL" }, { "]", "FECHA_COL" }, { "{", "ABRE_CHAVE" },
    { "}", "FECHA_CHAVE" }, { ";", "PV" }, { ",", "VIRGULA" },
    { ".", "PONTO" }, { ":", "DOIS_PONTOS" }, { "=", "IGUAL" },
    { "==", "IGUAL_IGUAL" }, { "!=", "DIFERENTE" }, { "<", "MENOR" },
    { ">", "MAIOR" }, { "<=", "MENOR_IGUAL" }, { ">=", "MAIOR_IGUAL" },
    { "&&", "E_LOGICO" }, { "||", "OU_LOGICO" }, { "!", "NAO" },
    { ":=", "ATRIBUICAO" }, { "->", "SETA" }
};

static int eh_palavra(const char *s)
{
    if (!isalpha((unsigned char) *s) && *s != '_')
        return 0;
    for (; *s != '\0'; s++)
        if (!isalnum((unsigned char) *s) && *s != '_')
            return 0;
    return 1;
}

static int nome_em_uso(const Gramatica *g, int ate, const char *nome)
{
    int i;
    for (i = 0; i < ate; i++)
        if (strcmp(g->terms[i].nome_c, nome) == 0)
            return 1;
    return 0;
}

/* Define g->terms[i].nome_c para todos os terminais. */
static void nomear_terminais(Gramatica *g, int microc)
{
    int i;
    size_t k;
    char buf[256];
    Terminal *t;

    for (i = 0; i < g->nterms; i++) {
        t = &g->terms[i];
        free(t->nome_c);
        if (i == TERM_FIM) {
            t->nome_c = xstrdup(microc ? "END_OF_FILE" : "T_FIM");
            continue;
        }
        if (microc) {
            t->nome_c = xstrdup(t->literal ? microc_nome_literal(t->nome) : t->nome);
            continue;
        }
        buf[0] = '\0';
        if (!t->literal) {
            sprintf(buf, "T_%.200s", t->nome);
        } else if (eh_palavra(t->nome) && strlen(t->nome) < 200) {
            sprintf(buf, "T_%s", t->nome);
            for (k = 2; buf[k] != '\0'; k++)
                buf[k] = (char) toupper((unsigned char) buf[k]);
        } else {
            for (k = 0; k < sizeof(nomes_simbolos) / sizeof(nomes_simbolos[0]); k++)
                if (strcmp(nomes_simbolos[k][0], t->nome) == 0)
                    sprintf(buf, "T_%s", nomes_simbolos[k][1]);
            if (buf[0] == '\0')
                sprintf(buf, "T_LIT_%d", i);
        }
        if (nome_em_uso(g, i, buf))
            sprintf(buf + strlen(buf), "_%d", i);
        t->nome_c = xstrdup(buf);
    }
}

/* ------------------------------------------------------------------ */
/* Conjuntos constantes                                               */
/* ------------------------------------------------------------------ */

#define MAX_COMPARACOES 3   /* ate 3 tokens: tok.tipo == A || ...; acima: pertence */

static Bitset *conjuntos = NULL;
static int nconj = 0, capconj = 0;

static int bitset_igual(const Bitset *a, const Bitset *b)
{
    int i;
    for (i = 0; i < a->n; i++)
        if (bitset_tem(a, i) != bitset_tem(b, i))
            return 0;
    return 1;
}

/* Registra um conjunto e devolve seu numero N (emitido como conj_N).
 * Conjuntos iguais compartilham a mesma constante. */
static int registrar_conjunto(const Bitset *b)
{
    int i;
    for (i = 0; i < nconj; i++)
        if (bitset_igual(&conjuntos[i], b))
            return i;
    if (nconj == capconj) {
        capconj = capconj ? 2 * capconj : 16;
        conjuntos = (Bitset *) xrealloc(conjuntos, (size_t) capconj * sizeof(Bitset));
    }
    bitset_iniciar(&conjuntos[nconj], b->n);
    bitset_copiar(&conjuntos[nconj], b);
    return nconj++;
}

static void liberar_conjuntos(void)
{
    int i;
    for (i = 0; i < nconj; i++)
        bitset_liberar(&conjuntos[i]);
    free(conjuntos);
    conjuntos = NULL;
    nconj = capconj = 0;
}

static void emitir_conjuntos(FILE *f, const Gramatica *g)
{
    int i, t;
    for (i = 0; i < nconj; i++) {
        fprintf(f, "static const int conj_%d[] = { ", i);
        for (t = bitset_proximo(&conjuntos[i], 0); t >= 0;
             t = bitset_proximo(&conjuntos[i], t + 1))
            fprintf(f, "%s, ", g->terms[t].nome_c);
        fputs("-1 };\n", f);
    }
}

/* Escreve a condicao "o token corrente pertence a b":
 *   tok.tipo == T_A                     (um token)
 *   tok.tipo == T_A || tok.tipo == T_B  (ate MAX_COMPARACOES)
 *   pertence(tok.tipo, conj_N)          (mais tokens) */
static void emitir_teste(FILE *f, const Gramatica *g, const Bitset *b)
{
    int t, n = bitset_tamanho(b), primeiro = 1;
    if (n == 0) {
        fputs("0", f);
    } else if (n <= MAX_COMPARACOES) {
        for (t = bitset_proximo(b, 0); t >= 0; t = bitset_proximo(b, t + 1)) {
            fprintf(f, "%stok.tipo == %s", primeiro ? "" : " || ", g->terms[t].nome_c);
            primeiro = 0;
        }
    } else {
        fprintf(f, "pertence(tok.tipo, conj_%d)", registrar_conjunto(b));
    }
}

/* Linha "<antes><teste><depois>", ex.: emit_teste(em, "while (", g, b, ") {") */
static void emit_teste(Emissor *em, const char *antes, const Gramatica *g,
                       const Bitset *b, const char *depois)
{
    int i;
    for (i = 0; i < em->nivel; i++)
        fputs("    ", em->f);
    fputs(antes, em->f);
    emitir_teste(em->f, g, b);
    fputs(depois, em->f);
    fputc('\n', em->f);
}

/* Linha "erro_sintatico(conj_N);" com N = conjunto dos tokens esperados. */
static void emit_erro(Emissor *em, const Bitset *esperados)
{
    emit(em, "erro_sintatico(conj_%d);", registrar_conjunto(esperados));
}

static void gen_expr(Emissor *em, const Gramatica *g, const Expr *e)
{
    int i, primeiro;
    const Expr *a, *anulavel;

    switch (e->tipo) {
    case E_TERM:
        emit(em, "match(%s);", g->terms[e->simbolo].nome_c);
        break;
    case E_NAOTERM:
        emit(em, "parse_%s();", g->nts[e->simbolo].nome);
        break;
    case E_SEQ:
        for (i = 0; i < e->nfilhos; i++)
            gen_expr(em, g, e->filhos[i]);
        break;
    case E_ALT:
        primeiro = 1;
        anulavel = NULL;
        for (i = 0; i < e->nfilhos; i++) {
            a = e->filhos[i];
            if (a->anulavel) {
                anulavel = a;
                continue;
            }
            emit_teste(em, primeiro ? "if (" : "} else if (", g, &a->first, ") {");
            em->nivel++;
            gen_expr(em, g, a);
            em->nivel--;
            primeiro = 0;
        }
        if (primeiro) {
            if (anulavel != NULL)
                gen_expr(em, g, anulavel);
        } else if (anulavel == NULL) {
            emit(em, "} else {");
            em->nivel++;
            emit_erro(em, &e->first);
            em->nivel--;
            emit(em, "}");
        } else if (anulavel->tipo == E_VAZIO) {
            emit(em, "}");
        } else {
            emit(em, "} else {");
            em->nivel++;
            gen_expr(em, g, anulavel);
            em->nivel--;
            emit(em, "}");
        }
        break;
    case E_OPC:
        emit_teste(em, "if (", g, &e->filhos[0]->first, ") {");
        em->nivel++;
        gen_expr(em, g, e->filhos[0]);
        em->nivel--;
        emit(em, "}");
        break;
    case E_REP:
        emit_teste(em, "while (", g, &e->filhos[0]->first, ") {");
        em->nivel++;
        gen_expr(em, g, e->filhos[0]);
        em->nivel--;
        emit(em, "}");
        break;
    case E_VAZIO:
        break;
    }
}


/* ------------------------------------------------------------------ */
/* Expressoes regulares de TOKENS (modo proprio)                      */
/* ------------------------------------------------------------------ */

typedef struct {
    int eps[2];
    int neps;
    int alvo;
    unsigned char classe[32];
} EstadoAfn;

typedef struct {
    EstadoAfn *e;
    int n, cap;
    const char *re;
    size_t pos;
    const char *erro;
} Afn;

typedef struct {
    int ini, fim;
} Frag;

static int afn_novo(Afn *a)
{
    if (a->n == a->cap) {
        a->cap = a->cap ? 2 * a->cap : 32;
        a->e = (EstadoAfn *) xrealloc(a->e, (size_t) a->cap * sizeof(EstadoAfn));
    }
    memset(&a->e[a->n], 0, sizeof(EstadoAfn));
    a->e[a->n].alvo = -1;
    return a->n++;
}

static void afn_eps(Afn *a, int de, int para)
{
    a->e[de].eps[a->e[de].neps++] = para;
}

static void classe_add(unsigned char *cl, int c)
{
    cl[c >> 3] |= (unsigned char) (1 << (c & 7));
}

static int classe_tem(const unsigned char *cl, int c)
{
    return (cl[c >> 3] >> (c & 7)) & 1;
}

static int re_escape(char c)
{
    switch (c) {
    case 'n': return '\n';
    case 't': return '\t';
    case 'r': return '\r';
    case 'f': return '\f';
    case 'v': return '\v';
    default:  return (unsigned char) c;
    }
}

static int re_char(Afn *a)
{
    int c = (unsigned char) a->re[a->pos];
    if (c == '\\') {
        a->pos++;
        if (a->re[a->pos] == '\0') {
            a->erro = "barra invertida no fim da expressao";
            return -1;
        }
        c = re_escape(a->re[a->pos]);
    }
    a->pos++;
    return c;
}

static Frag frag_classe(Afn *a, const unsigned char *cl)
{
    Frag f;
    f.ini = afn_novo(a);
    f.fim = afn_novo(a);
    memcpy(a->e[f.ini].classe, cl, 32);
    a->e[f.ini].alvo = f.fim;
    return f;
}

static Frag re_alt(Afn *a);

static Frag re_atomo(Afn *a)
{
    unsigned char cl[32];
    int c, d, i, negar;
    Frag f;

    memset(cl, 0, sizeof cl);
    c = (unsigned char) a->re[a->pos];
    if (c == '(') {
        a->pos++;
        f = re_alt(a);
        if (a->erro == NULL && a->re[a->pos] != ')')
            a->erro = "falta ')'";
        else if (a->erro == NULL)
            a->pos++;
        return f;
    }
    if (c == '[') {
        a->pos++;
        negar = 0;
        if (a->re[a->pos] == '^') {
            negar = 1;
            a->pos++;
        }
        if (a->re[a->pos] == ']') {
            classe_add(cl, ']');
            a->pos++;
        }
        while (a->re[a->pos] != ']') {
            if (a->re[a->pos] == '\0') {
                a->erro = "classe [ ] nao fechada";
                return frag_classe(a, cl);
            }
            c = re_char(a);
            if (c < 0)
                return frag_classe(a, cl);
            if (a->re[a->pos] == '-' && a->re[a->pos + 1] != ']' && a->re[a->pos + 1] != '\0') {
                a->pos++;
                d = re_char(a);
                if (d < 0)
                    return frag_classe(a, cl);
                if (d < c) {
                    a->erro = "faixa invertida em [ ]";
                    return frag_classe(a, cl);
                }
                for (i = c; i <= d; i++)
                    classe_add(cl, i);
            } else {
                classe_add(cl, c);
            }
        }
        a->pos++;
        if (negar)
            for (i = 0; i < 32; i++)
                cl[i] = (unsigned char) ~cl[i];
        return frag_classe(a, cl);
    }
    if (c == '.') {
        a->pos++;
        for (i = 1; i < 256; i++)
            if (i != '\n')
                classe_add(cl, i);
        return frag_classe(a, cl);
    }
    if (c == '\0' || c == '|' || c == ')' || c == '*' || c == '+' || c == '?') {
        a->erro = "operando ausente";
        return frag_classe(a, cl);
    }
    c = re_char(a);
    if (c >= 0)
        classe_add(cl, c);
    return frag_classe(a, cl);
}

static Frag re_repeticao(Afn *a)
{
    Frag f = re_atomo(a), r;
    char op;

    while (a->erro == NULL &&
           ((op = a->re[a->pos]) == '*' || op == '+' || op == '?')) {
        a->pos++;
        r.fim = afn_novo(a);
        if (op == '+') {
            r.ini = f.ini;
            afn_eps(a, f.fim, f.ini);
            afn_eps(a, f.fim, r.fim);
        } else {
            r.ini = afn_novo(a);
            afn_eps(a, r.ini, f.ini);
            afn_eps(a, r.ini, r.fim);
            if (op == '*')
                afn_eps(a, f.fim, f.ini);
            afn_eps(a, f.fim, r.fim);
        }
        f = r;
    }
    return f;
}

static Frag re_concat(Afn *a)
{
    Frag f, g;
    char c = a->re[a->pos];

    if (c == '\0' || c == '|' || c == ')') {
        f.ini = f.fim = afn_novo(a);
        return f;
    }
    f = re_repeticao(a);
    while (a->erro == NULL && (c = a->re[a->pos]) != '\0' && c != '|' && c != ')') {
        g = re_repeticao(a);
        afn_eps(a, f.fim, g.ini);
        f.fim = g.fim;
    }
    return f;
}

static Frag re_alt(Afn *a)
{
    Frag f = re_concat(a), g, r;

    while (a->erro == NULL && a->re[a->pos] == '|') {
        a->pos++;
        g = re_concat(a);
        r.ini = afn_novo(a);
        r.fim = afn_novo(a);
        afn_eps(a, r.ini, f.ini);
        afn_eps(a, r.ini, g.ini);
        afn_eps(a, f.fim, r.fim);
        afn_eps(a, g.fim, r.fim);
        f = r;
    }
    return f;
}

static void fecho_eps(const Afn *a, Bitset *b, int *pilha)
{
    int topo = 0, s, i, t;

    for (s = bitset_proximo(b, 0); s >= 0; s = bitset_proximo(b, s + 1))
        pilha[topo++] = s;
    while (topo > 0) {
        s = pilha[--topo];
        for (i = 0; i < a->e[s].neps; i++) {
            t = a->e[s].eps[i];
            if (!bitset_tem(b, t)) {
                bitset_add(b, t);
                pilha[topo++] = t;
            }
        }
    }
}

static void emitir_automato(FILE *f, const char *nome, int nafd, const int *trans,
                            const char *final)
{
    int d, c, lo, t, primeiro;

    fprintf(f, "static size_t %s(const char *s)\n{\n", nome);
    fputs("    static const char final[] = { ", f);
    for (d = 0; d < nafd; d++)
        fprintf(f, "%d, ", final[d]);
    fputs("0 };\n", f);
    fputs("    size_t i = 0, ultimo = 0;\n    int estado = 0, c;\n\n", f);
    fputs("    for (;;) {\n        c = (unsigned char) s[i];\n        switch (estado) {\n", f);
    for (d = 0; d < nafd; d++) {
        fprintf(f, "        case %d:\n", d);
        primeiro = 1;
        for (c = 1; c < 256; c++) {
            t = trans[d * 256 + c];
            if (t < 0)
                continue;
            lo = c;
            while (c + 1 < 256 && trans[d * 256 + c + 1] == t)
                c++;
            if (lo == c)
                fprintf(f, "            %sif (c == %d)\n", primeiro ? "" : "else ", lo);
            else
                fprintf(f, "            %sif (c >= %d && c <= %d)\n", primeiro ? "" : "else ",
                        lo, c);
            fprintf(f, "                estado = %d;\n", t);
            primeiro = 0;
        }
        if (primeiro)
            fputs("            return ultimo;\n", f);
        else
            fputs("            else\n                return ultimo;\n            break;\n", f);
    }
    fputs("        default:\n            return ultimo;\n        }\n", f);
    fputs("        i++;\n        if (final[estado])\n            ultimo = i;\n    }\n}\n\n", f);
}

static int gen_casamento_regex(FILE *f, const char *nome, const char *regex)
{
    Afn a;
    Frag fr;
    Bitset *estados = NULL, mov;
    int *trans = NULL, *pilha;
    char *final = NULL;
    int nafd = 0, cap = 0, d, c, s, k;

    memset(&a, 0, sizeof a);
    a.re = regex;
    fr = re_alt(&a);
    if (a.erro == NULL && a.re[a.pos] != '\0')
        a.erro = "')' sem '(' correspondente";
    if (a.erro != NULL) {
        diag_erro(0, 0, "expressao regular invalida /%s/: %s", regex, a.erro);
        free(a.e);
        fprintf(f, "static size_t %s(const char *s)\n{\n    (void) s;\n    return 0;\n}\n\n",
                nome);
        return 1;
    }

    pilha = (int *) xmalloc((size_t) a.n * sizeof(int));
    bitset_iniciar(&mov, a.n);
    cap = 16;
    estados = (Bitset *) xmalloc((size_t) cap * sizeof(Bitset));
    trans = (int *) xmalloc((size_t) cap * 256 * sizeof(int));
    final = (char *) xmalloc((size_t) cap);
    bitset_iniciar(&estados[0], a.n);
    bitset_add(&estados[0], fr.ini);
    fecho_eps(&a, &estados[0], pilha);
    nafd = 1;

    for (d = 0; d < nafd; d++) {
        final[d] = (char) bitset_tem(&estados[d], fr.fim);
        trans[d * 256] = -1;
        for (c = 1; c < 256; c++) {
            bitset_limpar(&mov);
            for (s = bitset_proximo(&estados[d], 0); s >= 0;
                 s = bitset_proximo(&estados[d], s + 1))
                if (a.e[s].alvo >= 0 && classe_tem(a.e[s].classe, c))
                    bitset_add(&mov, a.e[s].alvo);
            if (bitset_vazio(&mov)) {
                trans[d * 256 + c] = -1;
                continue;
            }
            fecho_eps(&a, &mov, pilha);
            for (k = 0; k < nafd; k++)
                if (bitset_igual(&estados[k], &mov))
                    break;
            if (k == nafd) {
                if (nafd == cap) {
                    cap *= 2;
                    estados = (Bitset *) xrealloc(estados, (size_t) cap * sizeof(Bitset));
                    trans = (int *) xrealloc(trans, (size_t) cap * 256 * sizeof(int));
                    final = (char *) xrealloc(final, (size_t) cap);
                }
                bitset_iniciar(&estados[nafd], a.n);
                bitset_copiar(&estados[nafd], &mov);
                nafd++;
            }
            trans[d * 256 + c] = k;
        }
    }

    emitir_automato(f, nome, nafd, trans, final);

    for (d = 0; d < nafd; d++)
        bitset_liberar(&estados[d]);
    free(estados);
    free(trans);
    free(final);
    free(pilha);
    bitset_liberar(&mov);
    free(a.e);
    return 0;
}


static void gen_token_de_arquivo(FILE *f, int microc)
{
    static const char *const inicio[] = {
        "static Token token_de_arquivo(void)",
        "{",
        "    static int num_linha = 0, ultima_linha = 1;",
        "    char buf[512];",
        "    char *ini, *fim, *p;",
        "    int tipo, linha;",
        "    size_t n;",
        "    Token t;",
        "",
        "    memset(&t, 0, sizeof t);",
        "    while (fgets(buf, sizeof buf, arquivo_tokens) != NULL) {",
        "        num_linha++;",
        "        n = strlen(buf);",
        "        while (n > 0 && (buf[n - 1] == '\\n' || buf[n - 1] == '\\r' ||",
        "                         buf[n - 1] == ' ' || buf[n - 1] == '\\t'))",
        "            buf[--n] = '\\0';",
        "        if (n == 0)",
        "            continue;",
        "        ini = strstr(buf, \"lexema = '\");",
        "        fim = NULL;",
        "        for (p = strstr(buf, \"', linha = \"); p != NULL; p = strstr(p + 1, \"', linha = \"))",
        "            fim = p;",
        "        if (sscanf(buf, \"Token: tipo = %d,\", &tipo) != 1 || ini == NULL ||",
        "            fim == NULL || fim < ini + 10 || sscanf(fim, \"', linha = %d\", &linha) != 1) {",
        "            fprintf(stderr, \"arquivo de tokens, linha %d: linha malformada: %s\\n\",",
        "                    num_linha, buf);",
        "            exit(EXIT_FAILURE);",
        "        }",
        "        ini += 10;",
        "        n = (size_t) (fim - ini);",
        "        if (n >= sizeof t.lexema)",
        "            n = sizeof t.lexema - 1;",
        "        memcpy(t.lexema, ini, n);",
        "        t.lexema[n] = '\\0';",
        NULL
    };
    static const char *const fim_proprio[] = {
        "        t.tipo = tipo;",
        "        t.linha = linha;",
        "        ultima_linha = linha;",
        "        return t;",
        "    }",
        "    t.tipo = TOKEN_FIM;",
        "    t.linha = ultima_linha;",
        "    return t;",
        "}",
        "",
        NULL
    };
    static const char *const fim_microc[] = {
        "        t.tipo = (TokenType) tipo;",
        "        t.linha = linha;",
        "        ultima_linha = linha;",
        "        return t;",
        "    }",
        "    t.tipo = TOKEN_FIM;",
        "    t.linha = ultima_linha;",
        "    return t;",
        "}",
        "",
        NULL
    };
    char lit[2];
    const char *nome;
    int c;

    emit_linhas(f, inicio);
    if (microc) {
        fputs("        if (tipo > (int) PRINT) {\n            switch (tipo) {\n", f);
        lit[1] = '\0';
        for (c = 33; c < 127; c++) {
            lit[0] = (char) c;
            nome = microc_nome_literal(lit);
            if (nome != NULL)
                fprintf(f, "            case %d: tipo = %s; break;\n", c, nome);
        }
        fputs("            default: break;\n            }\n        }\n", f);
        emit_linhas(f, fim_microc);
    } else {
        emit_linhas(f, fim_proprio);
    }
}


/* ------------------------------------------------------------------ */
/* Partes fixas do codigo gerado                                      */
/* ------------------------------------------------------------------ */

static const char *const rt_estado[] = {
    "/* ---- estado do analisador ---- */",
    "",
    "static Token tok;                  /* token corrente (lookahead) */",
    "static int imprimir_arvore = 0;    /* opcao --tree */",
    "static int nivel_arvore = 0;",
    "static FILE *arquivo_tokens = NULL; /* opcao --tokens */",
    "",
    "static Token token_de_arquivo(void);",
    "",
    NULL
};

static const char *const rt_primitivas[] = {
    "/* ---- primitivas ---- */",
    "",
    "int pertence(int tipo, const int *conjunto)",
    "{",
    "    for (; *conjunto != -1; conjunto++)",
    "        if (*conjunto == tipo)",
    "            return 1;",
    "    return 0;",
    "}",
    "",
    "/* Reporta o erro com os tokens esperados (lista terminada em -1) e encerra. */",
    "void erro_sintatico(const int *esperados)",
    "{",
    "    int i;",
    "    escrever_posicao();",
    "    if ((int) tok.tipo == TOKEN_FIM)",
    "        fprintf(stderr, \"encontrado fim de arquivo, \");",
    "    else",
    "        fprintf(stderr, \"encontrado '%s', \", tok.lexema);",
    "    if (esperados[0] != -1 && esperados[1] == -1) {",
    "        fprintf(stderr, \"esperado %s\\n\", nome_token(esperados[0]));",
    "    } else {",
    "        fprintf(stderr, \"esperado um de {\");",
    "        for (i = 0; esperados[i] != -1; i++)",
    "            fprintf(stderr, \"%s%s\", i > 0 ? \", \" : \"\", nome_token(esperados[i]));",
    "        fprintf(stderr, \"}\\n\");",
    "    }",
    "    exit(EXIT_FAILURE);",
    "}",
    "",
    "static void recuo(void)",
    "{",
    "    int i;",
    "    for (i = 0; i < nivel_arvore; i++)",
    "        fputs(\"  \", stdout);",
    "}",
    "",
    "void arvore_entra(const char *nao_terminal)",
    "{",
    "    if (imprimir_arvore) {",
    "        recuo();",
    "        printf(\"%s\\n\", nao_terminal);",
    "    }",
    "    nivel_arvore++;",
    "}",
    "",
    "void arvore_sai(void)",
    "{",
    "    nivel_arvore--;",
    "}",
    "",
    "/* Consome o token corrente se for do tipo esperado; senao, erro. */",
    "void match(int esperado)",
    "{",
    "    int lista[2];",
    "    if ((int) tok.tipo != esperado) {",
    "        lista[0] = esperado;",
    "        lista[1] = -1;",
    "        erro_sintatico(lista);",
    "    }",
    "    if (SUPORTE_ARVORE && imprimir_arvore) {",
    "        recuo();",
    "        if (nome_token(tok.tipo)[0] == '\\'')",
    "            printf(\"%s\\n\", nome_token(tok.tipo));",
    "        else",
    "            printf(\"%s '%s'\\n\", nome_token(tok.tipo), tok.lexema);",
    "    }",
    "    avancar();",
    "}",
    "",
    NULL
};

/* Lexico proprio: partes fixas antes e depois das funcoes de regex. */
static const char *const rt_lexico_estado[] = {
    "/* ---- analisador lexico gerado a partir de TOKENS ---- */",
    "",
    "static char *fonte = NULL;",
    "static size_t pos = 0;",
    "static int linha = 1, coluna = 1;",
    "",
    "static char *ler_tudo(FILE *f)",
    "{",
    "    size_t cap = 4096, n = 0, lidos;",
    "    char *buf = (char *) malloc(cap), *novo;",
    "    if (buf == NULL) {",
    "        fprintf(stderr, \"memoria insuficiente\\n\");",
    "        exit(EXIT_FAILURE);",
    "    }",
    "    while ((lidos = fread(buf + n, 1, cap - n - 1, f)) > 0) {",
    "        n += lidos;",
    "        if (cap - n - 1 == 0) {",
    "            cap *= 2;",
    "            novo = (char *) realloc(buf, cap);",
    "            if (novo == NULL) {",
    "                fprintf(stderr, \"memoria insuficiente\\n\");",
    "                exit(EXIT_FAILURE);",
    "            }",
    "            buf = novo;",
    "        }",
    "    }",
    "    buf[n] = '\\0';",
    "    return buf;",
    "}",
    "",
    "static void consumir(size_t n)",
    "{",
    "    for (; n > 0 && fonte[pos] != '\\0'; n--, pos++) {",
    "        if (fonte[pos] == '\\n') {",
    "            linha++;",
    "            coluna = 1;",
    "        } else {",
    "            coluna++;",
    "        }",
    "    }",
    "}",
    "",
    NULL
};

static void escrever_cabecalho_c(FILE *f, const OpcoesGeracao *op)
{
    fputs("/*\n * Analisador sintatico descendente recursivo gerado a partir de ", f);
    emitir_comentario(f, op->origem);
    fputs(".\n * Arquivo gerado automaticamente: nao edite.\n */\n", f);
}

/* ------------------------------------------------------------------ */
/* Arquivo .h                                                         */
/* ------------------------------------------------------------------ */

static int gerar_h(const Gramatica *g, const OpcoesGeracao *op)
{
    char *caminho = (char *) xmalloc(strlen(op->prefixo) + 3);
    FILE *f;
    int i;

    sprintf(caminho, "%s.h", op->prefixo);
    f = fopen(caminho, "w");
    if (f == NULL) {
        diag_erro(0, 0, "nao foi possivel criar %s", caminho);
        free(caminho);
        return -1;
    }
    escrever_cabecalho_c(f, op);
    fputs("#ifndef PARSER_GERADO_H\n#define PARSER_GERADO_H\n\n", f);
    if (op->microc) {
        fputs("#include \"scanner.h\"   /* scanner do TP1: Token, TokenType, proximo_token */\n\n", f);
        fputs("#define TOKEN_FIM END_OF_FILE\n\n", f);
    } else {
        fputs("typedef enum {\n", f);
        for (i = 0; i < g->nterms; i++) {
            fprintf(f, "    %s%s   /* ", g->terms[i].nome_c, i + 1 < g->nterms ? "," : "");
            emitir_comentario(f, g->terms[i].exibicao);
            fputs(" */\n", f);
        }
        fputs("} TipoToken;\n\n", f);
        fputs("typedef struct {\n    int tipo;\n    char lexema[100];\n"
              "    int linha;\n    int coluna;\n} Token;\n\n", f);
        fputs("#define TOKEN_FIM T_FIM\n\n", f);
    }
    fputs("const char *nome_token(int tipo);\n", f);
    fputs("int  pertence(int tipo, const int *conjunto);\n", f);
    fputs("void avancar(void);\n", f);
    fputs("void match(int esperado);\n", f);
    fputs("void erro_sintatico(const int *esperados);\n", f);
    fputs("void arvore_entra(const char *nao_terminal);\n", f);
    fputs("void arvore_sai(void);\n\n", f);
    for (i = 0; i < g->nnts; i++)
        if (g->nts[i].regra != NULL)
            fprintf(f, "void parse_%s(void);\n", g->nts[i].nome);
    fputs("\n#endif\n", f);
    fclose(f);
    free(caminho);
    return 0;
}

/* ------------------------------------------------------------------ */
/* Arquivo .c                                                         */
/* ------------------------------------------------------------------ */

static void gerar_nome_token(FILE *f, const Gramatica *g)
{
    int i;
    fputs("const char *nome_token(int tipo)\n{\n    switch (tipo) {\n", f);
    for (i = 0; i < g->nterms; i++) {
        fprintf(f, "    case %s: return ", g->terms[i].nome_c);
        emitir_string_c(f, i == TERM_FIM ? "fim de arquivo" : g->terms[i].exibicao);
        fputs(";\n", f);
    }
    fputs("    default: return \"token desconhecido\";\n    }\n}\n\n", f);
}

static void gerar_posicao_e_avancar(FILE *f, int microc)
{
    fputs("static void escrever_posicao(void)\n{\n", f);
    if (microc)
        fputs("    fprintf(stderr, \"linha %d: \", tok.linha);\n", f);
    else
        fputs("    fprintf(stderr, \"linha %d, coluna %d: \", tok.linha, tok.coluna);\n", f);
    fputs("}\n\n", f);

    fputs("/* Le o proximo token para tok. */\nvoid avancar(void)\n{\n", f);
    fputs("    if (arquivo_tokens != NULL)\n        tok = token_de_arquivo();\n    else\n", f);
    if (microc) {
        fputs("        tok = proximo_token();\n", f);
        fputs("    if (tok.tipo == UNDEF) {\n", f);
        fputs("        fprintf(stderr, \"linha %d: erro lexico: %s\\n\", tok.linha, tok.lexema);\n", f);
        fputs("        exit(EXIT_FAILURE);\n    }\n", f);
    } else {
        fputs("        tok = proximo_token_gerado();\n", f);
    }
    fputs("}\n\n", f);
}

static int gerar_lexico(FILE *f, const Gramatica *g)
{
    int i, nlit = 0, erros = 0;
    char nome[300];

    emit_linhas(f, rt_lexico_estado);

    for (i = 0; i < g->nskips; i++) {
        sprintf(nome, "casa_skip_%d", i);
        fputs("/* SKIP: ", f);
        emitir_comentario(f, g->skips[i]);
        fputs(" */\n", f);
        if (gen_casamento_regex(f, nome, g->skips[i]) != 0)
            erros++;
    }
    for (i = 1; i < g->nterms; i++) {
        if (g->terms[i].literal) {
            nlit++;
            continue;
        }
        sprintf(nome, "casa_%.250s", g->terms[i].nome_c);
        fprintf(f, "/* %s: ", g->terms[i].nome);
        emitir_comentario(f, g->terms[i].regex ? g->terms[i].regex : "");
        fputs(" */\n", f);
        if (gen_casamento_regex(f, nome, g->terms[i].regex ? g->terms[i].regex : "")
            != 0)
            erros++;
    }

    /* literais: comparacao direta, com prioridade em caso de empate */
    fputs("static const char *const texto_literais[] = {\n", f);
    for (i = 1; i < g->nterms; i++)
        if (g->terms[i].literal) {
            fputs("    ", f);
            emitir_string_c(f, g->terms[i].nome);
            fputs(",\n", f);
        }
    fputs("    NULL\n};\n\nstatic const int tipo_literais[] = {\n", f);
    for (i = 1; i < g->nterms; i++)
        if (g->terms[i].literal)
            fprintf(f, "    %s,\n", g->terms[i].nome_c);
    fputs("    -1\n};\n\n", f);

    fputs("/* Reconhece o maior prefixo da entrada; em caso de empate vence\n"
          " * o literal (palavras reservadas tem prioridade sobre ID). */\n", f);
    fputs("static Token proximo_token_gerado(void)\n{\n", f);
    fputs("    Token t;\n    size_t n, melhor;\n    int i, tipo, pulou;\n\n", f);
    fputs("    do {\n        pulou = 0;\n", f);
    for (i = 0; i < g->nskips; i++)
        fprintf(f, "        if ((n = casa_skip_%d(fonte + pos)) > 0) {\n"
                   "            consumir(n);\n            pulou = 1;\n        }\n", i);
    fputs("    } while (pulou);\n\n", f);
    fputs("    memset(&t, 0, sizeof t);\n", f);
    fputs("    t.linha = linha;\n    t.coluna = coluna;\n", f);
    fputs("    if (fonte[pos] == '\\0') {\n        t.tipo = T_FIM;\n        return t;\n    }\n", f);
    fputs("    melhor = 0;\n    tipo = -1;\n", f);
    fputs("    for (i = 0; texto_literais[i] != NULL; i++) {\n", f);
    fputs("        n = strlen(texto_literais[i]);\n", f);
    fputs("        if (n > melhor && strncmp(fonte + pos, texto_literais[i], n) == 0) {\n", f);
    fputs("            melhor = n;\n            tipo = tipo_literais[i];\n        }\n    }\n", f);
    for (i = 1; i < g->nterms; i++)
        if (!g->terms[i].literal)
            fprintf(f, "    if ((n = casa_%s(fonte + pos)) > melhor) {\n"
                       "        melhor = n;\n        tipo = %s;\n    }\n",
                    g->terms[i].nome_c, g->terms[i].nome_c);
    fputs("    if (melhor == 0) {\n", f);
    fputs("        fprintf(stderr, \"linha %d, coluna %d: erro lexico: caractere "
          "invalido '%c'\\n\",\n                linha, coluna, fonte[pos]);\n", f);
    fputs("        exit(EXIT_FAILURE);\n    }\n", f);
    fputs("    n = melhor < sizeof t.lexema ? melhor : sizeof t.lexema - 1;\n", f);
    fputs("    memcpy(t.lexema, fonte + pos, n);\n    t.lexema[n] = '\\0';\n", f);
    fputs("    t.tipo = tipo;\n    consumir(melhor);\n    return t;\n}\n\n", f);
    (void) nlit;
    return erros;
}

static void gerar_procedimentos(FILE *f, const Gramatica *g, const OpcoesGeracao *op)
{
    int i;
    Emissor em;
    em.f = f;
    em.nivel = 0;

    fputs("/* ---- procedimentos (um por nao terminal) ---- */\n\n", f);
    for (i = 0; i < g->nnts; i++) {
        if (g->nts[i].regra == NULL)
            continue;
        fprintf(f, "/* %s = ", g->nts[i].nome);
        {
            /* a regra em EBNF, sem "* /" */
            FILE *tmp = tmpfile();
            int c;
            if (tmp != NULL) {
                char buf[2] = { 0, 0 };
                expr_imprimir(tmp, g, g->nts[i].regra);
                rewind(tmp);
                while ((c = fgetc(tmp)) != EOF) {
                    buf[0] = (char) c;
                    emitir_comentario(f, buf);
                }
                fclose(tmp);
            }
        }
        fputs(" ; */\n", f);
        fprintf(f, "void parse_%s(void)\n{\n", g->nts[i].nome);
        em.nivel = 1;
        if (op->arvore)
            emit(&em, "arvore_entra(\"%s\");", g->nts[i].nome);
        gen_expr(&em, g, g->nts[i].regra);
        if (op->arvore)
            emit(&em, "arvore_sai();");
        fputs("}\n\n", f);
    }
}

static void gerar_main(FILE *f, const Gramatica *g, const OpcoesGeracao *op)
{
    fputs("/* ---- programa principal ---- */\n\n", f);
    fputs("int main(int argc, char **argv)\n{\n", f);
    fputs("    int i, fim[2];\n    const char *arquivo = NULL, *tokens = NULL;\n", f);
    fputs("    FILE *entrada = stdin;\n\n", f);
    fputs("    for (i = 1; i < argc; i++) {\n", f);
    fputs("        if (strcmp(argv[i], \"--tree\") == 0) {\n", f);
    fputs("            imprimir_arvore = 1;\n", f);
    fputs("        } else if (strcmp(argv[i], \"--tokens\") == 0 && i + 1 < argc) {\n", f);
    fputs("            tokens = argv[++i];\n", f);
    fputs("        } else if (argv[i][0] == '-' && argv[i][1] != '\\0') {\n", f);
    fputs("            fprintf(stderr, \"uso: %s [--tree] [--tokens arquivo.tok | "
          "programa]\\n\", argv[0]);\n", f);
    fputs("            return 2;\n        } else {\n            arquivo = argv[i];\n"
          "        }\n    }\n", f);
    fputs("    if (imprimir_arvore && !SUPORTE_ARVORE)\n", f);
    fputs("        fprintf(stderr, \"aviso: gere o analisador com --tree para "
          "imprimir a arvore\\n\");\n\n", f);
    fputs("    if (tokens != NULL) {\n", f);
    fputs("        arquivo_tokens = fopen(tokens, \"r\");\n", f);
    fputs("        if (arquivo_tokens == NULL) {\n", f);
    fputs("            fprintf(stderr, \"nao foi possivel abrir %s\\n\", tokens);\n", f);
    fputs("            return 2;\n        }\n    } else {\n", f);
    fputs("        if (arquivo != NULL && (entrada = fopen(arquivo, \"r\")) == NULL) {\n", f);
    fputs("            fprintf(stderr, \"nao foi possivel abrir %s\\n\", arquivo);\n", f);
    fputs("            return 2;\n        }\n", f);
    if (op->microc)
        fputs("        scanner_iniciar(entrada);\n", f);
    else
        fputs("        fonte = ler_tudo(entrada);\n", f);
    fputs("    }\n\n", f);
    fputs("    avancar();\n", f);
    fprintf(f, "    parse_%s();\n", g->nts[g->inicial].nome);
    fputs("    if (tok.tipo != TOKEN_FIM) {\n", f);
    fputs("        fim[0] = TOKEN_FIM;\n        fim[1] = -1;\n", f);
    fputs("        erro_sintatico(fim);\n    }\n", f);
    fputs("    printf(\"entrada aceita\\n\");\n\n", f);
    fputs("    if (arquivo_tokens != NULL) {\n        fclose(arquivo_tokens);\n", f);
    fputs("    } else {\n", f);
    if (op->microc)
        fputs("        scanner_finalizar();\n", f);
    else
        fputs("        free(fonte);\n", f);
    fputs("        if (entrada != stdin)\n            fclose(entrada);\n    }\n", f);
    fputs("    return 0;\n}\n", f);
}

static const char *nome_base(const char *caminho)
{
    const char *b = strrchr(caminho, '/');
    return b != NULL ? b + 1 : caminho;
}

static int gerar_c(const Gramatica *g, const OpcoesGeracao *op)
{
    char *caminho = (char *) xmalloc(strlen(op->prefixo) + 3);
    FILE *f, *corpo;
    int c, erros = 0;

    /* Os procedimentos sao gerados primeiro num arquivo temporario porque
     * registram os conjuntos (conj_N), que precisam vir antes no .c. */
    corpo = tmpfile();
    if (corpo == NULL) {
        diag_erro(0, 0, "nao foi possivel criar arquivo temporario");
        free(caminho);
        return -1;
    }
    gerar_procedimentos(corpo, g, op);

    sprintf(caminho, "%s.c", op->prefixo);
    f = fopen(caminho, "w");
    if (f == NULL) {
        diag_erro(0, 0, "nao foi possivel criar %s", caminho);
        fclose(corpo);
        free(caminho);
        return -1;
    }
    escrever_cabecalho_c(f, op);
    fputs("#include <stdio.h>\n#include <stdlib.h>\n#include <string.h>\n", f);
    fprintf(f, "#include \"%s.h\"\n\n", nome_base(op->prefixo));
    fprintf(f, "#define SUPORTE_ARVORE %d\n\n", op->arvore ? 1 : 0);

    fputs("/* ---- conjuntos de tokens ---- */\n\n", f);
    emitir_conjuntos(f, g);
    fputc('\n', f);

    emit_linhas(f, rt_estado);
    if (!op->microc)
        erros += gerar_lexico(f, g);
    gerar_nome_token(f, g);
    gerar_posicao_e_avancar(f, op->microc);
    emit_linhas(f, rt_primitivas);
    gen_token_de_arquivo(f, op->microc);

    rewind(corpo);
    while ((c = fgetc(corpo)) != EOF)
        fputc(c, f);
    fclose(corpo);

    gerar_main(f, g, op);
    fclose(f);
    if (erros != 0) {
        remove(caminho);
        sprintf(caminho, "%s.h", op->prefixo);
        remove(caminho);
    }

    free(caminho);
    return erros == 0 ? 0 : -1;
}

int codegen_gerar(Gramatica *g, const OpcoesGeracao *op)
{
    int r;
    nomear_terminais(g, op->microc);
    r = gerar_h(g, op);
    if (r == 0)
        r = gerar_c(g, op);
    liberar_conjuntos();
    return r;
}
