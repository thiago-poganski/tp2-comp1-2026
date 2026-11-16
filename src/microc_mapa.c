/*
 * microc_mapa.c - Correspondencia com os tokens de Micro C (ver microc_mapa.h).
 *
 * A tabela de literais segue o tokens.h do livro-texto (secao 2.3.1):
 *
 *   UNDEF, ID, END_OF_FILE, INTEGERCONST, CHARCONST, STRINGCONST,
 *   PLUS, MINUS, MUL, DIV, MOD, EQ, NEQ, LT, GT, LEQ, GEQ, AND, OR, NOT,
 *   ASSIGN, SEMICOLON, COMMA, LPAREN, RPAREN, LBRACE, RBRACE,
 *   LBRACKET, RBRACKET, MAIN, IF, ELSE, FOR, RETURN, INT, CHAR, PRINT
 *
 * Se o seu tokens.h do TP1 usar outros nomes, ajuste a tabela.
 */
#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "microc_mapa.h"
#include "util.h"

static const char *const literais[][2] = {
    { "+",  "PLUS" },      { "-",  "MINUS" },     { "*",  "MUL" },
    { "/",  "DIV" },       { "%",  "MOD" },
    { "==", "EQ" },        { "!=", "NEQ" },       { "<",  "LT" },
    { ">",  "GT" },        { "<=", "LEQ" },       { ">=", "GEQ" },
    { "&&", "AND" },       { "||", "OR" },        { "!",  "NOT" },
    { "=",  "ASSIGN" },    { ";",  "SEMICOLON" }, { ",",  "COMMA" },
    { "(",  "LPAREN" },    { ")",  "RPAREN" },    { "{",  "LBRACE" },
    { "}",  "RBRACE" },    { "[",  "LBRACKET" },  { "]",  "RBRACKET" },
    { "main", "MAIN" },    { "if", "IF" },        { "else", "ELSE" },
    { "for", "FOR" },      { "return", "RETURN" },{ "int", "INT" },
    { "char", "CHAR" },    { "print", "PRINT" }
};

static char **nomes = NULL;
static int nnomes = 0, capnomes = 0;

const char *microc_nome_literal(const char *literal)
{
    size_t i;
    for (i = 0; i < sizeof(literais) / sizeof(literais[0]); i++)
        if (strcmp(literais[i][0], literal) == 0)
            return literais[i][1];
    return NULL;
}

static void adicionar_nome(const char *s, size_t n)
{
    if (nnomes == capnomes) {
        capnomes = capnomes ? 2 * capnomes : 64;
        nomes = (char **) xrealloc(nomes, (size_t) capnomes * sizeof(char *));
    }
    nomes[nnomes++] = xstrndup(s, n);
}

static void apagar_comentarios(char *s)
{
    while (*s != '\0') {
        if (s[0] == '/' && s[1] == '*') {
            while (*s != '\0' && !(s[0] == '*' && s[1] == '/'))
                *s++ = ' ';
            if (*s != '\0') {
                *s++ = ' ';
                *s++ = ' ';
            }
        } else if (s[0] == '/' && s[1] == '/') {
            while (*s != '\0' && *s != '\n')
                *s++ = ' ';
        } else {
            s++;
        }
    }
}

static int eh_ident(int c)
{
    return isalnum((unsigned char) c) || c == '_';
}

static const char *pular_espacos(const char *s)
{
    while (isspace((unsigned char) *s))
        s++;
    return s;
}

int microc_carregar_tokens_h(const char *caminho)
{
    char *texto;
    const char *p, *q, *fim, *ini;
    int achou = 0;

    if (caminho == NULL)
        return -1;
    texto = ler_arquivo(caminho);
    if (texto == NULL) {
        diag_erro(0, 0, "nao foi possivel abrir %s", caminho);
        return -1;
    }
    apagar_comentarios(texto);
    for (p = strstr(texto, "typedef"); p != NULL && !achou; p = strstr(p + 1, "typedef")) {
        q = pular_espacos(p + 7);
        if (strncmp(q, "enum", 4) != 0 || eh_ident(q[4]))
            continue;
        q = pular_espacos(q + 4);
        while (eh_ident(*q))
            q++;
        q = pular_espacos(q);
        if (*q != '{')
            continue;
        fim = strchr(q, '}');
        if (fim == NULL)
            break;
        p = pular_espacos(fim + 1);
        if (strncmp(p, "TokenType", 9) != 0 || eh_ident(p[9]))
            continue;
        for (q = q + 1; q < fim; ) {
            if (isalpha((unsigned char) *q) || *q == '_') {
                ini = q;
                while (q < fim && eh_ident(*q))
                    q++;
                adicionar_nome(ini, (size_t) (q - ini));
                while (q < fim && *q != ',')
                    q++;
            } else {
                q++;
            }
        }
        achou = 1;
    }
    free(texto);
    if (!achou) {
        diag_erro(0, 0, "enumeracao \"typedef enum { ... } TokenType;\" nao encontrada em %s",
                  caminho);
        return -1;
    }
    return 0;
}


int microc_token_existe(const char *nome)
{
    int i;
    for (i = 0; i < nnomes; i++)
        if (strcmp(nomes[i], nome) == 0)
            return 1;
    return 0;
}

void microc_liberar(void)
{
    int i;
    for (i = 0; i < nnomes; i++)
        free(nomes[i]);
    free(nomes);
    nomes = NULL;
    nnomes = capnomes = 0;
}
