#include <stdio.h>
#include <string.h>
#include "scanner.h"

extern int   microc_yylex(void);
extern FILE *microc_yyin;
extern char *microc_yytext;
extern int   linha_atual;
extern int   microc_yylex_destroy(void);
extern void  microc_liberar_lexico(void);

static const char *texto_do_lexema(int tipo)
{
    if (tipo == ID || tipo == INTEGERCONST || tipo == CHARCONST || tipo == STRINGCONST)
        return microc_yylval.symbol;
    if (tipo == UNDEF)
        return microc_yylval.error_msg;
    return microc_yytext;
}

static TokenType normalizar(int tipo)
{
    if (tipo <= (int) PRINT)
        return (TokenType) tipo;
    switch (tipo) {
    case '+': return PLUS;
    case '-': return MINUS;
    case '*': return MUL;
    case '/': return DIV;
    case '%': return MOD;
    case '<': return LT;
    case '>': return GT;
    case '=': return ASSIGN;
    case ';': return SEMICOLON;
    case ',': return COMMA;
    case '(': return LPAREN;
    case ')': return RPAREN;
    case '{': return LBRACE;
    case '}': return RBRACE;
    case '[': return LBRACKET;
    case ']': return RBRACKET;
    default:  return (TokenType) tipo;
    }
}

void scanner_iniciar(FILE *entrada)
{
    microc_yyin = entrada;
    linha_atual = 1;
}

Token proximo_token(void)
{
    Token t;
    int tipo;
    const char *texto;

    memset(&t, 0, sizeof t);
    tipo = microc_yylex();
    t.tipo = normalizar(tipo);
    t.linha = linha_atual;
    texto = t.tipo == END_OF_FILE ? "" : texto_do_lexema(tipo);
    if (texto != NULL) {
        strncpy(t.lexema, texto, sizeof t.lexema - 1);
        t.lexema[sizeof t.lexema - 1] = '\0';
    }
    return t;
}

void scanner_finalizar(void)
{
    microc_yylex_destroy();
    microc_liberar_lexico();
}
