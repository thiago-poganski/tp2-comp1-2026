%{
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "tokens.h"

YYSTYPE microc_yylval;

int linha_atual = 1;
#define TAM_TABELA 211

typedef struct no_tabela {
    char *texto;
    struct no_tabela *prox;
} NoTabela;

static NoTabela *tabela[TAM_TABELA];

static unsigned long hash(const char *s) {
    unsigned long h = 5381;
    while (*s != '\0') {
        h = h * 33 + (unsigned char) *s;
        s++;
    }
    return h;
}

static char *tabela_inserir(const char *s) {
    unsigned long pos = hash(s) % TAM_TABELA;
    NoTabela *p;
    NoTabela *novo;

    for (p = tabela[pos]; p != NULL; p = p->prox) {
        if (strcmp(p->texto, s) == 0)
            return p->texto;
    }

    novo = malloc(sizeof(NoTabela));
    if (novo == NULL) {
        fprintf(stderr, "Erro: memoria insuficiente\n");
        exit(1);
    }
    novo->texto = strdup(s);
    novo->prox = tabela[pos];
    tabela[pos] = novo;
    return novo->texto;
}

static void tabela_liberar(void) {
    int i;
    NoTabela *p;
    NoTabela *seguinte;

    for (i = 0; i < TAM_TABELA; i++) {
        p = tabela[i];
        while (p != NULL) {
            seguinte = p->prox;
            free(p->texto);
            free(p);
            p = seguinte;
        }
        tabela[i] = NULL;
    }
}


static void guarda_lexema(void) {
    microc_yylval.symbol = tabela_inserir(yytext);
}
static char converte_escape(char c) {
    switch (c) {
    case 'n':  return '\n';
    case 't':  return '\t';
    case 'r':  return '\r';
    case '0':  return '\0';
    case '\\': return '\\';
    case '\'': return '\'';
    case '"':  return '"';
    default:   return c;
    }
}
static void guarda_caractere(char c) {
    char buf[2];
    buf[0] = c;
    buf[1] = '\0';
    microc_yylval.symbol = tabela_inserir(buf);
}

static char *str_buf = NULL;
static size_t str_tam = 0;
static size_t str_cap = 0;
static int str_nulo = 0;

static void str_adiciona(char c) {
    if (str_tam + 1 >= str_cap) {
        str_cap = str_cap ? str_cap * 2 : 64;
        str_buf = realloc(str_buf, str_cap);
        if (str_buf == NULL) {
            fprintf(stderr, "Erro: memoria insuficiente\n");
            exit(1);
        }
    }
    str_buf[str_tam++] = c;
}

#define YY_DECL static int yylex_interno(void)

static int ultimo_token = UNDEF;

%}

/* -----------------------------------------------------------------------
 * 2. SECAO DE DEFINICOES
 * ------------------------------------------------------------------- */

DIGIT       [0-9]
LETRA       [a-zA-Z_]
ALFANUM     [a-zA-Z0-9_]

%option prefix="microc_yy" noyywrap
%x COMMENT
%x STRING

%%

 /* -----------------------------------------------------------------------
  * 3. SECAO DE REGRAS
  * --------------------------------------------------------------------- */

<INITIAL><<EOF>>    { return END_OF_FILE; }


 /* --- Espacos em branco e quebras de linha ---------------------------- */
\n                  { linha_atual++; }
[ \t\r]+            { /* ignora espacos em branco */ }

"//".*              { /* comentario de linha: ignora ate o fim da linha */ }

"/*"                { BEGIN(COMMENT); }
<COMMENT>"*/"       { BEGIN(INITIAL); }
<COMMENT>\n         { linha_atual++; }
<COMMENT><<EOF>>    {
                        BEGIN(INITIAL);
                        microc_yylval.error_msg = "EOF em comentario";
                        return UNDEF;
                    }

<COMMENT>.          { /* consome qualquer outro caractere dentro do comentario */ }

 /* Fechamento de comentario sem abertura correspondente. */
"*/"                {
                        microc_yylval.error_msg = "Comentario nao iniciado";
                        return UNDEF;
                    }

{LETRA}{ALFANUM}*   {
                        if(strcmp(yytext, "main")==0){
                            return MAIN;
                        }
                        if(strcmp(yytext, "if")==0){
                            return IF;
                        }
                        if(strcmp(yytext, "else")==0){
                            return ELSE;
                        }
                        if(strcmp(yytext, "for")==0){
                            return FOR;
                        }
                        if(strcmp(yytext, "return")==0){
                            return RETURN;
                        }
                        if(strcmp(yytext, "int")==0){
                            return INT;
                        }
                        if(strcmp(yytext, "char")==0){
                            return CHAR;
                        }
                        if(strcmp(yytext, "print")==0){
                            return PRINT;
                        }
                        
                        guarda_lexema();
                        return ID;
                    }

"-"{DIGIT}+         {
                        if (ultimo_token == ID || ultimo_token == INTEGERCONST ||
                            ultimo_token == CHARCONST || ultimo_token == RPAREN ||
                            ultimo_token == RBRACKET) {
                            yyless(1);
                            return MINUS;
                        }
                        guarda_lexema();
                        return INTEGERCONST;
                    }

{DIGIT}+            {
                        guarda_lexema();
                        return INTEGERCONST;
                    }


'[^'\\\n]'          {
                        guarda_caractere(yytext[1]);
                        return CHARCONST;
                    }

'\\[ntr0\\'\"]'     {
                        guarda_caractere(converte_escape(yytext[2]));
                        return CHARCONST;
                    }

'\\.'               {
                        microc_yylval.error_msg = "Sequencia de escape invalida";
                        return UNDEF;
                    }

''                  {
                        microc_yylval.error_msg = "Constante de caractere vazia";
                        return UNDEF;
                    }

'[^'\n][^'\n]+'     {
                        microc_yylval.error_msg = "Constante de caractere com mais de um caractere";
                        return UNDEF;
                    }

'[^'\n]*            {
                        microc_yylval.error_msg = "Constante de caractere nao terminada";
                        return UNDEF;
                    }


\"                  {
                        BEGIN(STRING);
                        str_tam = 0;
                        str_nulo = 0;
                    }
<STRING>\"          {
                        BEGIN(INITIAL);
                        if (str_nulo) {
                            microc_yylval.error_msg = "String contem caractere nulo";
                            return UNDEF;
                        }
                        str_adiciona('\0');
                        microc_yylval.symbol = tabela_inserir(str_buf);
                        return STRINGCONST;
                    }
<STRING>\\[ntr0\\\"']  {
                        str_adiciona(converte_escape(yytext[1]));
                    }
<STRING>\\\n        {
                        linha_atual++;
                        str_adiciona('\n');
                    }
<STRING>\\.         {
                        str_adiciona(yytext[1]);
                    }
<STRING>\\          {
                        str_adiciona('\\');
                    }
<STRING>\0          {
                        str_nulo = 1;
                    }
<STRING>\n          {
                        yyless(0);
                        BEGIN(INITIAL);
                        microc_yylval.error_msg = "String nao terminada";
                        return UNDEF;
                    }
<STRING><<EOF>>     {
                        BEGIN(INITIAL);
                        microc_yylval.error_msg = "EOF em string";
                        return UNDEF;
                    }
<STRING>[^\\\"\n\0]+ {
                        int i;
                        for (i = 0; yytext[i] != '\0'; i++)
                            str_adiciona(yytext[i]);
                    }


"=="                { return EQ; }
"="                 { return ASSIGN; }
"!="                { return NEQ; }
"!"                 { return NOT; }
"<="                { return LEQ; }
"<"                 { return LT; }
">="                { return GEQ; }
">"                 { return GT; }
"&&"                { return AND; }
"||"                 { return OR; }
"+"                 { return PLUS; }
"-"                 { return MINUS; }
"*"                 { return MUL; }
"/"                 { return DIV; }
"%"                 { return MOD; }
";"                 { return SEMICOLON; }
","                 { return COMMA; }
"("                 { return LPAREN; }
")"                 { return RPAREN; }
"{"                 { return LBRACE; }
"}"                 { return RBRACE; }
"["                 { return LBRACKET; }
"]"                 { return RBRACKET; }

.                   {
                        microc_yylval.error_msg = tabela_inserir(yytext);
                        return UNDEF;
                    }

%%

int yylex(void) {
    ultimo_token = yylex_interno();
    return ultimo_token;
}

void microc_liberar_lexico(void) {
    free(str_buf);
    str_buf = NULL;
    str_cap = 0;
    tabela_liberar();
}

