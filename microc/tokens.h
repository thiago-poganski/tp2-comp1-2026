#ifndef TOKENS_H
#define TOKENS_H

typedef enum {
    UNDEF, ID, END_OF_FILE,
    INTEGERCONST, CHARCONST, STRINGCONST,
    PLUS, MINUS, MUL, DIV, MOD,
    EQ, NEQ, LT, GT, LEQ, GEQ, AND, OR, NOT,
    ASSIGN, SEMICOLON, COMMA, LPAREN, RPAREN,
    LBRACE, RBRACE, LBRACKET, RBRACKET,
    MAIN, IF, ELSE, FOR, RETURN, INT, CHAR, PRINT
} TokenType;

typedef struct {
    TokenType tipo;
    char lexema[100];
    int linha;
} Token;

typedef struct {
    char *symbol;
    char *error_msg;
} YYSTYPE;

extern YYSTYPE microc_yylval;

#endif
