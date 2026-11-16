#include <stdlib.h>
#include <string.h>
#include "verificacao.h"
#include "microc_mapa.h"
#include "util.h"

/* ------------------------------------------------------------------ */
/* Fornecido                                                          */
/* ------------------------------------------------------------------ */

static int verif_indefinidos(Gramatica *g)
{
    int i, erros = 0;
    for (i = 0; i < g->nnts; i++) {
        if (g->nts[i].regra == NULL) {
            diag_erro(g->nts[i].linha, g->nts[i].coluna,
                      "nao terminal %s usado mas nao definido", g->nts[i].nome);
            erros++;
        }
    }
    return erros;
}

static int verif_terminais(Gramatica *g, int modo_microc)
{
    int i, erros = 0, carregado = 0;
    Terminal *t;

    if (modo_microc)
        carregado = microc_carregar_tokens_h(g->tokens_externos) == 0;

    for (i = 1; i < g->nterms; i++) {
        t = &g->terms[i];
        if (modo_microc) {
            if (t->literal && microc_nome_literal(t->nome) == NULL) {
                diag_erro(t->linha, t->coluna, "literal %s nao corresponde a nenhum "
                          "token de Micro C", t->exibicao);
                erros++;
            } else if (!t->literal && carregado && !microc_token_existe(t->nome)) {
                diag_erro(t->linha, t->coluna, "terminal %s nao existe na enumeracao "
                          "TokenType de %s", t->nome, g->tokens_externos);
                erros++;
            }
        } else if (!t->declarado) {
            diag_erro(t->linha, t->coluna, "terminal %s nao declarado em TOKENS", t->nome);
            erros++;
        }
    }
    return erros;
}

static void marcar_usados(const Expr *e, char *marca, int *mudou)
{
    int i;
    if (e->tipo == E_NAOTERM) {
        if (!marca[e->simbolo]) {
            marca[e->simbolo] = 1;
            *mudou = 1;
        }
        return;
    }
    for (i = 0; i < e->nfilhos; i++)
        marcar_usados(e->filhos[i], marca, mudou);
}

static int verif_inalcancaveis(Gramatica *g)
{
    char *alcancavel = (char *) xcalloc((size_t) g->nnts, 1);
    int i, mudou = 1;

    alcancavel[g->inicial] = 1;
    while (mudou) {
        mudou = 0;
        for (i = 0; i < g->nnts; i++)
            if (alcancavel[i] && g->nts[i].regra != NULL)
                marcar_usados(g->nts[i].regra, alcancavel, &mudou);
    }
    for (i = 0; i < g->nnts; i++)
        if (!alcancavel[i] && g->nts[i].regra != NULL)
            diag_aviso(g->nts[i].linha, g->nts[i].coluna,
                       "nao terminal %s inalcancavel a partir de %s",
                       g->nts[i].nome, g->nts[g->inicial].nome);
    free(alcancavel);
    return 0;
}

static int expr_produtiva(const Expr *e, const char *produtivo)
{
    int i;
    switch (e->tipo) {
    case E_NAOTERM:
        return produtivo[e->simbolo];
    case E_SEQ:
        for (i = 0; i < e->nfilhos; i++)
            if (!expr_produtiva(e->filhos[i], produtivo))
                return 0;
        return 1;
    case E_ALT:
        for (i = 0; i < e->nfilhos; i++)
            if (expr_produtiva(e->filhos[i], produtivo))
                return 1;
        return 0;
    default:
        return 1;
    }
}

static int verif_improdutivos(Gramatica *g)
{
    char *produtivo = (char *) xcalloc((size_t) g->nnts, 1);
    int i, mudou = 1, erros = 0;

    while (mudou) {
        mudou = 0;
        for (i = 0; i < g->nnts; i++) {
            if (!produtivo[i] && g->nts[i].regra != NULL &&
                expr_produtiva(g->nts[i].regra, produtivo)) {
                produtivo[i] = 1;
                mudou = 1;
            }
        }
    }
    for (i = 0; i < g->nnts; i++) {
        if (!produtivo[i] && g->nts[i].regra != NULL) {
            diag_erro(g->nts[i].linha_def, 0,
                      "nao terminal %s e improdutivo: nao deriva nenhuma cadeia de terminais",
                      g->nts[i].nome);
            erros++;
        }
    }
    free(produtivo);
    return erros;
}

static void coletar_inicio(const Expr *e, char *linha)
{
    int i;
    switch (e->tipo) {
    case E_NAOTERM:
        linha[e->simbolo] = 1;
        break;
    case E_SEQ:
        for (i = 0; i < e->nfilhos; i++) {
            coletar_inicio(e->filhos[i], linha);
            if (!e->filhos[i]->anulavel)
                break;
        }
        break;
    case E_ALT:
    case E_OPC:
    case E_REP:
        for (i = 0; i < e->nfilhos; i++)
            coletar_inicio(e->filhos[i], linha);
        break;
    default:
        break;
    }
}

int verif_recursao_esquerda(Gramatica *g)
{
    int n = g->nnts, i, j, k, erros = 0;
    char *direto = (char *) xcalloc((size_t) n * (size_t) n, 1);
    char *alcanca = (char *) xcalloc((size_t) n * (size_t) n, 1);

    for (i = 0; i < n; i++)
        if (g->nts[i].regra != NULL)
            coletar_inicio(g->nts[i].regra, &direto[i * n]);
    memcpy(alcanca, direto, (size_t) n * (size_t) n);
    for (k = 0; k < n; k++)
        for (i = 0; i < n; i++)
            if (alcanca[i * n + k])
                for (j = 0; j < n; j++)
                    if (alcanca[k * n + j])
                        alcanca[i * n + j] = 1;
    for (i = 0; i < n; i++) {
        if (alcanca[i * n + i]) {
            diag_erro(g->nts[i].linha_def, 0, "nao terminal %s tem recursao a esquerda %s",
                      g->nts[i].nome, direto[i * n + i] ? "direta" : "indireta");
            erros++;
        }
    }
    free(direto);
    free(alcanca);
    return erros;
}


int verif_basica(Gramatica *g, int modo_microc)
{
    int erros = 0;
    if (g->inicial < 0) {
        diag_erro(0, 0, "a gramatica nao tem nenhuma regra");
        return 1;
    }
    erros += verif_indefinidos(g);
    erros += verif_terminais(g, modo_microc);
    erros += verif_inalcancaveis(g);
    if (erros == 0)
        erros += verif_improdutivos(g);
    return erros;
}
