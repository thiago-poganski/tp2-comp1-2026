#include <stdio.h>
#include <string.h>
#include "conjuntos.h"
#include "util.h"

/* ------------------------------------------------------------------ */
/* Fornecido                                                          */
/* ------------------------------------------------------------------ */

static void iniciar_expr(Expr *e, void *ctx)
{
    int n = *(int *) ctx;
    bitset_liberar(&e->first);
    bitset_liberar(&e->follow);
    bitset_iniciar(&e->first, n);
    bitset_iniciar(&e->follow, n);
    e->anulavel = 0;
}

void conj_iniciar(Gramatica *g)
{
    int i, n = g->nterms;
    for (i = 0; i < g->nnts; i++) {
        bitset_liberar(&g->nts[i].first);
        bitset_liberar(&g->nts[i].follow);
        bitset_iniciar(&g->nts[i].first, n);
        bitset_iniciar(&g->nts[i].follow, n);
        g->nts[i].anulavel = 0;
        expr_percorrer(g->nts[i].regra, iniciar_expr, &n);
    }
}

void conj_imprimir(FILE *f, const Gramatica *g)
{
    int i;
    size_t largura = strlen("NAO TERMINAL");
    for (i = 0; i < g->nnts; i++)
        if (strlen(g->nts[i].nome) > largura)
            largura = strlen(g->nts[i].nome);
    fprintf(f, "%-*s  ANULAVEL  FIRST / FOLLOW\n", (int) largura, "NAO TERMINAL");
    for (i = 0; i < g->nnts; i++) {
        fprintf(f, "%-*s  %-8s  FIRST  = ", (int) largura, g->nts[i].nome,
                g->nts[i].anulavel ? "sim" : "nao");
        gram_imprimir_conjunto(f, g, &g->nts[i].first);
        fprintf(f, "\n%-*s            FOLLOW = ", (int) largura, "");
        gram_imprimir_conjunto(f, g, &g->nts[i].follow);
        fputc('\n', f);
    }
}

/* ------------------------------------------------------------------ */
/* A implementar                                                      */
/* ------------------------------------------------------------------ */

static void anulavel_rec(Gramatica *g, Expr *e, int *mudou)
{
    int i, v = 0;

    for (i = 0; i < e->nfilhos; i++)
        anulavel_rec(g, e->filhos[i], mudou);
    switch (e->tipo) {
    case E_TERM:
        v = 0;
        break;
    case E_VAZIO:
    case E_OPC:
    case E_REP:
        v = 1;
        break;
    case E_NAOTERM:
        v = g->nts[e->simbolo].anulavel;
        break;
    case E_SEQ:
        v = 1;
        for (i = 0; i < e->nfilhos; i++)
            if (!e->filhos[i]->anulavel)
                v = 0;
        break;
    case E_ALT:
        v = 0;
        for (i = 0; i < e->nfilhos; i++)
            if (e->filhos[i]->anulavel)
                v = 1;
        break;
    }
    if (v != e->anulavel) {
        e->anulavel = v;
        *mudou = 1;
    }
}

void conj_anulavel(Gramatica *g)
{
    int i, mudou = 1;

    while (mudou) {
        mudou = 0;
        for (i = 0; i < g->nnts; i++) {
            if (g->nts[i].regra == NULL)
                continue;
            anulavel_rec(g, g->nts[i].regra, &mudou);
            if (g->nts[i].anulavel != g->nts[i].regra->anulavel) {
                g->nts[i].anulavel = g->nts[i].regra->anulavel;
                mudou = 1;
            }
        }
    }
}


static void first_rec(Gramatica *g, Expr *e, int *mudou)
{
    int i;

    for (i = 0; i < e->nfilhos; i++)
        first_rec(g, e->filhos[i], mudou);
    switch (e->tipo) {
    case E_TERM:
        if (!bitset_tem(&e->first, e->simbolo)) {
            bitset_add(&e->first, e->simbolo);
            *mudou = 1;
        }
        break;
    case E_NAOTERM:
        *mudou |= bitset_unir(&e->first, &g->nts[e->simbolo].first);
        break;
    case E_SEQ:
        for (i = 0; i < e->nfilhos; i++) {
            *mudou |= bitset_unir(&e->first, &e->filhos[i]->first);
            if (!e->filhos[i]->anulavel)
                break;
        }
        break;
    case E_ALT:
    case E_OPC:
    case E_REP:
        for (i = 0; i < e->nfilhos; i++)
            *mudou |= bitset_unir(&e->first, &e->filhos[i]->first);
        break;
    case E_VAZIO:
        break;
    }
}

void conj_first(Gramatica *g)
{
    int i, mudou = 1;

    while (mudou) {
        mudou = 0;
        for (i = 0; i < g->nnts; i++) {
            if (g->nts[i].regra == NULL)
                continue;
            first_rec(g, g->nts[i].regra, &mudou);
            mudou |= bitset_unir(&g->nts[i].first, &g->nts[i].regra->first);
        }
    }
}

static void follow_rec(Gramatica *g, Expr *e, int *mudou)
{
    int i, resto_anulavel;
    Bitset resto;
    Expr *f;

    switch (e->tipo) {
    case E_SEQ:
        bitset_iniciar(&resto, g->nterms);
        resto_anulavel = 1;
        for (i = e->nfilhos - 1; i >= 0; i--) {
            f = e->filhos[i];
            *mudou |= bitset_unir(&f->follow, &resto);
            if (resto_anulavel)
                *mudou |= bitset_unir(&f->follow, &e->follow);
            if (f->anulavel) {
                bitset_unir(&resto, &f->first);
            } else {
                bitset_copiar(&resto, &f->first);
                resto_anulavel = 0;
            }
        }
        bitset_liberar(&resto);
        break;
    case E_ALT:
    case E_OPC:
        for (i = 0; i < e->nfilhos; i++)
            *mudou |= bitset_unir(&e->filhos[i]->follow, &e->follow);
        break;
    case E_REP:
        *mudou |= bitset_unir(&e->filhos[0]->follow, &e->follow);
        *mudou |= bitset_unir(&e->filhos[0]->follow, &e->filhos[0]->first);
        break;
    case E_NAOTERM:
        *mudou |= bitset_unir(&g->nts[e->simbolo].follow, &e->follow);
        break;
    default:
        break;
    }
    for (i = 0; i < e->nfilhos; i++)
        follow_rec(g, e->filhos[i], mudou);
}

void conj_follow(Gramatica *g)
{
    int i, mudou = 1;

    bitset_add(&g->nts[g->inicial].follow, TERM_FIM);
    while (mudou) {
        mudou = 0;
        for (i = 0; i < g->nnts; i++) {
            if (g->nts[i].regra == NULL)
                continue;
            mudou |= bitset_unir(&g->nts[i].regra->follow, &g->nts[i].follow);
            follow_rec(g, g->nts[i].regra, &mudou);
        }
    }
}

