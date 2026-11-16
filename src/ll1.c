#include <stdarg.h>
#include <stdio.h>
#include "ll1.h"
#include "util.h"

/* Reporta um conflito na regra do nao terminal nt, na posicao de e.
 * comum (pode ser NULL) e o conjunto de tokens em conflito. */
static void reportar(const Gramatica *g, int nt, const Expr *e, int eh_aviso,
                     const Bitset *comum, const char *fmt, ...)
{
    va_list ap;
    fprintf(stderr, "%s:%d:%d: %s: conflito LL(1) em %s: ", g->arquivo, e->linha,
            e->coluna, eh_aviso ? "aviso" : "erro", g->nts[nt].nome);
    va_start(ap, fmt);
    vfprintf(stderr, fmt, ap);
    va_end(ap);
    if (comum != NULL) {
        fprintf(stderr, " ");
        gram_imprimir_conjunto(stderr, g, comum);
    }
    fputc('\n', stderr);
}

static int verificar_expr(const Gramatica *g, int nt, const Expr *e)
{
    int i, j, erros = 0;
    const Expr *a, *b;
    const char *nome;
    Bitset comum;

    bitset_iniciar(&comum, g->nterms);
    switch (e->tipo) {
    case E_ALT:
        for (i = 0; i < e->nfilhos; i++) {
            a = e->filhos[i];
            for (j = i + 1; j < e->nfilhos; j++) {
                b = e->filhos[j];
                bitset_intersecao(&comum, &a->first, &b->first);
                if (!bitset_vazio(&comum)) {
                    reportar(g, nt, e, 0, &comum, "alternativas %d e %d comecam com", i + 1, j + 1);
                    erros++;
                }
                if (a->anulavel && b->anulavel) {
                    reportar(g, nt, e, 0, NULL, "alternativas %d e %d sao anulaveis", i + 1, j + 1);
                    erros++;
                }
            }
        }
        for (i = 0; i < e->nfilhos; i++) {
            a = e->filhos[i];
            if (!a->anulavel)
                continue;
            for (j = 0; j < e->nfilhos; j++) {
                if (j == i)
                    continue;
                b = e->filhos[j];
                bitset_intersecao(&comum, &e->follow, &b->first);
                if (!bitset_vazio(&comum)) {
                    reportar(g, nt, e, 0, &comum, "alternativa %d e anulavel e o FOLLOW "
                             "intersecta o FIRST da alternativa %d em", i + 1, j + 1);
                    erros++;
                }
            }
        }
        break;
    case E_OPC:
    case E_REP:
        a = e->filhos[0];
        nome = e->tipo == E_OPC ? "[ ]" : "{ }";
        if (a->anulavel) {
            reportar(g, nt, e, 0, NULL, "o conteudo de %s e anulavel", nome);
            erros++;
        } else {
            bitset_intersecao(&comum, &a->first, &e->follow);
            if (!bitset_vazio(&comum))
                reportar(g, nt, e, 1, &comum, "FIRST e FOLLOW de %s se intersectam "
                         "(resolvido de forma gulosa) em", nome);
        }
        break;
    default:
        break;
    }
    bitset_liberar(&comum);
    for (i = 0; i < e->nfilhos; i++)
        erros += verificar_expr(g, nt, e->filhos[i]);
    return erros;
}

int ll1_verificar(const Gramatica *g)
{
    int i, erros = 0;

    for (i = 0; i < g->nnts; i++)
        if (g->nts[i].regra != NULL)
            erros += verificar_expr(g, i, g->nts[i].regra);
    return erros;
}

