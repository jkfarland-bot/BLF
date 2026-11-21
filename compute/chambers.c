/* Chambers of the toric arrangement {t + r.x in Z} met by a grid, counted directly.
   A generic point u = (K + a.x)/q gives the floor vector F(x) = floor(u(x)); its chamber on
   the torus is F modulo integer affine functions. Canonical form: G = F - F(0) - sum_i x_i (F(e_i) - F(0)).
   Folded enumeration (0 <= a_1 <= ... <= a_n <= q/2) plus closure under input permutations and
   complementations, which act on F by F -> F o sigma (then re-canonicalize).
   Only points with K + a.x not divisible by q for every x are generic; we use 2K+1 over 2q,
   i.e. u = (2K + 1 + 2 a.x)/(2q), which is never an integer, so every grid point is generic.
   Universality: same determinant/rounding argument with grid step 1/q after the shift.
   Also counts output-affine classes (G mod 2 with affine part removed) to test |classes| = (R+1)/2.
   usage: chambers n q fold(0/1) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int n, N;
#define HBITS 25
static int8_t (*tab)[64]; static uint8_t *used; static long cnt = 0;
static int8_t (*qu)[64]; static long qn = 0;
static uint64_t hsh(const int8_t *g) { uint64_t h = 1469598103934665603ULL; for (int i = 0; i < N; i++) { h ^= (uint8_t)g[i]; h *= 1099511628211ULL; } return h; }
static void canon(const long *F, int8_t *g) {
    for (int x = 0; x < N; x++) {
        long v = F[x] - F[0];
        for (int i = 0; i < n; i++) if (x >> i & 1) v -= F[1 << i] - F[0];
        g[x] = (int8_t)v;
    }
}
static void add(const int8_t *g) {
    uint64_t h = hsh(g) & ((1UL << HBITS) - 1);
    while (used[h]) { if (!memcmp(tab[h], g, N)) return; h = (h + 1) & ((1UL << HBITS) - 1); }
    used[h] = 1; memcpy(tab[h], g, N); cnt++; memcpy(qu[qn++], g, N);
}
static long q; static long a[8]; static int fold;
static void point(void) {
    long F[64]; int8_t g[64];
    long s[64];
    for (int x = 0; x < N; x++) { long v = 0; for (int k = 0; k < n; k++) if (x >> k & 1) v += a[k]; s[x] = v; }
    for (long K = 0; K < q; K++) {
        for (int x = 0; x < N; x++) { long w = 2 * K + 1 + 2 * s[x]; F[x] = w / (2 * q); }
        canon(F, g); add(g);
    }
}
static void rec(int i, long lo) {
    if (i == n) { point(); return; }
    long hi = fold ? q / 2 : q - 1;
    for (long v = fold ? lo : 0; v <= hi; v++) { a[i] = v; rec(i + 1, v); }
}
int main(int argc, char **argv) {
    n = atoi(argv[1]); q = atol(argv[2]); fold = atoi(argv[3]); N = 1 << n;
    tab = calloc(1UL << HBITS, 64); used = calloc(1UL << HBITS, 1); qu = malloc((1UL << 25) * 64);
    rec(0, 0);
    long folded = qn;
    for (long h = 0; h < qn; h++) {
        long F[64], F2[64]; int8_t g[64];
        for (int x = 0; x < N; x++) F[x] = qu[h][x];
        for (int i = 0; i + 1 < n; i++) {
            for (int x = 0; x < N; x++) {
                int bi = x >> i & 1, bj = x >> (i + 1) & 1; int y = x & ~((1 << i) | (1 << (i + 1)));
                y |= bi << (i + 1); y |= bj << i; F2[y] = F[x];
            }
            canon(F2, g); add(g);
        }
        if (n) { for (int x = 0; x < N; x++) F2[x ^ 1] = F[x]; canon(F2, g); add(g); }
    }
    /* output-affine classes: G mod 2 (G already has G(0)=G(e_i)=0), counted in a hash set */
    long CB = 1L << 25; uint64_t *ct = calloc(CB, 8); long nc = 0;
    for (long h = 0; h < qn; h++) {
        uint64_t T = 0; for (int x = 0; x < N; x++) T |= (uint64_t)(qu[h][x] & 1) << x;
        uint64_t key = T + 1; uint64_t p = (key * 0x9E3779B97F4A7C15ULL) >> 39;
        while (ct[p] && ct[p] != key) p = (p + 1) & (CB - 1);
        if (!ct[p]) { ct[p] = key; nc++; }
    }
    printf("n=%d q=%ld fold=%d folded_chambers=%ld chambers=%ld classes=%ld (R+1)/2=%ld\n", n, q, fold, folded, qn, nc, (qn + 1) / 2);
    return 0;
}
