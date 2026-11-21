/* Threshold functions, threshold XOR affine, and their place inside BLF(n), n <= 5.
   Thresholds: T(x) = [Y_0 + w.x > 0] with |Y_k| <= M_n (twbound.c). Enumerated in a folded form
   (0 <= w_1 <= ... <= w_n <= M, |Y_0| <= (n+1) M, which covers every realization after complementing
   and permuting inputs) and closed under input permutations and complementations.
   unfold=1: enumerate all |Y_k| <= M directly instead (check of the fold, n <= 4).
   BLF classes: universal folded grid q (gridfold.c logic) plus closure.
   usage: thresh n M q unfold */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int n, N;
static uint64_t canon(uint64_t T) {
    int f0 = T & 1; uint64_t A = 0;
    for (int x = 0; x < N; x++) { int bit = f0;
        for (int i = 0; i < n; i++) if (x >> i & 1) bit ^= (int)((T >> (1 << i)) & 1) ^ f0;
        A |= (uint64_t)bit << x; }
    return T ^ A;
}
static uint64_t swp(uint64_t T, int i, int j) { uint64_t R = 0;
    for (int x = 0; x < N; x++) { int bi = x >> i & 1, bj = x >> j & 1; int y = x & ~((1 << i) | (1 << j));
        y |= bi << j; y |= bj << i; R |= ((T >> x) & 1) << y; } return R; }
static uint64_t flp(uint64_t T, int i) { uint64_t R = 0; for (int x = 0; x < N; x++) R |= ((T >> x) & 1) << (x ^ (1 << i)); return R; }
typedef struct { uint8_t *bits; uint64_t *q; long qn; } Set;
static Set mk(void) { Set s; s.bits = calloc(((uint64_t)1 << N) / 8 + 1, 1); s.q = malloc(sizeof(uint64_t) * 40000000); s.qn = 0; return s; }
static int has(Set *s, uint64_t T) { return s->bits[T >> 3] >> (T & 7) & 1; }
static void add(Set *s, uint64_t T) { if (!has(s, T)) { s->bits[T >> 3] |= 1 << (T & 7); s->q[s->qn++] = T; } }
static void close_tables(Set *s) { /* close tables (not classes) under the group */
    for (long h = 0; h < s->qn; h++) { uint64_t T = s->q[h];
        for (int i = 0; i + 1 < n; i++) add(s, swp(T, i, i + 1)); if (n) add(s, flp(T, 0)); } }
static void close_classes(Set *s) {
    for (long h = 0; h < s->qn; h++) { uint64_t T = s->q[h];
        for (int i = 0; i + 1 < n; i++) add(s, canon(swp(T, i, i + 1))); if (n) add(s, canon(flp(T, 0))); } }
static long M, q; static long w[8]; static Set TH, BL;
static void trec(int i, long lo, int unfold) {
    if (i == n) {
        long s[64]; for (int x = 0; x < N; x++) { long v = 0; for (int k = 0; k < n; k++) if (x >> k & 1) v += w[k]; s[x] = v; }
        long B = unfold ? M : (n + 1) * M;
        for (long y0 = -B; y0 <= B; y0++) { uint64_t T = 0; for (int x = 0; x < N; x++) if (y0 + s[x] > 0) T |= (uint64_t)1 << x; add(&TH, T); }
        return;
    }
    for (long v = unfold ? -M : lo; v <= M; v++) { w[i] = v; trec(i + 1, v, unfold); }
}
static long a[8];
static void brec(int i, long lo) {
    if (i == n) { long s[64]; for (int x = 0; x < N; x++) { long v = 0; for (int k = 0; k < n; k++) if (x >> k & 1) v += a[k]; s[x] = v; }
        for (long K = 0; K < q; K++) { uint64_t T = 0; for (int x = 0; x < N; x++) T |= (uint64_t)(((K + s[x]) / q) & 1) << x; add(&BL, canon(T)); }
        return; }
    for (long v = lo; v <= q / 2; v++) { a[i] = v; brec(i + 1, v); }
}
int main(int argc, char **argv) {
    n = atoi(argv[1]); M = atol(argv[2]); q = atol(argv[3]); int unfold = atoi(argv[4]); N = 1 << n;
    TH = mk(); trec(0, 0, unfold); if (!unfold) close_tables(&TH);
    printf("n=%d threshold functions: %ld\n", n, TH.qn);
    Set TX = mk(); for (long h = 0; h < TH.qn; h++) add(&TX, canon(TH.q[h]));
    printf("threshold XOR affine: %ld classes, %ld tables\n", TX.qn, TX.qn << (n + 1));
    BL = mk(); brec(0, 0); close_classes(&BL);
    printf("BLF: %ld classes, %ld tables\n", BL.qn, BL.qn << (n + 1));
    long notin = 0; for (long h = 0; h < TX.qn; h++) if (!has(&BL, TX.q[h])) notin++;
    printf("threshold-XOR-affine classes outside BLF: %ld\n", notin);
    Set EX = mk(); for (long h = 0; h < BL.qn; h++) if (!has(&TX, BL.q[h])) add(&EX, BL.q[h]);
    printf("extra classes: %ld (%ld tables)\n", EX.qn, EX.qn << (n + 1));
    /* orbits of extras under the group, by flood fill */
    uint8_t *done = calloc(((uint64_t)1 << N) / 8 + 1, 1); long orbits = 0;
    uint64_t *stk = malloc(sizeof(uint64_t) * 40000000);
    for (long h = 0; h < EX.qn; h++) { uint64_t T = EX.q[h]; if (done[T >> 3] >> (T & 7) & 1) continue;
        orbits++; long sp = 0, sz = 0; stk[sp++] = T; done[T >> 3] |= 1 << (T & 7); uint64_t mn = T;
        while (sp) { uint64_t U = stk[--sp]; sz++; if (U < mn) mn = U;
            uint64_t nb[8]; int k = 0; for (int i = 0; i + 1 < n; i++) nb[k++] = canon(swp(U, i, i + 1)); if (n) nb[k++] = canon(flp(U, 0));
            for (int e = 0; e < k; e++) { uint64_t V = nb[e]; if (!(done[V >> 3] >> (V & 7) & 1)) { done[V >> 3] |= 1 << (V & 7); stk[sp++] = V; } } }
        printf("  extra orbit %ld: %ld classes, min canonical table 0x%llx\n", orbits, sz, (unsigned long long)mn);
    }
    if (n == 4) { /* bit 1 of x1+x2+x3+x4 */
        uint64_t g = 0; for (int x = 0; x < N; x++) if ((__builtin_popcount(x) >> 1) & 1) g |= (uint64_t)1 << x;
        printf("canon(bit1(x1+..+x4)) = 0x%llx, in extras: %d\n", (unsigned long long)canon(g), has(&EX, canon(g)));
    }
    return 0;
}
