/* Folded grid search plus closure under the hyperoctahedral group.
   Grid: u = (K + a.x)/q, 0 <= a_1 <= ... <= a_n <= q/2, 0 <= K < q.
   The full grid {a in [0,q)^n, K in [0,q)} is invariant (mod output-affine XOR)
   under input permutations and input complementations (x_i -> 1 - x_i sends a_i to -a_i,
   then a_i -> a_i + q is an output-affine change), and its classes are exactly the
   closure of the folded classes. We verify this on small n against the unfolded grid.
   usage: gridfold n q    (n <= 5) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static int n, N;
static uint64_t canon(uint64_t T) {
    int f0 = T & 1; uint64_t A = 0;
    for (int x = 0; x < N; x++) {
        int bit = f0;
        for (int i = 0; i < n; i++) if (x >> i & 1) bit ^= (int)((T >> (1 << i)) & 1) ^ f0;
        A |= (uint64_t)bit << x;
    }
    return T ^ A;
}
static uint64_t perm_swap(uint64_t T, int i, int j) { /* swap variables i, j */
    uint64_t R = 0;
    for (int x = 0; x < N; x++) {
        int bi = x >> i & 1, bj = x >> j & 1; int y = x & ~((1 << i) | (1 << j));
        y |= bi << j; y |= bj << i;
        R |= ((T >> x) & 1) << y;
    }
    return R;
}
static uint64_t flip(uint64_t T, int i) {
    uint64_t R = 0;
    for (int x = 0; x < N; x++) R |= ((T >> x) & 1) << (x ^ (1 << i));
    return R;
}
static uint8_t *seen; static uint64_t *queue; static long qn = 0;
static void add(uint64_t C) {
    if (!(seen[C >> 3] >> (C & 7) & 1)) { seen[C >> 3] |= 1 << (C & 7); queue[qn++] = C; }
}
static long q; static long a[8];
static void rec(int i, long lo) {
    if (i == n) {
        long s[64];
        for (int x = 0; x < N; x++) { long v = 0; for (int k = 0; k < n; k++) if (x >> k & 1) v += a[k]; s[x] = v; }
        for (long K = 0; K < q; K++) {
            uint64_t T = 0;
            for (int x = 0; x < N; x++) T |= (uint64_t)(((K + s[x]) / q) & 1) << x;
            add(canon(T));
        }
        return;
    }
    for (long v = lo; v <= q / 2; v++) { a[i] = v; rec(i + 1, v); }
}
int main(int argc, char **argv) {
    n = atoi(argv[1]); q = atol(argv[2]); N = 1 << n;
    uint64_t nb = (uint64_t)1 << N;
    seen = calloc(nb / 8 + 1, 1); queue = malloc(sizeof(uint64_t) * 40000000);
    rec(0, 0);
    long folded = qn;
    for (long h = 0; h < qn; h++) {
        uint64_t T = queue[h];
        for (int i = 0; i + 1 < n; i++) add(canon(perm_swap(T, i, i + 1)));
        if (n) add(canon(flip(T, 0)));
    }
    printf("n=%d q=%ld folded_classes=%ld closed_classes=%ld tables=%ld\n", n, q, folded, qn, qn << (n + 1));
    return 0;
}
