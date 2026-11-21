/* Output-affine classes of BLF(n) met by the grid u = (K + a.x)/q, a_i, K in [0,q).
   f(x) = floor((K + a.x)/q) mod 2 = bit log2(q) of K + a.x.
   Class representative: XOR the unique affine function making f(0) = f(e_i) = 0.
   Prints the number of classes and |classes| * 2^(n+1). usage: grid n q */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
int main(int argc, char **argv) {
    int n = atoi(argv[1]); long q = atol(argv[2]);
    int N = 1 << n;
    /* canonical form leaves 2^n - n - 1 free bits; index bitset by full table >> nothing:
       simpler: bitset over full 2^N tables for n <= 5 (2^32 bits = 512 MB) */
    uint64_t nbits = (uint64_t)1 << N;
    uint8_t *seen = calloc(nbits / 8 + 1, 1);
    if (!seen) { fprintf(stderr, "alloc\n"); return 1; }
    long total = 1; for (int i = 0; i < n; i++) total *= q;
    long *s = malloc(sizeof(long) * N);
    long classes = 0;
    for (long code = 0; code < total; code++) {
        long a[8]; long c = code;
        for (int i = 0; i < n; i++) { a[i] = c % q; c /= q; }
        for (int x = 0; x < N; x++) { long v = 0; for (int i = 0; i < n; i++) if (x >> i & 1) v += a[i]; s[x] = v; }
        for (long K = 0; K < q; K++) {
            uint64_t T = 0;
            for (int x = 0; x < N; x++) {
                /* floor((K + a.x)/q) mod 2, a.x not reduced */
                long w = K + s[x]; T |= (uint64_t)((w / q) & 1) << x; }
            /* canonicalize */
            int f0 = T & 1; uint64_t A = 0;
            for (int x = 0; x < N; x++) {
                int bit = f0;
                for (int i = 0; i < n; i++) if (x >> i & 1) bit ^= (int)((T >> (1 << i)) & 1) ^ f0;
                A |= (uint64_t)bit << x;
            }
            uint64_t C = T ^ A;
            if (!(seen[C >> 3] >> (C & 7) & 1)) { seen[C >> 3] |= 1 << (C & 7); classes++; }
        }
    }
    printf("n=%d q=%ld classes=%ld tables=%ld\n", n, q, classes, classes << (n + 1));
    return 0;
}
