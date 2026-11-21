/* Weight bound for threshold functions (Cramer). A threshold function T(x) = [s(x) = +1] has a
   realization y with s(x) (1,x).y >= 1 for all x; the polyhedron is pointed (the vectors (1,x) span),
   so it has a vertex y = B^-1 1 for n+1 tight rows s(x)(1,x). Then Y = |det B| y is an integer
   realization (s(x)(1,x).Y >= |det B| >= 1) whose k-th entry is +-det of B with column k replaced by
   the all-ones vector, i.e. +-det of the matrix with rows (1, x) except entry k replaced by s(x).
   This program computes M_n = max over k and over (n+1)-row choices of |det| of such matrices, so every
   threshold function has an integer realization T(x) = [Y_0 + Y.x > 0] with |Y_k| <= M_n.
   usage: twbound n */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef long long ll;
static int n, d, R; static int rows[256][10]; static int idx[10]; static ll best = 0;
static ll detB(int m[10][10]) {
    ll a[10][10]; int sign = 1; ll prev = 1;
    for (int i = 0; i < d; i++) for (int j = 0; j < d; j++) a[i][j] = m[i][j];
    for (int k = 0; k < d - 1; k++) {
        if (a[k][k] == 0) { int p = -1; for (int i = k + 1; i < d; i++) if (a[i][k]) { p = i; break; }
            if (p < 0) return 0; for (int j = 0; j < d; j++) { ll t = a[k][j]; a[k][j] = a[p][j]; a[p][j] = t; } sign = -sign; }
        for (int i = k + 1; i < d; i++) for (int j = k + 1; j < d; j++) a[i][j] = (a[i][j] * a[k][k] - a[i][k] * a[k][j]) / prev;
        prev = a[k][k];
    }
    return sign * a[d - 1][d - 1];
}
static void rec(int start, int depth) {
    if (depth == d) { int m[10][10]; for (int i = 0; i < d; i++) memcpy(m[i], rows[idx[i]], sizeof(int) * d);
        ll v = detB(m); if (v < 0) v = -v; if (v > best) best = v; return; }
    for (int i = start; i <= R - (d - depth); i++) { idx[depth] = i; rec(i + 1, depth + 1); }
}
int main(int argc, char **argv) {
    n = atoi(argv[1]); d = n + 1;
    for (int k = 0; k <= n; k++) {
        R = 0;
        for (int x = 0; x < (1 << n); x++) for (int s = 1; s >= -1; s -= 2) {
            rows[R][0] = 1; for (int i = 0; i < n; i++) rows[R][1 + i] = (x >> i) & 1;
            rows[R][k] = s; R++;
        }
        rec(0, 0);
    }
    printf("n=%d M_n=%lld\n", n, best);
    return 0;
}
