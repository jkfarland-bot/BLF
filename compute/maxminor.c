/* Largest |det| of an (n+2)x(n+2) matrix whose rows are taken from
   {(1, x, s) : x in {0,1}^n, s in {+1,-1}}  (cell-constraint normals, unfolded,
   variables t, r_1..r_n, delta). Exact integer Bareiss on every subset.
   usage: maxminor n */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef long long ll;
static int n, d, R;
static int rows[256][10];
static int idx[10];
static ll best = 0; static ll cnt = 0;
static ll detB(int m[10][10]) {
    ll a[10][10]; int sign = 1;
    for (int i = 0; i < d; i++) for (int j = 0; j < d; j++) a[i][j] = m[i][j];
    ll prev = 1;
    for (int k = 0; k < d - 1; k++) {
        if (a[k][k] == 0) {
            int p = -1;
            for (int i = k + 1; i < d; i++) if (a[i][k]) { p = i; break; }
            if (p < 0) return 0;
            for (int j = 0; j < d; j++) { ll t = a[k][j]; a[k][j] = a[p][j]; a[p][j] = t; }
            sign = -sign;
        }
        for (int i = k + 1; i < d; i++) for (int j = k + 1; j < d; j++)
            a[i][j] = (a[i][j] * a[k][k] - a[i][k] * a[k][j]) / prev;
        prev = a[k][k];
    }
    return sign * a[d - 1][d - 1];
}
static void rec(int start, int depth) {
    if (depth == d) {
        int m[10][10];
        for (int i = 0; i < d; i++) memcpy(m[i], rows[idx[i]], sizeof(int) * d);
        ll v = detB(m); if (v < 0) v = -v;
        cnt++;
        if (v > best) { best = v; fprintf(stderr, "new max %lld at", v);
            for (int i = 0; i < d; i++) fprintf(stderr, " %d", idx[i]); fprintf(stderr, "\n"); }
        return;
    }
    for (int i = start; i <= R - (d - depth); i++) { idx[depth] = i; rec(i + 1, depth + 1); }
}
int main(int argc, char **argv) {
    n = atoi(argv[1]); d = n + 2; R = 0;
    for (int x = 0; x < (1 << n); x++) for (int s = 1; s >= -1; s -= 2) {
        rows[R][0] = 1;
        for (int i = 0; i < n; i++) rows[R][1 + i] = (x >> i) & 1;
        rows[R][n + 1] = s; R++;
    }
    /* WLOG the first chosen row is fixed up to symmetry? no: full enumeration */
    rec(0, 0);
    printf("n=%d rows=%d subsets=%lld maxdet=%lld\n", n, R, cnt, best);
    return 0;
}
