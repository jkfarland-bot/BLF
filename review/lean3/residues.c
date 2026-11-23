/* Verifier's own residue enumeration.
 * bit j of N depends only on N mod 2^(j+1), so for fixed j the functions
 * x -> bit j of (K + a.x) are obtained with K, a_i ranging over residues mod 2^(j+1).
 * Since bit j of N = bit j+1 of 2N, the sets grow with j; we report the union up to each j.
 *
 * mode "count n jmax": |{f : f = bit j (K + a.x), j <= jmax}| for n variables.
 * mode "gated jmax": for each j <= jmax, is z && T(x) (T = [x1+2x2+2x3+3x4 >= 5]) with z the
 *   fifth variable (index 4) equal to bit j of K + a.x + c z for some residues?
 * mode "fn n jmax hexmask": is the n-variable function with truth table hexmask bit j of an
 *   integer affine form for some j <= jmax (reports each j).
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

static int bitj(long N, int j) { /* floor semantics, N may be negative: use mod */
  long M = 1L << (j + 1);
  long r = ((N % M) + M) % M;
  return (int)((r >> j) & 1);
}

/* enumerate all (K, a) mod M for n vars; callback on mask; returns via global bitmap */
static uint8_t *seen;
static uint64_t target;
static int found;

static void enumerate(int n, int j, int want_target) {
  long M = 1L << (j + 1);
  int N = 1 << n;
  long a[8] = {0};
  long s[256];
  for (;;) {
    for (int v = 0; v < N; v++) {
      long t = 0;
      for (int i = 0; i < n; i++) if ((v >> i) & 1) t += a[i];
      s[v] = t;
    }
    for (long K = 0; K < M; K++) {
      uint64_t mask = 0;
      for (int v = 0; v < N; v++) if (bitj(K + s[v], j)) mask |= (1ULL << v);
      if (want_target) { if (mask == target) { found = 1; return; } }
      else seen[mask] = 1;
    }
    int i = 0;
    while (i < n) { a[i]++; if (a[i] < M) break; a[i] = 0; i++; }
    if (i == n) break;
  }
}

int main(int argc, char **argv) {
  if (argc >= 4 && !strcmp(argv[1], "count")) {
    int n = atoi(argv[2]), jmax = atoi(argv[3]);
    size_t sz = (size_t)1 << (1 << n);
    seen = calloc(sz, 1);
    for (int j = 0; j <= jmax; j++) {
      enumerate(n, j, 0);
      size_t c = 0;
      for (size_t m = 0; m < sz; m++) c += seen[m];
      printf("n=%d union over j<=%d: %zu\n", n, j, c);
      fflush(stdout);
    }
    return 0;
  }
  if (argc >= 5 && !strcmp(argv[1], "fn")) {
    int n = atoi(argv[2]), jmax = atoi(argv[3]);
    target = strtoull(argv[4], NULL, 16);
    for (int j = 0; j <= jmax; j++) {
      found = 0;
      enumerate(n, j, 1);
      printf("n=%d mask=%s bit %d: %s\n", n, argv[4], j, found ? "REALIZABLE" : "not realizable");
      fflush(stdout);
    }
    return 0;
  }
  fprintf(stderr, "usage\n");
  return 2;
}
