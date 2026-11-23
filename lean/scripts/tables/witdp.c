/* The dynamic program of app:correction-tests, with back-pointers.

   Usage: witdp p d1 d2 d3 d4 d5 [-a] < codes > witnesses

   The host is the diagonal lattice J = <d1, ..., d5> at the prime p = 2 or 3. A Gram residue
   (a, b, c, d, e, f) is taken modulo (8, 4, 8, 4, 4, 8) at 2 and modulo 9 at 3, and coded as a
   number in mixed radix (`code`). A residue is accepted when it is [X^T J X]_p for an integer
   5 x 3 matrix X whose rows span F_p^3 modulo p.

   The program adds the rows of X one at a time. A state after r rows is the pair (span of the
   rows modulo p, residue of the partial sum of d_i v_i v_i^T); row i runs over the vectors modulo
   4 at p = 2, modulo 9 at p = 3, and modulo 3 at p = 3 when 3 | d_i (these moduli determine both
   parts of the state). Each state records the first predecessor and row that reach it.

   With -a, print the code of every accepted residue, one per line, in increasing order.
   Otherwise, for each code on stdin, print the 15 entries of a matrix X (row by row) that
   witnesses it, or NONE. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static int P;              /* the prime */
static int NV;             /* the number of vectors of F_p^3 */
static int SIZE;           /* the number of residues */
static int mod_[6];        /* the moduli of the six entries */
static int nsub;           /* the number of subspaces found so far */
static unsigned subs[64];  /* the subspaces of F_p^3, as bitsets of their vectors */

static int vid(int x, int y, int z) { return (x * P + y) * P + z; }

/* The span of a set of vectors (closure under v + t w). */
static unsigned closure(unsigned m) {
  int changed = 1;
  while (changed) {
    changed = 0;
    for (int i = 0; i < NV; i++) {
      if (!(m >> i & 1)) continue;
      for (int j = 0; j < NV; j++) {
        if (!(m >> j & 1)) continue;
        int xi = i / (P * P), yi = i / P % P, zi = i % P;
        int xj = j / (P * P), yj = j / P % P, zj = j % P;
        for (int t = 0; t < P; t++) {
          int k = vid((xi + t * xj) % P, (yi + t * yj) % P, (zi + t * zj) % P);
          if (!(m >> k & 1)) { m |= 1u << k; changed = 1; }
        }
      }
    }
  }
  return m;
}

/* The index of a subspace, added to the list if new. */
static int subid(unsigned m) {
  for (int i = 0; i < nsub; i++)
    if (subs[i] == m) return i;
  subs[nsub] = m;
  return nsub++;
}

static int code(const int *g) {
  int c = 0;
  for (int i = 0; i < 6; i++) c = c * mod_[i] + ((g[i] % mod_[i]) + mod_[i]) % mod_[i];
  return c;
}

static void decode(int c, int *g) {
  for (int i = 5; i >= 0; i--) { g[i] = c % mod_[i]; c /= mod_[i]; }
}

int main(int argc, char **argv) {
  if (argc < 7) { fprintf(stderr, "usage: witdp p d1 d2 d3 d4 d5 [-a]\n"); return 2; }
  P = atoi(argv[1]);
  int dd[5];
  for (int i = 0; i < 5; i++) dd[i] = atoi(argv[2 + i]);
  int list_accepted = argc > 7 && strcmp(argv[7], "-a") == 0;
  int q = P == 2 ? 8 : 9, r = P == 2 ? 4 : 9;
  int mm[6] = {q, r, q, r, r, q};
  memcpy(mod_, mm, sizeof mm);
  NV = P * P * P;
  SIZE = 1;
  for (int i = 0; i < 6; i++) SIZE *= mod_[i];

  /* All subspaces, from {0} by adjoining vectors, and the table join[s][v] = span(s, v). */
  subid(1u);
  for (int it = 0; it < nsub; it++)
    for (int v = 0; v < NV; v++) subid(closure(subs[it] | (1u << v)));
  int *join = malloc(sizeof(int) * nsub * NV);
  for (int s = 0; s < nsub; s++)
    for (int v = 0; v < NV; v++) join[s * NV + v] = subid(closure(subs[s] | (1u << v)));
  int full = -1;
  for (int s = 0; s < nsub; s++)
    if (__builtin_popcount(subs[s]) == NV) full = s;

  /* pred[st][span * SIZE + code]: -1 if unreached after st rows, else
     (previous span * SIZE + previous code) * 1000 + (row digits i j k). */
  int64_t *pred[6];
  for (int st = 0; st <= 5; st++) {
    pred[st] = malloc(sizeof(int64_t) * nsub * SIZE);
    for (long i = 0; i < (long)nsub * SIZE; i++) pred[st][i] = -1;
  }
  int g0[6] = {0, 0, 0, 0, 0, 0};
  pred[0][code(g0)] = 0;
  int *dig = malloc(sizeof(int) * SIZE * 6);
  for (int c = 0; c < SIZE; c++) decode(c, dig + 6 * c);

  for (int st = 0; st < 5; st++) {
    int d = dd[st];
    int per = P == 2 ? 4 : (d % 3 == 0 ? 3 : 9);
    for (int s = 0; s < nsub; s++)
      for (int c = 0; c < SIZE; c++) {
        if (pred[st][(long)s * SIZE + c] < 0) continue;
        for (int i = 0; i < per; i++)
          for (int j = 0; j < per; j++)
            for (int k = 0; k < per; k++) {
              int s2 = join[s * NV + vid(i % P, j % P, k % P)];
              int con[6] = {d * i * i, d * i * j, d * j * j, d * i * k, d * j * k, d * k * k};
              int g[6];
              for (int t = 0; t < 6; t++) g[t] = dig[6 * c + t] + con[t];
              long idx = (long)s2 * SIZE + code(g);
              if (pred[st + 1][idx] < 0)
                pred[st + 1][idx] = ((int64_t)s * SIZE + c) * 1000 + (i * 100 + j * 10 + k);
            }
      }
  }

  if (list_accepted) {
    for (int c = 0; c < SIZE; c++)
      if (pred[5][(long)full * SIZE + c] >= 0) printf("%d\n", c);
    return 0;
  }
  int target;
  while (scanf("%d", &target) == 1) {
    long idx = (long)full * SIZE + target;
    if (pred[5][idx] < 0) { printf("NONE\n"); continue; }
    int rows[5][3];
    long cur = idx;
    for (int st = 5; st >= 1; st--) {
      int64_t pr = pred[st][cur];
      int rr = (int)(pr % 1000);
      rows[st - 1][0] = rr / 100;
      rows[st - 1][1] = rr / 10 % 10;
      rows[st - 1][2] = rr % 10;
      cur = pr / 1000;
    }
    for (int i = 0; i < 5; i++)
      for (int j = 0; j < 3; j++) printf("%d ", rows[i][j]);
    printf("\n");
  }
  return 0;
}
