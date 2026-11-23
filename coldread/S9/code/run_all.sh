#!/bin/sh
# Runs every check of the cold read of Section 9 (single thread, Python only).
set -e
cd "$(dirname "$0")"
echo "== blf_small.py (BLF(3), elementary rules, Corollary 5.3 cross-check)"; python3 blf_small.py
echo "== thm95.py thm 8 (Theorem 9.5, all 256 rules, k=1,2,3, N<=8)"; python3 thm95.py thm 8
echo "== thm95.py thm 10 (same, N<=10)"; python3 thm95.py thm 10 | grep -E "^k=|rows"
echo "== thm95.py prop 8 (Proposition 9.4, 208 BLF rules, k=1, N<=8)"; python3 thm95.py prop 8
echo "== thm95.py big 12 (Rule 110, k=2 and 3, rows of 256 cells)"; python3 thm95.py big 12
echo "== general_tables.py (Theorem 9.5, random tables, r=1..5, offsets)"; python3 general_tables.py 7 40
echo "== cor93.py (Corollary 9.3)"; python3 cor93.py
echo "== lemma91.py (Lemma 9.1 construction)"; python3 lemma91.py 300
echo "== excluded_case.py (Proposition 9.2 excluded case; counting stress test)"; python3 excluded_case.py
echo "== fixed_encoding_probe.py 12 (Prop 9.4 with a fixed small encoding; inconclusive probe)"; python3 fixed_encoding_probe.py 12
