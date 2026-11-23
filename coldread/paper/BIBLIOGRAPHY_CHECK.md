# Bibliography check for blf.tex

Checked 23 Nov 2026 against /home/claude/paper_blf/blf.tex (not modified). 19 \bibitem entries are present: the 18 outside references plus BLFrepo, the author's own repository. All 19 are cited in the text, and no \cite key is missing from the bibliography.

Sources used: Crossref metadata (api.crossref.org), arXiv PDFs, author-site preprints, the MIT DSpace record and a later RLE report that cites Spann, OEIS JSON, the NeurIPS proceedings record and researchr, and mathnet.ru. Not reachable from here: ams.org (bot check), link.springer.com and the Spann QPR 76 scan itself. So the journal numbering for KKS and ERS, and the journal versus arXiv numbering for Moci, rest on the evidence described under each entry.

Legend: VERIFIED = all details match. CORRECTED = a fix is suggested, with replacement \bibitem text. PARTLY VERIFIED = the bibliographic data is verified but a cited statement number could not be fully confirmed.

---

## 1. AlonVu97: VERIFIED

Crossref (DOI 10.1006/jcta.1997.2780) gives J. Combin. Theory Ser. A 79 (1997), no. 1, 133-160. The authors (Alon, Vu) and the title match.

What they prove (from the authors' preprint, web.math.princeton.edu/~nalon/PDFS/av1.pdf):
- Main Theorem: for i = 1, 2 ({0,1} and {-1,1} matrices), 2^{(1/2) n log n - n(1+o(1))} >= chi_i(n) >= 2^{(1/2) n log n - n(2+o(1))} for every n. The upper bound comes from Hadamard's inequality and 2^{n-1} | det.
- Theorem 2.1.1 and Corollary 2.2.2: for n a power of 2 there is a matrix with chi = 2^{(1/2) n log n - n(1+o(1))}.
- Theorem 3.3.1: 2^{(1/2) n log n - n(2+o(1))} <= w(n) <= 2^{(1/2) n log n - n(1+o(1))} for the threshold weights w(n), for all n.

So the sentence in the status line of Announced Result ann:ah is accurate for chi(n). Lower-order term: -n(1+o(1)) for powers of two, -n(2+o(1)) in general.

Caveat: ann:ah also talks about w(n). For powers of two, the lower bound on w(n) is due to Håstad (1994), not to Alon and Vu. Alon and Vu say so themselves: Håstad's bound is (1/2n) e^{-4 n^beta} 2^{(1/2) n log n - n}. The text should credit Håstad if it compares the power-of-two case for w(n). See the missing references below.

Optional precision: "\cite[Main Theorem and Theorem~2.1.1]{AlonVu97}".

## 2. BHP01: VERIFIED

Crossref (DOI 10.1112/plms/83.3.532) gives R. C. Baker, G. Harman and J. Pintz, "The difference between consecutive primes, II", Proc. London Math. Soc. (3) 83 (2001), no. 3, 532-562. This is the standard source for the prime-gap exponent 0.525, which is the use made of it.

## 3. Bjorner92: VERIFIED (small addition suggested)

Crossref (DOI 10.1017/CBO9780511662041.008) gives A. Björner, "Homology and shellability of matroids and geometric lattices", in Matroid Applications, Cambridge University Press, 1992, 226-283. Suggested fuller form, with editor and series:

```
\bibitem{Bjorner92} A.~Bj\"orner, The homology and shellability of matroids and geometric lattices, in
N.~White (ed.), \emph{Matroid Applications}, Encyclopedia Math. Appl. 40, Cambridge University Press,
1992, 226-283.
```

It is the standard reference for |mu| = number of nbc bases, which is the use made of it.

## 4. BLFrepo: VERIFIED

https://github.com/jkfarland-bot/BLF returns HTTP 200 and is public. The author name matches \author.

## 5. BohossianBruck97: CORRECTED (pages and publisher missing)

The NeurIPS proceedings record and researchr give V. Bohossian and J. Bruck, "Multiple Threshold Neural Logic", Advances in Neural Information Processing Systems 10 (NIPS 1997), M. I. Jordan, M. J. Kearns and S. A. Solla (eds.), MIT Press, pp. 252-258. The proceedings volume appeared in 1998; researchr lists the year as 1997.

```
\bibitem{BohossianBruck97} V.~Bohossian and J.~Bruck, Multiple threshold neural logic, in
M.~I.~Jordan, M.~J.~Kearns and S.~A.~Solla (eds.), \emph{Advances in Neural Information Processing
Systems} 10 (NIPS 1997), MIT Press, 1998, 252-258.
```

## 6. Cover65: VERIFIED

Crossref (DOI 10.1109/PGEC.1965.264137) gives T. M. Cover, IEEE Trans. Electron. Comput. EC-14 (1965), no. 3, 326-334.

The use is correct. Cover's function counting theorem gives C(N,d) = 2 sum_{k=0}^{d-1} binom(N-1,k) homogeneous linear dichotomies for N points in general position in R^d. With N = 2^n and d = n+1 this is 2 sum_{i=0}^{n} binom(2^n - 1, i), as in the paper.

Minor point: Cover states the count as an equality for points in general position. The cube points v_x are not in general position, so the paper uses it as an upper bound. That use is standard and correct, because degenerate position can only lose regions. The paper could add the phrase "(an upper bound for points in arbitrary position)".

## 7. ERS09: VERIFIED (bibliographic); theorem numbering clarified

Crossref (DOI 10.1007/s00454-009-9134-x) gives Discrete Comput. Geom. 41 (2009), no. 4, 481-512. The authors are listed as Richard Ehrenborg, Margaret Readdy and "MLE Slone"; the author-site version gives "Michael Slone". So "M. Slone" is correct.

The numbering differs between versions:
- arXiv 0810.0295v1 (Oct 2008): Theorem 3.5 is the characteristic polynomial as a valuation. Theorem 3.6 is the region count: number of regions = (-1)^n chi(H; t=0), when the regions are open balls. Theorem 3.11 is the region count as the toric Zaslavsky invariant Z_t(P) = sum over coatoms x of P of |mu(0̂, x)|, the coatoms being the vertices.
- Revised version on the authors' site (www.ms.uky.edu/~readdy/Papers/Affine_toric.pdf; abstract reworded, author given as Michael Slone, almost certainly the accepted text): Theorem 3.4 is the characteristic polynomial. Theorem 3.5 is the region count (-1)^n chi(H; t=0). Theorem 3.6 is the lattice-point count. Theorem 3.10 is the region count as Z_t(P), the sum over vertices of |mu|.

The Springer page could not be fetched, so the journal numbering is inferred from the revised preprint.

Answer to the question: the journal version almost certainly has the region count (-1)^n chi(0) as Theorem 3.5. The formula the paper actually uses, the sum over vertices of |mu|, is Theorem 3.10 (Theorem 3.11 on arXiv). Theorem 3.6 is the region count only in the arXiv v1 numbering.

Recommendation: keep "\cite[Section~3]{ERS09}", which is correct in every version, or write "\cite[Theorem~3.10]{ERS09}". The hypothesis "regions are open balls" holds exactly when the normals span, which the paper states.

Convention note: ERS order the intersection poset with the torus as 0̂ and the vertices as coatoms, so the term is |mu(0̂, p)|. The paper writes |mu(p, 1̂)| "in the poset of layers", which is right only if the poset is ordered by inclusion, with the torus at the top. Moci orders the poset of layers by reverse inclusion, so in his convention the term is mu(0̂, p). Suggest adding "(ordered by inclusion)" or switching to mu(0̂, p).

## 8. FJZ22: VERIFIED; theorem number 1.6 is right for the journal version

Crossref and the journal PDF give Combin. Probab. Comput. 31 (2022), no. 3, 455-477, DOI 10.1017/S0963548321000377, first published online 10 Sept 2021. The authors (Ferber, Jain, Zhao) and the title match.

- Journal version: Theorem 1.6 (Kahn-Komlós-Szemerédi). There is a constant C > 0 such that if r <= n - C and v_1, ..., v_r are i.i.d. uniform in {±1}^n, then P[d_±(span{v_1, ..., v_r}) > log_2(2r)] = (1+o(1)) 4 binom(r,3) (3/4)^n. Here d_± is the combinatorial dimension (Definition 1.5), so the event says the span contains more than 2r sign vectors.
- arXiv 1808.07222 (v1 only, Aug 2018): the same statement is Theorem 1.7, and the definition is 1.6.

The paper's Theorem thm:kks matches this exactly with n = d. Since the bibitem cites the journal, "Theorem~1.6" is correct. Optional: add "doi:10.1017/S0963548321000377", or note "(Theorem 1.7 in arXiv:1808.07222)".

## 9. Haring66: VERIFIED

Crossref (DOI 10.1109/PGEC.1966.264375) gives D. R. Haring, "Multi-threshold threshold elements", IEEE Trans. Electron. Comput. EC-15 (1966), no. 1, 45-65.

## 10. HaringOhori67: VERIFIED (title spelling)

Crossref (DOI 10.1109/PGEC.1967.264576) gives D. R. Haring and D. Ohori, "A Tabular Method for the Synthesis of Multithreshold Threshold Elements", IEEE Trans. Electron. Comput. EC-16 (1967), no. 2, 216-220. The only difference is that IEEE spells "Multithreshold" without the hyphen. Optional fix:

```
\bibitem{HaringOhori67} D.~R.~Haring and D.~Ohori, A tabular method for the synthesis of multithreshold
threshold elements, \emph{IEEE Trans. Electron. Comput.} EC-16 (1967), 216-220.
```

## 11. KKS95: PARTLY VERIFIED

The AMS record (DOI 10.1090/S0894-0347-1995-1260107-2, MR1260107) gives J. Kahn, J. Komlós and E. Szemerédi, J. Amer. Math. Soc. 8 (1995), 223-240. The bibliographic data is correct.

Statement number: the PDF is behind an AMS bot check, so I could not read KKS directly. arXiv:2405.05082 (on subspaces spanned by ±1 vectors) states that KKS "showed (corollary 4, [KKS])" that Odlyzko's theorem extends to p <= n - C. That theorem is: P(span of p random ±1 vectors contains a ±1 vector other than ±v_i) = P_3 + small error, with P_3 = 4 binom(p,3)(3/4)^n (1+o(1)). So Corollary 4 is confirmed as the right statement. The sub-label "(b)" could not be confirmed.

Recommendation: unless someone checks the printed page, cite "\cite[Corollary~4]{KKS95}" or keep only the FJZ Theorem 1.6 citation, which is verified.

The formula 4 binom(r,3)(3/4)^n itself is due to Odlyzko (1988) in the range r <= n - 10n/log n. KKS extended it to r <= n - C. Citing Odlyzko as well would be fair (see missing references).

## 12. Knuth4A: VERIFIED

D. E. Knuth, The Art of Computer Programming, Vol. 4A: Combinatorial Algorithms, Part 1, Addison-Wesley, 2011. Section 7.1.3, "Bitwise tricks and techniques", is where broadword computing is treated, which is the use made of it.

Threshold functions are treated in Section 7.1.1, which OEIS A000609 cites at p. 79. If the paper ever cites Knuth for threshold functions, it should use 7.1.1. Optional fuller title:

```
\bibitem{Knuth4A} D.~E.~Knuth, \emph{The Art of Computer Programming}, Vol.~4A: Combinatorial
Algorithms, Part~1, Addison-Wesley, 2011, Section~7.1.3.
```

## 13. Moci12: VERIFIED (bibliographic); Corollary 5.16 and Proposition 2.2 verified in arXiv v5

Crossref (DOI 10.1090/S0002-9947-2011-05491-7) gives L. Moci, "A Tutte polynomial for toric arrangements", Trans. Amer. Math. Soc. 364 (2012), no. 2, 1067-1088.

In arXiv 0911.4823v5 (9 Nov 2010, the final arXiv version; the AMS page could not be fetched):
- Theorem 5.15: R(X) = (-1)^n chi(0), the number of regions of the compact (real) toric arrangement, attributed to ERS.
- Corollary 5.16: R(X) = M_X(1,0).
- Proposition 2.2: M_X(1,1) equals the volume of the zonotope Z(X), that is, sum over bases B of |det B|.

Both cited numbers are right, and what they say fits the use. Prop 2.2 gives D_n = M_X(1,1). Since M_X has nonnegative coefficients, R_n = M_X(1,0) <= M_X(1,1) = D_n, so "compare" is apt.

Suggestion: Corollary 5.16 expresses R as M_X(1,0), not as a sum over vertices of |mu|. For the vertex sum, "\cite[Theorem~5.15]{Moci12}" (regions = (-1)^n chi(0)) together with ERS Theorem 3.10 is the more literal pair.

Applicability: Moci treats central toric arrangements (hypersurfaces chi(t) = 1). The arrangement A_n, with walls z_0 + x.z in Z, is central, so Moci applies. The affine slice arrangement in the lower-bound proof is not central, and for that one only ERS applies. That is consistent with the text, which uses "the vertex formula on Sigma" from ERS.

## 14. Muroga71: VERIFIED (capitalization)

S. Muroga, Threshold Logic and Its Applications, Wiley-Interscience, New York, 1971. OEIS A000609 cites p. 38, Table 2.3.2. The title has "Its" capitalized:

```
\bibitem{Muroga71} S.~Muroga, \emph{Threshold Logic and Its Applications}, Wiley-Interscience, New York,
1971.
```

## 15. OEIS: VERIFIED

A000609 is "Number of threshold functions of n or fewer variables". Its data begins 2, 4, 14, 104, 1882, 94572, 15028134, 8378070864, ..., so the terms for n = 0..6 match those listed. The entry cites Muroga 1971 (p. 38, Table 2.3.2) and Knuth 4A Section 7.1.1 (p. 79). Optional: add "accessed November 2026".

## 16. Rota64: CORRECTED (journal name)

Crossref (DOI 10.1007/BF00531932) gives G.-C. Rota, "On the foundations of combinatorial theory I. Theory of Möbius functions", Zeitschrift für Wahrscheinlichkeitstheorie und Verwandte Gebiete 2 (1964), no. 4, 340-368. The bibitem drops "und Verw. Gebiete". The sign theorem used (mu alternates in sign on geometric lattices, so |mu| >= 1) is in this paper.

```
\bibitem{Rota64} G.-C.~Rota, On the foundations of combinatorial theory I. Theory of M\"obius functions,
\emph{Z. Wahrscheinlichkeitstheorie und Verw. Gebiete} 2 (1964), 340-368.
```

## 17. Spann65: VERIFIED (via the DSpace record and Spann's own later citation)

MIT DSpace (hdl 1721.1/54058) lists RLE Quarterly Progress Report No. 76, January 15, 1965, Section XIX "Processing and Transmission of Information", with R. N. Spann among the authors.

Spann's own later report, QPR No. 78 (1965), Section XIII.A "Bounds on multiple-threshold functions", pp. 207-210, cites: R. N. Spann, "Modular Threshold Functions," QPR No. 76, Research Laboratory of Electronics, M.I.T., January 15, 1965, pp. 241-247.

So the volume, pages and title in the bibitem are right. Optional: add the date.

```
\bibitem{Spann65} R.~N.~Spann, Modular threshold functions, \emph{Quarterly Progress Report} No.~76,
Research Laboratory of Electronics, MIT, January 15, 1965, 241-247.
```

I could not read the QPR 76 scan itself, because DSpace blocks automated download. So the claim that floor(u) mod 2 is "the balanced case" of Spann's modular threshold functions is not checked here. A human should check Spann's definition on p. 241.

Spann also proves in QPR 78, Theorem 3, that "for n > 10 the class of Modular Threshold functions does not contain all functions". That result is relevant to BLF and could be mentioned.

## 18. Wolfram83: VERIFIED

Crossref (DOI 10.1103/RevModPhys.55.601) gives S. Wolfram, "Statistical mechanics of cellular automata", Rev. Modern Phys. 55 (1983), no. 3, 601-644. This paper introduced the rule-numbering convention, which is the use made of it.

The 88 classes under reflection and complementation are standard. All 15 representatives listed in Corollary cor:ca (6, 9, 18, 27, 29, 33, 40, 46, 58, 72, 78, 130, 132, 172, 184) are among the standard 88 minimal representatives. If a source for "88" is wanted, the paper could add W. Li and N. Packard, "The structure of the elementary cellular automata rule space", Complex Systems 4 (1990), 281-297 (not re-verified here).

## 19. (count check) No duplicate or orphan keys

The 19 bibitems are AlonVu97, BHP01, Bjorner92, BLFrepo, BohossianBruck97, Cover65, ERS09, FJZ22, Haring66, HaringOhori67, KKS95, Knuth4A, Moci12, Muroga71, OEIS, Rota64, Spann65 and Wolfram83 (18 outside references), plus BLFrepo. Each is cited at least once.

---

# Missing references (suggested)

Each item below was checked on Crossref or the publisher record unless marked otherwise.

Closest prior work on the class itself, Boolean functions given by parallel equally spaced or alternating thresholds:

1. R. Takiyama, The separating capacity of a multithreshold threshold element, IEEE Trans. Pattern Anal. Mach. Intell. PAMI-7 (1985), 112-116. DOI 10.1109/TPAMI.1985.4767626. Counts dichotomies by sets of parallel hyperplanes with alternating labels, the closest counting precedent for BLF.
```
\bibitem{Takiyama85} R.~Takiyama, The separating capacity of a multithreshold threshold element,
\emph{IEEE Trans. Pattern Anal. Mach. Intell.} PAMI-7 (1985), 112-116.
```
2. R. Takiyama, The number of dichotomies and the separating capacity of a set of parallel hyperplanes: the information processing capability of the multithreshold threshold elements, Electron. Comm. Japan Part I 66 (1983), no. 5, 30-37. DOI 10.1002/ecja.4400660505.
3. S. Olafsson and Y. S. Abu-Mostafa, The capacity of multilevel threshold functions, IEEE Trans. Pattern Anal. Mach. Intell. 10 (1988), 277-281. DOI 10.1109/34.3890.
```
\bibitem{OlafssonAbuMostafa88} S.~Olafsson and Y.~S.~Abu-Mostafa, The capacity of multilevel threshold
functions, \emph{IEEE Trans. Pattern Anal. Mach. Intell.} 10 (1988), 277-281.
```
4. A. Ngom, I. Stojmenović and J. Žunić, On the number of multilinear partitions and the computing capacity of multiple-valued multiple-threshold perceptrons, IEEE Trans. Neural Networks 14 (2003), 469-477. DOI 10.1109/TNN.2003.810598.
5. R. N. Spann, Bounds on multiple-threshold functions, Quarterly Progress Report No. 78, Research Laboratory of Electronics, MIT, July 15, 1965, 207-210. Includes the theorem that modular threshold functions do not give all functions for n > 10.
6. P. Ercoli and L. Mercurio, Threshold logic with one or more than one threshold, in Information Processing 1962 (Proc. IFIP Congress 62, Munich), North-Holland, Amsterdam, 1963, 741-745. The earliest multi-threshold reference, cited by Spann. Verified only through Spann's citation; the publication year of the proceedings should be checked.
7. D. R. Haring and R. J. Diephuis, A realization procedure for multithreshold threshold elements, IEEE Trans. Electron. Comput. EC-16 (1967), 828-835. DOI 10.1109/PGEC.1967.264728.

For the anti-Hadamard and weight comparison (Announced Result ann:ah):

8. J. Håstad, On the size of weights for threshold gates, SIAM J. Discrete Math. 7 (1994), 484-492. DOI 10.1137/S0895480192235878. This is the source of the power-of-two lower bound for threshold weights that Alon and Vu extend.
```
\bibitem{Hastad94} J.~H{\aa}stad, On the size of weights for threshold gates, \emph{SIAM J. Discrete
Math.} 7 (1994), 484-492.
```

For Theorem thm:kks:

9. A. M. Odlyzko, On subspaces spanned by random selections of ±1 vectors, J. Combin. Theory Ser. A 47 (1988), 124-133. DOI 10.1016/0097-3165(88)90046-5. This is the origin of the 4 binom(r,3)(3/4)^n asymptotic, for r <= n - 10n/log n.
```
\bibitem{Odlyzko88} A.~M.~Odlyzko, On subspaces spanned by random selections of $\pm1$ vectors,
\emph{J. Combin. Theory Ser. A} 47 (1988), 124-133.
```

For toric region counts:

10. J. Lawrence, Enumeration in torus arrangements, European J. Combin. 32 (2011), 870-881. DOI 10.1016/j.ejc.2011.02.003. An independent treatment of region and face counts for torus arrangements.
11. I. Novik, A. Postnikov and B. Sturmfels, Syzygies of oriented matroids, Duke Math. J. 111 (2002), 287-317. DOI 10.1215/S0012-7094-02-11124-7. Counts regions of unimodular toric arrangements, and ERS cite it as the precedent.
12. Optional: L. Moci, "Combinatorics and topology of toric arrangements defined by root systems" and F. Ardila, F. Castillo and M. Henley, "The arithmetic Tutte polynomials of the classical root systems" (IMRN 2015) are further toric region counts. Not re-verified here.

For the threshold share (Corollary cor:share):

13. Yu. A. Zuev, Asymptotics of the logarithm of the number of threshold functions of the algebra of logic, Dokl. Akad. Nauk SSSR 306 (1989), no. 3, 528-530; English transl. in Soviet Math. Dokl. 39 (1989), no. 3, 512-513 (mathnet.ru). Shows log_2 T(n) ~ n^2. It complements the Cover upper bound and puts the share result in context.

No earlier paper was found that counts floor(u) mod 2 functions on the cube, or that links them to chambers of a toric arrangement. Searches for "modular threshold", "periodic threshold", "parity of a linear form" and "floor mod 2 affine Boolean" turned up nothing beyond the items above. This supports the paper's novelty claim, with the caveat that Spann's QPR 76 text was not read.
