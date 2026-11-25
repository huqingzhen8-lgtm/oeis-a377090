# Surjectivity and Logarithmic Deviation of OEIS A377090

Complete unconditional proofs and an exact rational-arithmetic counterexample certification for two conjectures on [OEIS A377090](https://oeis.org/A377090).

## Sequence Definition

The sequence **A377090** starts at $a_0 = 0$. For each $n \ge 1$, $a_n$ is the unvisited integer of smallest absolute value such that $|a_n - a_{n-1}|$ is prime, breaking ties in favor of the positive integer.

- **Sloane's Surjectivity Conjecture (Apr 30, 2025):** Every integer eventually appears in A377090.
- **Hasler's Logarithmic Deviation Conjecture (Feb 2025):** Letting $\delta_n := \bigl||a_n| - n/2\bigr|$, it was conjectured that $\delta_n = O(\log n)$ and specifically $\delta_n < 2\log(n+2)$ for all $n \ge 0$ (verified empirically up to $n = 10^5$).

## Main Results

1. **Surjectivity holds unconditionally (Theorem 1 & Theorem 2):**
   Every integer appears in A377090 exactly once ($V = \{a_n : n \ge 0\} = \mathbb{Z}$). Moreover, for any finite prefix $S_n = \{a_0, \dots, a_n\}$, the smallest unvisited radius $k_n = \min\{|h| : h \in \mathbb{Z} \setminus S_n\}$ satisfies
   $$k_n \ge \frac{c_1 n}{(\log n)^4}$$
   for all sufficiently large $n$ and an absolute constant $c_1 > 0$ (proved via an omitted-point greedy barrier and classical binary Goldbach mean-square bounds).

2. **Logarithmic bounds fail infinitely often (Theorem 3):**
   For any pair of consecutive primes $p < q$,
   $$\max_{p \le n \le q} \delta_n \ge \frac{q - p}{8}.$$
   By Westzynthius's large prime-gap theorem (and Bertrand's postulate $q < 2p$),
   $$\limsup_{n \to \infty} \frac{\delta_n}{\log(n+2)} = \infty.$$

3. **Earliest counterexample to $\delta_n < 2\log(n+2)$:**
   The inequality first fails at **$n = 370313$**, where $a_{370313} = -185183$ and
   $$\delta_{370313} = 26.5 > 2\log(370315) \approx 25.64421855.$$

## Prime-Gap Mechanism Around $n = 370313$

The earliest violation lies inside the large prime gap $[p, q] = [370261, 370373]$ of width $112$. Throughout $370261 \le n \le 370317$, all $57$ consecutive terms stay negative until the walk crosses zero via the exact prime step $q = 370373$ at $n = 370318$, after which all $56$ terms for $370318 \le n \le 370373$ remain positive:

| Index $n$ | Term $a_n$ | Step $\lvert a_n - a_{n-1}\rvert$ | Deviation $\delta_n$ | Bound $2\log(n+2)$ | Feature |
|---:|---:|---:|---:|---:|---|
| 370309 | -185180 | 2 | 25.5 | 25.64419694 | Closest prior near-miss |
| 370312 | -185181 | 2 | 25.0 | 25.64421315 | Preceding term |
| 370313 | -185183 | 2 | 26.5 | 25.64421855 | **First violation** |
| 370314 | -185185 | 2 | 28.0 | 25.64422395 | Gap peak attained |
| 370317 | -185186 | 2 | 27.5 | 25.64424015 | Last negative term in gap |
| 370318 | +185187 | 370373 | 28.0 | 25.64424555 | Sign flip (step $= q$) |

## Repository Contents

- [`paper/A377090_Surjectivity_and_Logarithmic_Deviation.pdf`](paper/A377090_Surjectivity_and_Logarithmic_Deviation.pdf) — Full 7-page English manuscript with complete proofs and tables.
- [`paper/a377090_proof.tex`](paper/a377090_proof.tex) — Portable LaTeX source (`article` class; compiles cleanly with `pdflatex`, `xelatex`, `lualatex`, or `tectonic`).
- [`verify_a377090.py`](verify_a377090.py) — Standalone Python 3 verification script using exact trial division and rational Taylor bounds for $e$ (no floating-point rounding in inequality checks).
- [`LICENSE`](LICENSE) — MIT License.

## Reproducing the Numerical Certification

Requires Python 3 (standard library only, no third-party packages):

```bash
python3 verify_a377090.py
```

Expected output:

```text
last (370313, -185183); first logarithmic violation (370313, -185183, 53)
deviation 26.5; bound 25.644218547556
```

To generate all terms up to $n = 370340$ on `stdout` (verified term-for-term against an independent sieve implementation and against the OEIS b-file [`b377090.txt`](https://oeis.org/A377090/b377090.txt) for $0 \le n \le 10000$):

```bash
python3 verify_a377090.py 370340 dump > a377090_0_370340.txt
```

## Building the Paper from Source

```bash
cd paper
tectonic a377090_proof.tex
# or: pdflatex a377090_proof.tex && pdflatex a377090_proof.tex
```

## References

- OEIS Foundation Inc., *Entry A377090*, https://oeis.org/A377090
- R. C. Vaughan, *On Goldbach's problem*, Acta Arith. **22** (1972), 21–48 (p. 22), https://matwbn.icm.edu.pl/ksiazki/aa/aa22/aa2213.pdf
- E. Westzynthius, *Über die Verteilung der Zahlen, die zu den $n$ ersten Primzahlen teilerfremd sind*, Comment. Phys.-Math. Soc. Sci. Fenn. **5** (1931), 1–37
- K. Ford, B. Green, S. Konyagin, and T. Tao, *Large gaps between consecutive prime numbers*, Ann. of Math. (2) **183** (2016), 935–974 (pp. 935–936), https://annals.math.princeton.edu/wp-content/uploads/annals-v183-n3-p04-p.pdf

## Acknowledgments and AI Disclosure

This repository was initiated, curated, and released by **Qingzhen Hu**. The proof constructions, English exposition, LaTeX typesetting, and computational verification scripts were generated with AI assistance throughout. All analytic and combinatorial arguments are self-contained and verifiable line by line, and the earliest numerical counterexample is certified independently in exact rational arithmetic via `verify_a377090.py`.
