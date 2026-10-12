# Two asymptotic formulas for square Hardinian arrays

A proof of the `r = 2` and `r = 3` formulas in the asymptotic conjecture table of Robert Dougherty-Bliss and Manuel Kauers, *Hardinian Arrays*, **Electronic Journal of Combinatorics 31(2) (2024), P2.9**, [DOI: 10.37236/12358](https://doi.org/10.37236/12358), page 12:

\[
H_2(n,n)\sim\frac{16^n}{324\pi n},\qquad
H_3(n,n)\sim\frac{64^n}{78732\pi n^3}.
\]

Here `H_r(n,n)` counts the square arrays defined in that paper. Both limits hold for fixed `r` as the integer side length `n` tends to infinity. The result does not cover general `r`.

[OEIS A253217](https://oeis.org/A253217) credits the `r = 2` asymptotic conjecture to Vaclav Kotesovec on March 2, 2023.

## Read the proof

- [Manuscript PDF](main.pdf)
- [Standalone LaTeX source](main.tex)
- [中文简述](README.zh-CN.md)
- [AI assistance and verification status](AI_USAGE.md)

Starting from Dougherty-Bliss and Kauers's published complementary-minor counting identity (the proof of Theorem 6, page 9), the argument derives exact sums of squares. A uniform binomial expansion and a geometric tail bound establish the limits; two moment determinants give the constants. No conjectured recurrence is used.

The scope of this version is a written proof with reproducible finite checks. It does not claim proof-assistant verification, external peer review, or completion of an exhaustive priority search.

## Reproduce the checks

From this directory, run with Python 3.8 or later:

```text
python hardinian.py --max-n 201
```

Only the standard library is required for the integer checks. Do not use Python's `-O` option, because the program uses assertions. If SymPy and mpmath are installed, the script also checks the two rational moment determinants symbolically and prints decimal ratios to the asymptotic leading terms. The included run used Python 3.8.3, SymPy 1.6.1 and mpmath 1.1.0.

The program writes [hardinian_results.json](hardinian_results.json), including:

- exact square-sum counts through `n = 201`;
- direct enumeration using the original array rules for `1 ≤ n ≤ 6`, for both parameters;
- independent evaluation of the complementary-minor formula for `3 ≤ n ≤ 8`;
- agreement with the 37 transcribed terms of [OEIS A253217](https://oeis.org/A253217), and the first 24 terms plus the `n = 100, 101` entries of [OEIS A252998](https://oeis.org/A252998).

The OEIS source URLs and the exact comparison values are included in the script. The result file comes from an actual successful run. Finite checks support the formulas' implementation; the manuscript proves the infinite limits.

## Build the PDF

With a standard LaTeX installation:

```text
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

The bibliography is included in the source. [SHA256SUMS.txt](SHA256SUMS.txt) records the hashes of the public content files.
