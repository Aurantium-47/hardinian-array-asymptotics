# Reproducibility and execution boundaries

The general proof is symbolic. It includes arbitrary fixed-order local expansions, exact alternating-polynomial cancellation, Gaussian normalization, the weighted discrete square sum and the whole geometric tail. No finite check or numerical extrapolation is a premise of the infinite theorem.

## Distinct existing records

The records below are historical. Preparing this extension involved no new mathematical execution.

| Record | Evidence and limits |
|---|---|
| Original general-parameter author data | Its JSON reports Linux/Python 3.13.5, SymPy 1.14.0, mpmath 1.3.0 and 3.741 seconds. The declared script hash matches the archived script. These are author-reported execution details, not independent authentication of that environment or run. |
| Later candidate replay in a separate directory | Archived stdout and comparison record show Python 3.8.3, SymPy 1.6.1, mpmath 1.1.0 on Windows, 6.072 seconds, and all listed checks passing. The comparison reports equality of 509 nonmetadata scalar leaves, excluding only command, environment and elapsed_seconds. This is existing replay evidence, distinct from the author JSON and the preparation of this version. |
| Separately written finite checker | Archived stdout/result report 3.004 seconds and all finite checks passing. It uses standard-library row transfer, rational elimination, matching-based Pfaffians and direct signed samples without importing the candidate implementation. These are finite-range checks, not an all-r asymptotic proof by extrapolation. |
| General proof review and extension preparation | The later general proof review read program/data statically, without running mathematics. Preparation of this extension likewise involved no mathematical execution, old suite, new entry-point test or Lean check. Hash agreement establishes version binding only. |

The historical candidate replay covers H_4(n,n) through n=101; direct arrays through n=7; 42 complementary-minor comparisons for 1<=r<=7 and valid n<=10; 501 individual row subsets at N=8; signs including ties; symbolic four-row calculations; and formal Gaussian coefficients for r=2,...,8. Diagnostic decimal ratios are not certificates. The archived author script SHA-256 is `665acf555f725ed12e23939697b4aad9590b9874f7bcac8f4821a08192198800`; original data SHA-256 is `7c3ff28b116a9a1954532513051b7ba04d80dee7174fee2d52a6fb32e04a8e66`.

The separate finite checker covers 86 determinant tests; matrix dimensions 0,...,8; 100 two-variable pairs; all 256 subsets of {0,...,7}; seven full-permutation Pfaffian normalizations; 9,194 sign/order cases; 52 array/minor/square-sum comparisons through n=8; and 99 path-family comparisons through n=5. Its recorded code SHA-256 is `8de411262e670a6e776cf6fd6c3210b56b303623bffb8fd0f219bcdea5454c1d`. Historical logs and general-parameter programs are not supplied as a new portable entry here; no new execution claim follows merely from their hashes.

## Original public r=2,3 program

The original `hardinian.py` and `hardinian_results.json` remain unchanged from v0.1.0. That program treats the old r=2,3 volume, not arbitrary r. Its original invocation is `python hardinian.py --max-n 201` with assertions enabled; optional symbolic and decimal checks use SymPy and mpmath. It writes `hardinian_results.json`, so future reproduction should use a separate working copy to preserve distributed data. Preparation of this extension did not execute that command or revalidate every original calculation. The unchanged original volume and public source retain their historical evidence scope.

## Rebuild only the extension PDF

With the standard LaTeX packages already installed, run `pdflatex proof.tex` twice from `extensions/paper/` to resolve references. The source is standalone, with no external figures, bibliography program or third-party PDF. No mathematical computation is part of the build. A rebuild can change PDF metadata/font encoding; the manifest identifies the supplied bytes. Original main.tex/main.pdf were not rebuilt.

The proof's trust basis is its explicit combinatorial source, standard analytic results and conventional mathematical reasoning. No proof-assistant certificate, independent human peer review or worldwide-priority certification is asserted.
