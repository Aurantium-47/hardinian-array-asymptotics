# Lean supplement for the original r=2 array asymptotic

The written v0.2.0 extension covers every fixed integer parameter r. The Lean supplement covers **r=2**. Its final theorem concerns the cardinal of the actual array type, rather than a sequence defined from a determinant or a kernel formula.

The checked mathematical source is commit `94eb6714f159dba5d0c3cdb1ea2237da4e9c3a1b`, tree `3658968e3336b97379918282a7406f336304f5c8`. See [R2FiniteAssembly.lean](lean-kernel/Hardinian/R2FiniteAssembly.lean), [R2Asymptotic.lean](lean-kernel/Hardinian/R2Asymptotic.lean), the [actual full theorem types](verification/r2_actual_theorem_types.txt), and the [execution summary](verification/r2_execution_summary.json).

## Counted objects and exact range

For every natural k, `R2Array k` is the existing subtype of natural-valued arrays of side n=k+3. The first value is zero and the final value is k=n-3. Every available right, down and down-right step increases the value by zero or one. Each value remains within two of the king-distance reference `max(i,j)` in the zero-based coordinates. These are conditions on the actual array; no matrix-count identity is a field or hypothesis of its definition.

The parameters remain n=k+3, N=k+1=n-2 and m=k+2. All finite identities include k=0. The asymptotic statement covers the tail n>=3; no artificial n=1 or n=2 value is assigned using truncated natural subtraction. It does not formalize r=3 or the all-fixed-r theorem.

The actual final theorem is

```lean
Asymptotics.IsEquivalent atTop
  (fun k : ℕ => (Nat.card (R2Array k) : ℝ))
  (fun k : ℕ => (16 : ℝ) ^ (k + 3) /
    (324 * Real.pi * ((k + 3 : ℕ) : ℝ)))
```

Thus the comparison is with `16^n/(324*pi*n)` on n=k+3. The comparison function is proved positive. Separate actual theorems establish that the array/comparison ratio tends to one and that `(k+3)*card(R2Array k)/16^(k+3)` tends to `1/(324*pi)`.

## Proof chain

1. The original arrays are put in a genuine two-way correspondence with separated nested cuts and then with all k=n-3 ordered, vertex-disjoint lattice paths. Finiteness, the inverse laws and sink ordering are derived. Empty families and zero-length paths retain their actual vertices.
2. The signed-family expansion of the actual path matrix determinant is proved. A lexicographically least genuine intersection defines an unmarked bad-family involution. Its selection is stable under the actual two-path tail exchange, and its sign changes. The bad contribution cancels, while ordered disjoint families have identity endpoint permutation and weight one. This proves the relevant lattice-path LGV count internally.
3. Endpoint sets are matched to their omitted two-element complements, giving the original array cardinal as a double sum of actual complementary Pascal determinants. The convention is I for deleted source rows and J for deleted sink columns. The subsequent Jacobi formula has its separately proved J,I reversal; no factorial is inserted.
4. Explicit Pascal matrices, their inverse witnesses, Jacobi's complementary two-minor formula, rectangular two-row Cauchy–Binet and ordered two-set reindexing give the genuine strict W-square sum. The actual W is proved equal to an integer binomial interval sum for u<v; it is not defined by that target identity.
5. The integer interval is cast to Real before division. The resulting expression is the existing real binomial kernel Q. A bounded coordinate-reflection equivalence and exact powers of four give the existing weighted kernel sum as N/16^N times the strict W-square sum, including N=0. The coordinates are reflected separately, without an extra a+b<=N restriction.
6. The analytic chain proves the central-binomial limit, a common moving logarithmic window, a global summable majorant, the full weighted-sum limit and its exact constant. The final array assembly applies that proved limit at N=k+1. The exact conversion factor is `((k+3)/(k+1))/256`, and `(64/(81*pi))/256=1/(324*pi)`.

In particular, the final proof has no added assumption asserting a count, LGV, the kernel limit or the desired asymptotic. The underlying analytic and algebraic results remain explicit dependencies in the checked source.

## Recorded verification and trust

[Run 38716485093](https://github.com/Aurantium-47/hardinian-array-asymptotics/actions/runs/38716485093), job 116360310721, freshly compiled 40 project modules with Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. It checked 567 complete declaration types and transitive axiom reports, 167 complete definition/instance/constructor/projection print items, all fresh source/import identities, 129 resource-supervised command exits and final assertions. Only `propext`, `Classical.choice` and `Quot.sound` occurred. The run, job and three recorded steps succeeded. Complete type output was required; no unfinished proof or elided mathematical type was accepted.

The runner used the official Lean binary and pinned external precompiled dependency caches. Project sources were compiled freshly; the full external dependency source tree was not rebuilt, and this was not a replay through an independently implemented kernel. The cache helper `mathlib/Cache/Requests.lean` retained two explicit cleanup changes: the calls removing its `lib` and `ir` directories were replaced with `pure ()`. Its recorded SHA256 is `646fed31a48d85ed75746ec09d06c23f5abdaca455518b6760b0dcb2b10c47c0`. Mathematical library proof sources and the nine dependency revisions were unchanged; the helper modification means that the entire dependency working tree is not described as byte-identical.

A received audit-log fragment contained one UTF8 BOM followed by a service timestamp. Removing exactly that 32-byte formatting prefix reconstructed the original audit-command SHA256 `6b74704e0cfa7125c5411fd75c63994729f9e5da7f01b2666d0e13cbf846248c`. This changed no source, proof or build. The complete received log SHA256 is `4eab856e1b7ff01678de713e182acc87d0924f1c40f0614517b21aa917ce0a3d`. Download/cache printed-text newline boundaries remain distinguished from the original command-file hashes.

The supplement was prepared with AI assistance. It does not claim independent human peer review, an independent proof-checker implementation, an exhaustive priority search, or formalization of the r=3/all-fixed-r extension. The original papers' statements that they did not include proof-assistant certification describe their historical distributions. Their mathematical PDFs, TeX, code/data, references and rights remain unchanged. Current formal coverage and execution boundaries are those stated here.

## Reproduction

The [workflow](.github/workflows/hardinian-r2-final-assembly.yml) preserves the exact source commit, dependency revisions, cache roots, full fresh compilation and audit commands, and external resource guards. Consult [REPRODUCIBILITY.md](REPRODUCIBILITY.md) before attempting a new build. The documentation update itself did not rerun Lean, a mathematical suite, the old program or a PDF build, and did not create a new release archive.
