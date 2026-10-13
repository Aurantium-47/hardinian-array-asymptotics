# Asymptotics of square Hardinian arrays

Aurantium · v0.2.0 · 14 October 2026

For every integer r>=1 fixed before n tends to infinity, this extension proves

\[
H_r(n,n)\sim c_r4^{rn}n^{-\binom r2},\qquad
c_r=\frac{2^{r(r-3)}}{3^{r^2}\pi^r}\prod_{j=1}^{r}\Gamma(j/2)^2.
\]

The full proof retains the arbitrary fixed-order binomial expansion on a logarithmic window, cancellation of all lower orders, the Mehta normalization, the discrete Vandermonde square sum, the whole omitted tail and the n-2 shift in the constant. It includes kappa_1=1 and the exact r=0,1 cases. It does not treat r growing with n or a joint rectangular limit.

- [General extension PDF](extensions/paper/proof.pdf) and [LaTeX](extensions/paper/proof.tex)
- [Original r=2,3 PDF](main.pdf) and [LaTeX](main.tex), retained byte-for-byte
- [Scope](SCOPE.md), [references](REFERENCES.md), [reproducibility](REPRODUCIBILITY.md), [rights](RIGHTS.md)
- [中文说明](README.zh-CN.md), [AI assistance](AI_USAGE.md)

The constants match the r<=5 table in Dougherty-Bliss–Kauers, *Hardinian Arrays*, EJC 31(2) (2024), P2.9. However, c_7=2^18·5^2/(3^45 pi^3) refutes the extra suggestion that all constants use only **integer** powers of 2, 3 and pi. The displayed table and asymptotic scale are established; that separate additional pattern fails.

The formal four-page ACM poster *Rectangular Hardinian Arrays* has been read for the comparison. Its eventual polynomial theorem fixes width k and does not justify setting k=n. The bounded source comparison does not certify first discovery or worldwide priority.

This version extends the [public v0.1.0 release](https://github.com/Aurantium-47/hardinian-array-asymptotics/releases/tag/v0.1.0). Its original mathematical manuscript, code and results remain unchanged; its r=2,3 limitations are the historical scope of that volume. The original volume preserves its OEIS A253217 attribution of the r=2 asymptotic conjecture to Vaclav Kotesovec.

No new mathematical computation was performed in preparing this extension. Author-reported data, an earlier separate candidate replay and independently implemented finite checks are distinguished in REPRODUCIBILITY.md. Finite checks do not substitute for the infinite argument. Prepared with AI assistance; no independent human peer review or proof-assistant certification is claimed. Third-party papers are linked, not bundled. WHITELIST.txt gives the payload, and MANIFEST.json/SHA256SUMS.txt identify its bytes.
