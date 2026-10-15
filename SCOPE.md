# Written scope and current Lean coverage

The current [Lean supplement](FORMALIZATION.md) covers only r=2. For every k:Nat it uses the original `R2Array k` of side n=k+3, with N=k+1 and m=k+2. It proves the actual finite count as the strict W-square sum, the exact weighted-kernel normalization, and asymptotic equivalence to `16^(k+3)/(324*pi*(k+3))`. The finite identities include k0; original n1/2 are not invented by natural subtraction. The r2 counting identity, lattice-path cancellation and inverse correspondences are proved internally. No extra count/LGV/kernel-limit hypothesis is imposed.

The following describes the preserved v0.2.0 written theorem. Its all-fixed-r claim and its explicitly cited external inputs must not be confused with the narrower formal coverage. The old PDFs/TeX remain exact historical volumes.

## Written general-parameter result

The original nonnegative n x n arrays have a(1,1)=0, a(n,n)=n-r-1, |a(i,j)-(max(i,j)-1)|<=r, and every available right/down/down-right step increases the value by 0 or 1. The extension proves the Gamma-product asymptotic for **each fixed integer r>=1 as n tends to infinity**. H_0(n,n)=1; H_1(n,n)=(4^(n-1)-1)/3; n<=r has count zero.

The local expansion has arbitrary fixed order K and is uniform for offsets at most C log N with fixed K,C. The Pfaffian order is determined by the already fixed r. The proof controls the entire complementary tail and keeps N=n-2 until the constant is evaluated. These bounds are not uniform in r and do not give an r=r(n) or joint rectangular limit.

The constants match all r<=5 rows of Dougherty-Bliss–Kauers. The r=7 value contains 5², refuting the additional pattern when powers of 2, 3 and pi have integer exponents. This does not refute the table or asymptotic scale; arbitrary real exponents would not impose the same prime-factor restriction.

The complementary-minor enumeration is an external input from EJC Theorem 6's proof. Jacobi, finite Cauchy–Binet, positive-real Stirling with remainder, Faulhaber and the Gaussian Mehta integral are used with stated conditions. The square-sum and sign-expectation reductions from public v0.1.0 are proved again. The independent algebraic extraction of the r=4 constant is retained.

The published ACM poster treats fixed r and width k and eventual polynomial behavior in n. It does not supply uniformity allowing k=n. Publication priority is not certified. The original main.tex, main.pdf, hardinian.py and hardinian_results.json remain byte-for-byte unchanged. The root documentation describes both volumes. The v0.1.0 tag and Release retain their historical scope.
