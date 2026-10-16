import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval

open scoped BigOperators

noncomputable section
namespace HardinianHandoff

def moment (h d : ℕ) : ℚ :=
  ∑ j ∈ Finset.range d, ((j : ℚ) - (d : ℚ) / 2) ^ (2 * h)

def momentPolynomial (h : ℕ) : Polynomial ℚ :=
  Polynomial.C (((2 * h + 1 : ℕ) : ℚ)⁻¹) *
    ((Polynomial.bernoulli (2 * h + 1)).comp
        (Polynomial.C (1 / 2 : ℚ) * Polynomial.X) -
     (Polynomial.bernoulli (2 * h + 1)).comp
        (Polynomial.C (-(1 / 2 : ℚ)) * Polynomial.X))

abbrev BiPoly := MvPolynomial (Fin 2) ℚ

def gridLift (K : ℕ) (c : Fin (K + 1) → Polynomial ℚ) : BiPoly :=
  ∑ h : Fin (K + 1),
    (c h).eval₂ (MvPolynomial.C : ℚ →+* BiPoly) (MvPolynomial.X 0) *
      (momentPolynomial h.val).eval₂
        (MvPolynomial.C : ℚ →+* BiPoly) (MvPolynomial.X 1)

def evalSD (p : BiPoly) (s d : ℚ) : ℚ :=
  MvPolynomial.eval (fun i : Fin 2 => if i = 0 then s else d) p

def reflectD (p : BiPoly) : BiPoly :=
  MvPolynomial.eval₂Hom (MvPolynomial.C : ℚ →+* BiPoly)
    (fun i : Fin 2 => if i = 0 then MvPolynomial.X 0 else -(MvPolynomial.X 1 : BiPoly)) p

def topCoefficient (K : ℕ) : ℚ :=
  (-1 : ℚ) ^ K /
    ((4 : ℚ) ^ K * (Nat.factorial K : ℚ) * ((2 * K + 1 : ℕ) : ℚ))

end HardinianHandoff
