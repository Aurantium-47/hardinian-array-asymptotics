import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Data.Nat.Choose.Basic

open scoped BigOperators

noncomputable section
namespace HardinianHandoff

abbrev AltPoly (r : ℕ) := MvPolynomial (Fin r) ℚ

def IsAlternating {r : ℕ} (p : AltPoly r) : Prop :=
  ∀ i j : Fin r, i ≠ j → MvPolynomial.rename (Equiv.swap i j) p = -p

def vandermonde (r : ℕ) : AltPoly r :=
  ∏ i : Fin r, ∏ j ∈ Finset.Ioi i,
    (MvPolynomial.X i - MvPolynomial.X j)

def criticalOrder (r : ℕ) : ℕ :=
  (Nat.choose r 2 - r / 2) / 2

end HardinianHandoff
