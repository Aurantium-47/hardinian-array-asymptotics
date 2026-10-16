import HardinianHandoff

open scoped BigOperators
open HardinianHandoff

set_option pp.all true
set_option pp.universes true
set_option pp.maxSteps 1000000

example (h d : ℕ) : moment h d = (momentPolynomial h).eval (d : ℚ) :=
  moment_eq_eval h d

example (h : ℕ) :
    (momentPolynomial h).comp (-Polynomial.X) = -momentPolynomial h :=
  momentPolynomial_odd h

example (h : ℕ) : (momentPolynomial h).natDegree = 2 * h + 1 :=
  momentPolynomial_natDegree h

example (h : ℕ) : (momentPolynomial h).coeff (2 * h + 1) =
    1 / ((4 : ℚ) ^ h * ((2 * h + 1 : ℕ) : ℚ)) :=
  momentPolynomial_top_coeff h

example : momentPolynomial 0 = Polynomial.X := momentPolynomial_zero

example (K : ℕ) (c : Fin (K + 1) → Polynomial ℚ) (s : ℚ) (d : ℕ) :
    evalSD (gridLift K c) s (d : ℚ) =
      ∑ j ∈ Finset.range d, ∑ h : Fin (K + 1),
        (c h).eval s * ((j : ℚ) - (d : ℚ) / 2) ^ (2 * h.val) :=
  gridLift_eval K c s d

example (K : ℕ) (c : Fin (K + 1) → Polynomial ℚ) :
    reflectD (gridLift K c) = -gridLift K c :=
  gridLift_odd K c

example (K : ℕ) (c : Fin (K + 1) → Polynomial ℚ)
    (hc : ∀ h, (c h).natDegree + 2 * h.val ≤ 2 * K) :
    (gridLift K c).totalDegree ≤ 2 * K + 1 :=
  gridLift_totalDegree K c hc

example (K : ℕ) (c : Fin (K + 1) → Polynomial ℚ)
    (hlow : ∀ h, h.val < K → (c h).natDegree + 2 * h.val < 2 * K)
    (hlast : c ⟨K, Nat.lt_succ_self K⟩ =
      Polynomial.C ((-1 : ℚ) ^ K / (Nat.factorial K : ℚ))) :
    (gridLift K c - MvPolynomial.C (topCoefficient K) *
      (MvPolynomial.X (1 : Fin 2)) ^ (2 * K + 1)).totalDegree ≤ 2 * K :=
  gridLift_top K c hlow hlast

example (K : ℕ) (c : Fin (K + 1) → Polynomial ℚ) (a b : ℚ) :
    evalSD (gridLift K c) (b + a) (b - a) =
      -evalSD (gridLift K c) (a + b) (a - b) :=
  gridLift_ab_swap K c a b

#check HardinianHandoff.moment_eq_eval
#check HardinianHandoff.momentPolynomial_odd
#check HardinianHandoff.momentPolynomial_natDegree
#check HardinianHandoff.momentPolynomial_top_coeff
#check HardinianHandoff.momentPolynomial_zero
#check HardinianHandoff.gridLift_eval
#check HardinianHandoff.gridLift_odd
#check HardinianHandoff.gridLift_totalDegree
#check HardinianHandoff.gridLift_top
#check HardinianHandoff.gridLift_ab_swap

#print axioms HardinianHandoff.moment_eq_eval
#print axioms HardinianHandoff.momentPolynomial_odd
#print axioms HardinianHandoff.momentPolynomial_natDegree
#print axioms HardinianHandoff.momentPolynomial_top_coeff
#print axioms HardinianHandoff.momentPolynomial_zero
#print axioms HardinianHandoff.gridLift_eval
#print axioms HardinianHandoff.gridLift_odd
#print axioms HardinianHandoff.gridLift_totalDegree
#print axioms HardinianHandoff.gridLift_top
#print axioms HardinianHandoff.gridLift_ab_swap

#print HardinianHandoff.moment
#print HardinianHandoff.momentPolynomial
#print HardinianHandoff.gridLift
#print HardinianHandoff.evalSD
#print HardinianHandoff.reflectD
#print HardinianHandoff.topCoefficient

#eval IO.println "HANDOFF_TEN_TARGETS_TYPECHECKED"
