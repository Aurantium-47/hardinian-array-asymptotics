import HardinianHandoff.DegreeCancellation

open HardinianHandoff

set_option pp.all true
set_option pp.universes true
set_option pp.maxSteps 1000000

example (r : ℕ) (p : AltPoly r) (hp : IsAlternating p)
    (i j : Fin r) (hij : i ≠ j) :
    (MvPolynomial.X i - MvPolynomial.X j) ∣ p :=
  pairFactor_dvd r p hp i j hij

example (r : ℕ) (p : AltPoly r) (hp : IsAlternating p) :
    vandermonde r ∣ p := vandermonde_dvd r p hp

example (r : ℕ) : vandermonde r ≠ 0 := vandermonde_ne_zero r

example (r : ℕ) : (vandermonde r).totalDegree = Nat.choose r 2 :=
  vandermonde_totalDegree r

example (r : ℕ) : IsAlternating (vandermonde r) :=
  vandermonde_isAlternating r

example (r : ℕ) (hr : r ≤ 1) : vandermonde r = 1 :=
  vandermonde_small r hr

example (r : ℕ) (p : AltPoly r) (hp : IsAlternating p)
    (hdeg : p.totalDegree < Nat.choose r 2) : p = 0 :=
  alternating_zero_of_degree_lt r p hp hdeg

example (r : ℕ) (p : AltPoly r) (hp : IsAlternating p)
    (hdeg : p.totalDegree ≤ Nat.choose r 2) :
    ∃! c : ℚ, p = MvPolynomial.C c * vandermonde r :=
  alternating_scalar_of_degree_le r p hp hdeg

example (r : ℕ) : r / 2 + 2 * criticalOrder r = Nat.choose r 2 :=
  criticalOrder_balance r

example (r : ℕ) (F : ℕ → AltPoly r)
    (hAlt : ∀ k, IsAlternating (F k))
    (hdeg : ∀ k, (F k).totalDegree ≤ r / 2 + 2 * k)
    (k : ℕ) (hk : k < criticalOrder r) : F k = 0 :=
  coefficient_below_critical r F hAlt hdeg k hk

example (r : ℕ) (F : ℕ → AltPoly r)
    (hAlt : ∀ k, IsAlternating (F k))
    (hdeg : ∀ k, (F k).totalDegree ≤ r / 2 + 2 * k) :
    ∃! c : ℚ, F (criticalOrder r) = MvPolynomial.C c * vandermonde r :=
  coefficient_at_critical r F hAlt hdeg

#check HardinianHandoff.pairFactor_dvd
#check HardinianHandoff.vandermonde_dvd
#check HardinianHandoff.vandermonde_ne_zero
#check HardinianHandoff.vandermonde_totalDegree
#check HardinianHandoff.vandermonde_isAlternating
#check HardinianHandoff.vandermonde_small
#check HardinianHandoff.alternating_zero_of_degree_lt
#check HardinianHandoff.alternating_scalar_of_degree_le
#check HardinianHandoff.criticalOrder_balance
#check HardinianHandoff.coefficient_below_critical
#check HardinianHandoff.coefficient_at_critical

#print axioms HardinianHandoff.pairFactor_dvd
#print axioms HardinianHandoff.vandermonde_dvd
#print axioms HardinianHandoff.vandermonde_ne_zero
#print axioms HardinianHandoff.vandermonde_totalDegree
#print axioms HardinianHandoff.vandermonde_isAlternating
#print axioms HardinianHandoff.vandermonde_small
#print axioms HardinianHandoff.alternating_zero_of_degree_lt
#print axioms HardinianHandoff.alternating_scalar_of_degree_le
#print axioms HardinianHandoff.criticalOrder_balance
#print axioms HardinianHandoff.coefficient_below_critical
#print axioms HardinianHandoff.coefficient_at_critical

#print HardinianHandoff.IsAlternating
#print HardinianHandoff.vandermonde
#print HardinianHandoff.criticalOrder

#eval IO.println "HANDOFF_ELEVEN_ALTERNATING_TARGETS_TYPECHECKED"
