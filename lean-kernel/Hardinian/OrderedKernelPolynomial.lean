import Hardinian.BinomialActualEvenCoefficients
import HardinianHandoff.PolynomialLift

namespace Hardinian

open Finset MvPolynomial

noncomputable def orderedKernelPolynomial (n : ℕ) : MvPolynomial (Fin 2) ℚ :=
  HardinianHandoff.gridLift n (fun h => binomialExpEvenCoeff n h)

theorem orderedBinomialKernelCoeff_eq_poly_eval (n a b : ℕ) :
    orderedBinomialKernelCoeff n a b =
      HardinianHandoff.evalSD (orderedKernelPolynomial n)
        ((a : ℚ) + (b : ℚ)) (((a - b : ℕ) : ℚ)) := by
  rw [orderedBinomialKernelCoeff_even_sum]
  exact (HardinianHandoff.gridLift_eval n (binomialExpEvenCoeff n)
    ((a : ℚ) + (b : ℚ)) (a - b)).symm

theorem orderedBinomialKernelCoeff_eq_poly_eval_ordered (n a b : ℕ) (hba : b ≤ a) :
    orderedBinomialKernelCoeff n a b =
      HardinianHandoff.evalSD (orderedKernelPolynomial n)
        ((a : ℚ) + (b : ℚ)) ((a : ℚ) - (b : ℚ)) := by
  rw [orderedBinomialKernelCoeff_eq_poly_eval, Nat.cast_sub hba]

theorem orderedKernelPolynomial_eval_cast (n : ℕ) (s d : ℚ) :
    (HardinianHandoff.evalSD (orderedKernelPolynomial n) s d : ℝ) =
      eval₂Hom (Rat.castHom ℝ)
        (fun i : Fin 2 => if i = 0 then (s : ℝ) else (d : ℝ))
        (orderedKernelPolynomial n) := by
  change (Rat.castHom ℝ) (eval₂Hom (RingHom.id ℚ)
    (fun i : Fin 2 => if i = 0 then s else d) (orderedKernelPolynomial n)) = _
  rw [MvPolynomial.map_eval₂Hom, RingHom.comp_id]
  have hv : (fun i : Fin 2 => (Rat.castHom ℝ) (if i = 0 then s else d)) =
      (fun i : Fin 2 => if i = 0 then (s : ℝ) else (d : ℝ)) := by
    funext i
    split_ifs <;> rfl
  rw [hv]

theorem orderedBinomialKernelCoeff_eq_poly_eval_real (n a b : ℕ) :
    (orderedBinomialKernelCoeff n a b : ℝ) =
      eval₂Hom (Rat.castHom ℝ)
        (fun i : Fin 2 => if i = 0 then (a : ℝ) + (b : ℝ)
          else ((a - b : ℕ) : ℝ)) (orderedKernelPolynomial n) := by
  rw [orderedBinomialKernelCoeff_eq_poly_eval, orderedKernelPolynomial_eval_cast]
  have hv :
      (fun i : Fin 2 => if i = 0 then (((a : ℚ) + (b : ℚ) : ℚ) : ℝ)
        else (((a - b : ℕ) : ℚ) : ℝ)) =
      (fun i : Fin 2 => if i = 0 then (a : ℝ) + (b : ℝ)
        else ((a - b : ℕ) : ℝ)) := by
    funext i
    split_ifs <;> norm_num
  rw [hv]

theorem orderedBinomialKernelCoeff_eq_poly_eval_real_ordered
    (n a b : ℕ) (hba : b ≤ a) :
    (orderedBinomialKernelCoeff n a b : ℝ) =
      eval₂Hom (Rat.castHom ℝ)
        (fun i : Fin 2 => if i = 0 then (a : ℝ) + (b : ℝ)
          else (a : ℝ) - (b : ℝ)) (orderedKernelPolynomial n) := by
  rw [orderedBinomialKernelCoeff_eq_poly_eval_real, Nat.cast_sub hba]

theorem orderedKernelPolynomial_zero : orderedKernelPolynomial 0 = X (1 : Fin 2) := by
  simp [orderedKernelPolynomial, HardinianHandoff.gridLift, Fin.sum_univ_one,
    binomialExpEvenCoeff_zero, HardinianHandoff.momentPolynomial_zero]

theorem orderedKernelPolynomial_odd (n : ℕ) :
    HardinianHandoff.reflectD (orderedKernelPolynomial n) = -orderedKernelPolynomial n := by
  exact HardinianHandoff.gridLift_odd n (binomialExpEvenCoeff n)

theorem orderedKernelPolynomial_totalDegree (n : ℕ) :
    (orderedKernelPolynomial n).totalDegree ≤ 2 * n + 1 := by
  exact HardinianHandoff.gridLift_totalDegree n (binomialExpEvenCoeff n)
    (binomialExpEvenCoeff_weighted_degree n)

theorem orderedKernelPolynomial_top (n : ℕ) :
    (orderedKernelPolynomial n -
      C (((-1 : ℚ) ^ n) /
        ((4 : ℚ) ^ n * (n.factorial : ℚ) * ((2 * n + 1 : ℕ) : ℚ))) *
      (X (1 : Fin 2)) ^ (2 * n + 1)).totalDegree ≤ 2 * n := by
  simpa only [orderedKernelPolynomial, HardinianHandoff.topCoefficient] using
    HardinianHandoff.gridLift_top n (binomialExpEvenCoeff n)
      (binomialExpEvenCoeff_strict_low n) (binomialExpEvenCoeff_last n)

theorem orderedKernelPolynomial_ab_swap (n : ℕ) (a b : ℚ) :
    HardinianHandoff.evalSD (orderedKernelPolynomial n) (b + a) (b - a) =
      -HardinianHandoff.evalSD (orderedKernelPolynomial n) (a + b) (a - b) := by
  exact HardinianHandoff.gridLift_ab_swap n (binomialExpEvenCoeff n) a b

theorem uniform_orderedBinomialKernel_polynomial_expansion
    (C : ℝ) (hC : 0 < C) (K : ℕ) :
    ∃ N0 : ℕ, 4 ≤ N0 ∧ ∀ N ≥ N0, ∀ L a b : ℕ,
      b < a → a ≤ L → (L : ℝ) ≤ C * Real.log (N : ℝ) →
      let err := |Real.sqrt (Real.pi * (N : ℝ)) * binomialKernel (N - a) (N - b) -
        (∑ n ∈ Icc 0 K, eval₂Hom (Rat.castHom ℝ)
          (fun i : Fin 2 => if i = 0 then (a : ℝ) + (b : ℝ)
            else (a : ℝ) - (b : ℝ)) (orderedKernelPolynomial n) / (N : ℝ) ^ n)|
      err ≤ ((a - b : ℕ) : ℝ) * binomialExpWindowConstant K *
        (1 + (L : ℝ)) ^ (2 * K + 2) / (N : ℝ) ^ (K + 1) ∧
      err ≤ binomialExpWindowConstant K *
        (1 + (L : ℝ)) ^ (2 * K + 3) / (N : ℝ) ^ (K + 1) := by
  classical
  obtain ⟨N0, hN04, hwindow⟩ := uniform_orderedBinomialKernel_expansion C hC K
  refine ⟨N0, hN04, ?_⟩
  intro N hN L a b hba haL hL
  have hs : (∑ n ∈ Icc 0 K, (orderedBinomialKernelCoeff n a b : ℝ) / (N : ℝ) ^ n) =
      ∑ n ∈ Icc 0 K, eval₂Hom (Rat.castHom ℝ)
        (fun i : Fin 2 => if i = 0 then (a : ℝ) + (b : ℝ)
          else (a : ℝ) - (b : ℝ)) (orderedKernelPolynomial n) / (N : ℝ) ^ n := by
    apply sum_congr rfl
    intro n hn
    rw [orderedBinomialKernelCoeff_eq_poly_eval_real_ordered n a b hba.le]
  have hbnd := hwindow N hN L a b hba haL hL
  dsimp only at hbnd ⊢
  simpa only [hs] using hbnd

end Hardinian
