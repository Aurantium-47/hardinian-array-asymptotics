import Hardinian.StirlingTailRemainder
import Hardinian.StirlingCoefficientMatching
import Mathlib.Topology.Algebra.InfiniteSum.Ring

namespace Hardinian

open Filter
open scoped BigOperators Topology

theorem reciprocalPower_tail_tendsto_zero (N p : ℕ) :
    Tendsto (fun j : ℕ => (1 / (((N + j : ℕ) : ℝ) ^ (p + 1)) : ℝ))
      atTop (𝓝 0) := by
  have h : Tendsto (fun j : ℕ => (1 / ((N + j : ℕ) : ℝ) : ℝ)) atTop (𝓝 0) := by
    simpa only [Nat.add_comm] using
      tendsto_one_div_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat N)
  simpa only [one_div, inv_pow, zero_pow (by omega : p + 1 ≠ 0)] using h.pow (p + 1)

theorem reciprocalPower_difference_nonneg (N p j : ℕ) (hN : 1 ≤ N) :
    0 ≤ (1 / (((N + j : ℕ) : ℝ) ^ (p + 1)) -
      1 / (((N + j + 1 : ℕ) : ℝ) ^ (p + 1)) : ℝ) := by
  have hm : (0 : ℝ) < ((N + j : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < N + j by omega)
  have hstep : (((N + j : ℕ) : ℝ)) ≤ ((N + j + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.le_succ (N + j))
  exact sub_nonneg.mpr (one_div_le_one_div_of_le (pow_pos hm _)
    (pow_le_pow_left₀ hm.le hstep (p + 1)))

theorem reciprocalPower_difference_hasSum (N p : ℕ) (hN : 1 ≤ N) :
    HasSum (fun j : ℕ => (1 / (((N + j : ℕ) : ℝ) ^ (p + 1)) -
      1 / (((N + j + 1 : ℕ) : ℝ) ^ (p + 1)) : ℝ))
      (1 / ((N : ℝ) ^ (p + 1))) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg
    (fun j => reciprocalPower_difference_nonneg N p j hN) _).2
  have hsum : (fun M : ℕ => ∑ j ∈ Finset.range M,
      (1 / (((N + j : ℕ) : ℝ) ^ (p + 1)) -
        1 / (((N + j + 1 : ℕ) : ℝ) ^ (p + 1)) : ℝ)) =
      fun M : ℕ => 1 / ((N : ℝ) ^ (p + 1)) -
        1 / (((N + M : ℕ) : ℝ) ^ (p + 1)) := by
    funext M
    simpa only [Nat.add_zero, Nat.add_assoc] using
      Finset.sum_range_sub' (fun j : ℕ => (1 / (((N + j : ℕ) : ℝ) ^ (p + 1)) : ℝ)) M
  rw [hsum]
  simpa only [sub_zero] using
    (tendsto_const_nhds.sub (reciprocalPower_tail_tendsto_zero N p) : Tendsto
      (fun M : ℕ => 1 / ((N : ℝ) ^ (p + 1)) -
        1 / (((N + M : ℕ) : ℝ) ^ (p + 1)))
      atTop (𝓝 (1 / ((N : ℝ) ^ (p + 1)) - 0)))

theorem stirlingCorrectionPrefix_delta_hasSum (N J : ℕ) (hN : 1 ≤ N) :
    HasSum (fun j : ℕ => stirlingCorrectionPrefix (N + j) J -
      stirlingCorrectionPrefix (N + j + 1) J) (stirlingCorrectionPrefix N J) := by
  have hs : HasSum (fun j : ℕ => ∑ i ∈ Finset.range J,
      (stirlingCorrectionCoeff i : ℝ) *
        (1 / (((N + j : ℕ) : ℝ) ^ (i + 1)) -
          1 / (((N + j + 1 : ℕ) : ℝ) ^ (i + 1))))
      (∑ i ∈ Finset.range J, (stirlingCorrectionCoeff i : ℝ) *
        (1 / ((N : ℝ) ^ (i + 1)))) :=
    hasSum_sum (fun i hi => (reciprocalPower_difference_hasSum N i hN).mul_left
      (stirlingCorrectionCoeff i : ℝ))
  have he : (∑ i ∈ Finset.range J, (stirlingCorrectionCoeff i : ℝ) *
      (1 / ((N : ℝ) ^ (i + 1)))) = stirlingCorrectionPrefix N J := by
    simp only [stirlingCorrectionPrefix, div_eq_mul_inv, one_mul]
  rw [he] at hs
  refine hs.congr_fun (fun j => ?_)
  rw [stirlingCorrectionDifference_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Nat.cast_add, Nat.cast_one, add_assoc]

theorem stirlingCorrection_residual_hasSum (N J : ℕ) (hN : 1 ≤ N) :
    HasSum (fun j : ℕ =>
      (Real.log (Stirling.stirlingSeq (N + j)) -
        Real.log (Stirling.stirlingSeq (N + j + 1))) -
        (stirlingCorrectionPrefix (N + j) J - stirlingCorrectionPrefix (N + j + 1) J))
      (logFactorialCorrection N - stirlingCorrectionPrefix N J) :=
  (stirlingLogStep_tail_hasSum N hN).sub (stirlingCorrectionPrefix_delta_hasSum N J hN)

theorem reciprocalPower_tail_majorant (N J j : ℕ) (hN : 1 ≤ N) :
    (1 / (((N + j : ℕ) : ℝ) ^ (J + 2)) : ℝ) ≤
      (2 / ((N : ℝ) ^ J)) *
        (1 / (((N + j : ℕ) : ℝ) * (((N + j : ℕ) : ℝ) + 1))) := by
  have hn1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hnm : (N : ℝ) ≤ ((N + j : ℕ) : ℝ) := by
    exact_mod_cast (show N ≤ N + j by omega)
  have hm1 : (1 : ℝ) ≤ ((N + j : ℕ) : ℝ) := hn1.trans hnm
  have hn : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le zero_lt_one hn1
  have hm : (0 : ℝ) < ((N + j : ℕ) : ℝ) := lt_of_lt_of_le zero_lt_one hm1
  have hpow : (1 / (((N + j : ℕ) : ℝ) ^ J) : ℝ) ≤ 1 / ((N : ℝ) ^ J) :=
    one_div_le_one_div_of_le (pow_pos hn _) (pow_le_pow_left₀ hn.le hnm J)
  have htwo : (1 / (((N + j : ℕ) : ℝ) ^ 2) : ℝ) ≤
      2 / (((N + j : ℕ) : ℝ) * (((N + j : ℕ) : ℝ) + 1)) := by
    apply (div_le_div_iff₀ (pow_pos hm _) (mul_pos hm (by positivity))).2
    nlinarith
  calc
    _ = (1 / (((N + j : ℕ) : ℝ) ^ J)) *
        (1 / (((N + j : ℕ) : ℝ) ^ 2)) := by
      simp only [pow_add, one_div, mul_inv_rev]
      ring
    _ ≤ (1 / ((N : ℝ) ^ J)) *
        (2 / (((N + j : ℕ) : ℝ) * (((N + j : ℕ) : ℝ) + 1))) :=
      mul_le_mul hpow htwo (by positivity) (by positivity)
    _ = _ := by simp only [div_eq_mul_inv]; ring

theorem stirlingCorrection_residual_term_majorant (N J j : ℕ) (hN : 1 ≤ N) :
    |(Real.log (Stirling.stirlingSeq (N + j)) -
        Real.log (Stirling.stirlingSeq (N + j + 1))) -
        (stirlingCorrectionPrefix (N + j) J - stirlingCorrectionPrefix (N + j + 1) J)| ≤
      (2 * (stirlingResidualConstant J : ℝ) / ((N : ℝ) ^ J)) *
        (1 / (((N + j : ℕ) : ℝ) * (((N + j : ℕ) : ℝ) + 1))) := by
  have hC : (0 : ℝ) ≤ (stirlingResidualConstant J : ℝ) := by
    exact_mod_cast stirlingResidualConstant_nonneg J
  calc
    _ ≤ (stirlingResidualConstant J : ℝ) / (((N + j : ℕ) : ℝ) ^ (J + 2)) :=
      stirlingCorrection_increment_error (N + j) J (by omega)
    _ = (stirlingResidualConstant J : ℝ) *
        (1 / (((N + j : ℕ) : ℝ) ^ (J + 2))) := by ring
    _ ≤ (stirlingResidualConstant J : ℝ) *
        ((2 / ((N : ℝ) ^ J)) *
          (1 / (((N + j : ℕ) : ℝ) * (((N + j : ℕ) : ℝ) + 1)))) :=
      mul_le_mul_of_nonneg_left (reciprocalPower_tail_majorant N J j hN) hC
    _ = _ := by ring

theorem stirlingCorrection_majorant_hasSum (N J : ℕ) (hN : 1 ≤ N) :
    HasSum (fun j : ℕ =>
      (2 * (stirlingResidualConstant J : ℝ) / ((N : ℝ) ^ J)) *
        (1 / (((N + j : ℕ) : ℝ) * (((N + j : ℕ) : ℝ) + 1))))
      (2 * (stirlingResidualConstant J : ℝ) / ((N : ℝ) ^ (J + 1))) := by
  have hs := (reciprocal_telescope_hasSum N hN).mul_left
    (2 * (stirlingResidualConstant J : ℝ) / ((N : ℝ) ^ J))
  have he : (2 * (stirlingResidualConstant J : ℝ) / ((N : ℝ) ^ J)) *
      (1 / (N : ℝ)) = 2 * (stirlingResidualConstant J : ℝ) / ((N : ℝ) ^ (J + 1)) := by
    simp only [pow_succ, one_div, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he] at hs
  exact hs

theorem stirlingCorrection_residual_abs_summable (N J : ℕ) (hN : 1 ≤ N) :
    Summable (fun j : ℕ =>
      |(Real.log (Stirling.stirlingSeq (N + j)) -
          Real.log (Stirling.stirlingSeq (N + j + 1))) -
          (stirlingCorrectionPrefix (N + j) J - stirlingCorrectionPrefix (N + j + 1) J)|) :=
  Summable.of_nonneg_of_le (fun j => abs_nonneg _)
    (fun j => stirlingCorrection_residual_term_majorant N J j hN)
    (stirlingCorrection_majorant_hasSum N J hN).summable

theorem logFactorialCorrection_inversePower_error (N J : ℕ) (hN : 1 ≤ N) :
    |logFactorialCorrection N - stirlingCorrectionPrefix N J| ≤
      2 * (stirlingResidualConstant J : ℝ) / ((N : ℝ) ^ (J + 1)) := by
  have hs := stirlingCorrection_residual_hasSum N J hN
  have ht := stirlingCorrection_majorant_hasSum N J hN
  exact abs_le.mpr ⟨
    hasSum_le (fun j => (abs_le.mp (stirlingCorrection_residual_term_majorant N J j hN)).1)
      ht.neg hs,
    hasSum_le (fun j => (abs_le.mp (stirlingCorrection_residual_term_majorant N J j hN)).2)
      hs ht⟩

end Hardinian
