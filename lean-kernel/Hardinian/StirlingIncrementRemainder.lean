import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Hardinian

open scoped BigOperators

/-- The genuine positive terms of the logarithmic Stirling increment. -/
noncomputable def stirlingStepTerm (N k : ℕ) : ℝ :=
  (1 / (2 * (k : ℝ) + 3)) *
    ((1 / (2 * (N : ℝ) + 1)) ^ 2) ^ (k + 1)

theorem stirlingStepTerm_nonneg (N k : ℕ) : 0 ≤ stirlingStepTerm N k := by
  unfold stirlingStepTerm
  positivity

theorem stirling_ratio_bounds (N : ℕ) (hN : 1 ≤ N) :
    0 < ((1 / (2 * (N : ℝ) + 1)) ^ 2) ∧
    ((1 / (2 * (N : ℝ) + 1)) ^ 2) < 1 := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  constructor
  · positivity
  · rw [one_div, inv_pow]
    exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ (by linarith) two_ne_zero)

theorem stirling_ratio_geometric_identity (N : ℕ) (hN : 1 ≤ N) :
    ((1 / (2 * (N : ℝ) + 1)) ^ 2) /
        (1 - (1 / (2 * (N : ℝ) + 1)) ^ 2) =
      1 / (4 * (N : ℝ) * ((N : ℝ) + 1)) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hd : 2 * (N : ℝ) + 1 ≠ 0 := by positivity
  have hq : 1 - (1 / (2 * (N : ℝ) + 1)) ^ 2 ≠ 0 :=
    ne_of_gt (sub_pos.mpr (stirling_ratio_bounds N hN).2)
  apply (div_eq_div_iff hq (ne_of_gt (by positivity :
    0 < 4 * (N : ℝ) * ((N : ℝ) + 1)))).2
  field_simp [hd] <;> ring

theorem stirlingStep_hasSum (N : ℕ) (hN : 1 ≤ N) :
    HasSum (stirlingStepTerm N)
      (Real.log (Stirling.stirlingSeq N) -
        Real.log (Stirling.stirlingSeq (N + 1))) := by
  have hi : N - 1 + 1 = N := Nat.sub_add_cancel hN
  have hi' : N - 1 + 2 = N + 1 := by omega
  have hs := Stirling.log_stirlingSeq_diff_hasSum (N - 1)
  rw [hi, hi'] at hs
  convert hs using 1
  funext k
  have hk : (2 * (((k + 1 : ℕ) : ℝ)) + 1) = 2 * (k : ℝ) + 3 := by
    push_cast
    ring
  simp only [stirlingStepTerm, hk]

theorem stirlingStep_summable (N : ℕ) (hN : 1 ≤ N) :
    Summable (stirlingStepTerm N) :=
  (stirlingStep_hasSum N hN).summable

theorem stirlingStep_tail_hasSum (N K : ℕ) (hN : 1 ≤ N) :
    HasSum (fun j : ℕ => stirlingStepTerm N (j + K))
      ((Real.log (Stirling.stirlingSeq N) -
        Real.log (Stirling.stirlingSeq (N + 1))) -
        ∑ k ∈ Finset.range K, stirlingStepTerm N k) := by
  exact (hasSum_nat_add_iff' K).2 (stirlingStep_hasSum N hN)

theorem stirlingStep_tail_term_le (N K j : ℕ) :
    stirlingStepTerm N (j + K) ≤
      ((1 / (2 * (K : ℝ) + 3)) *
        ((1 / (2 * (N : ℝ) + 1)) ^ 2) ^ (K + 1)) *
        ((1 / (2 * (N : ℝ) + 1)) ^ 2) ^ j := by
  have hd : (1 / (2 * (((j + K : ℕ) : ℝ)) + 3) : ℝ) ≤
      1 / (2 * (K : ℝ) + 3) := by
    apply one_div_le_one_div_of_le (by positivity)
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) j]
  unfold stirlingStepTerm
  calc
    _ ≤ (1 / (2 * (K : ℝ) + 3)) *
        ((1 / (2 * (N : ℝ) + 1)) ^ 2) ^ (j + K + 1) :=
      mul_le_mul_of_nonneg_right hd (by positivity)
    _ = _ := by
      rw [show j + K + 1 = K + 1 + j by omega, pow_add]
      ring

/-- All truncation orders, including the empty truncation, for every positive index. -/
theorem stirlingStep_truncation_bounds (N K : ℕ) (hN : 1 ≤ N) :
    0 ≤ (Real.log (Stirling.stirlingSeq N) -
        Real.log (Stirling.stirlingSeq (N + 1))) -
        ∑ k ∈ Finset.range K, stirlingStepTerm N k ∧
    (Real.log (Stirling.stirlingSeq N) -
        Real.log (Stirling.stirlingSeq (N + 1))) -
        ∑ k ∈ Finset.range K, stirlingStepTerm N k ≤
      ((1 / (2 * (N : ℝ) + 1)) ^ 2) ^ K /
        (4 * (2 * (K : ℝ) + 3) * (N : ℝ) * ((N : ℝ) + 1)) := by
  let q : ℝ := (1 / (2 * (N : ℝ) + 1)) ^ 2
  have hq : 0 < q ∧ q < 1 := stirling_ratio_bounds N hN
  have ht := stirlingStep_tail_hasSum N K hN
  refine ⟨ht.nonneg (fun j => stirlingStepTerm_nonneg N (j + K)), ?_⟩
  have hg := (hasSum_geometric_of_lt_one hq.1.le hq.2).mul_left
    ((1 / (2 * (K : ℝ) + 3)) * q ^ (K + 1))
  have hb := hasSum_le (fun j => stirlingStep_tail_term_le N K j) ht hg
  have hid : q / (1 - q) = 1 / (4 * (N : ℝ) * ((N : ℝ) + 1)) :=
    stirling_ratio_geometric_identity N hN
  have he : ((1 / (2 * (K : ℝ) + 3)) * q ^ (K + 1)) * (1 - q)⁻¹ =
      q ^ K / (4 * (2 * (K : ℝ) + 3) * (N : ℝ) * ((N : ℝ) + 1)) := by
    calc
      _ = (q ^ K / (2 * (K : ℝ) + 3)) * (q / (1 - q)) := by
        rw [pow_succ]
        simp only [div_eq_mul_inv]
        ring
      _ = _ := by
        rw [hid]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
  exact he ▸ hb

end Hardinian
