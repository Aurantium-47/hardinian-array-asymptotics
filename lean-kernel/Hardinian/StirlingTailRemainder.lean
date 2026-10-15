import Hardinian.StirlingIncrementRemainder
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Hardinian

open Filter
open scoped BigOperators Topology

/-- The logarithmic factorial correction, specified independently of any series. -/
noncomputable def logFactorialCorrection (N : ℕ) : ℝ :=
  Real.log (N.factorial : ℝ) -
    ((N : ℝ) + 1 / 2) * Real.log (N : ℝ) + (N : ℝ) -
    Real.log (2 * Real.pi) / 2

/-- A genuine discrete tail block; it is not a Bernoulli inverse-power coefficient. -/
noncomputable def stirlingTailBlock (N k : ℕ) : ℝ :=
  ∑' j : ℕ, stirlingStepTerm (N + j) k

theorem logFactorialCorrection_eq_stirling (N : ℕ) (hN : 1 ≤ N) :
    logFactorialCorrection N =
      Real.log (Stirling.stirlingSeq N) - Real.log (Real.sqrt Real.pi) := by
  have hn : (N : ℝ) ≠ 0 := by
    exact_mod_cast (show N ≠ 0 by omega)
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  unfold logFactorialCorrection
  rw [Stirling.log_stirlingSeq_formula,
    Real.log_div hn (Real.exp_ne_zero 1), Real.log_exp,
    Real.log_mul htwo hn, Real.log_mul htwo hpi,
    Real.log_sqrt Real.pi_pos.le]
  ring

theorem reciprocal_telescope_step (m : ℕ) (hm : 1 ≤ m) :
    1 / ((m : ℝ) * ((m : ℝ) + 1)) =
      1 / (m : ℝ) - 1 / ((m : ℝ) + 1) := by
  have hn : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hn' : (m : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hn, hn'] <;> ring

theorem reciprocal_telescope_hasSum (N : ℕ) (hN : 1 ≤ N) :
    HasSum (fun j : ℕ =>
      1 / (((N + j : ℕ) : ℝ) * (((N + j : ℕ) : ℝ) + 1)))
      (1 / (N : ℝ)) := by
  have hp (j : ℕ) :
      0 ≤ (1 / (((N + j : ℕ) : ℝ) * (((N + j : ℕ) : ℝ) + 1)) : ℝ) := by
    positivity
  apply (hasSum_iff_tendsto_nat_of_nonneg hp _).2
  have hsum (M : ℕ) :
      (∑ j ∈ Finset.range M,
        (1 / (((N + j : ℕ) : ℝ) * (((N + j : ℕ) : ℝ) + 1)) : ℝ)) =
        1 / (N : ℝ) - 1 / ((N + M : ℕ) : ℝ) := by
    calc
      _ = ∑ j ∈ Finset.range M,
          ((1 / ((N + j : ℕ) : ℝ)) - 1 / ((N + (j + 1) : ℕ) : ℝ)) := by
        apply Finset.sum_congr rfl
        intro j hj
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
          reciprocal_telescope_step (N + j) (by omega)
      _ = _ := by
        simpa only [Nat.add_zero] using
          Finset.sum_range_sub' (fun j : ℕ => (1 / ((N + j : ℕ) : ℝ) : ℝ)) M
  have hlim : Tendsto (fun M : ℕ => (1 / ((N + M : ℕ) : ℝ) : ℝ)) atTop (𝓝 0) := by
    simpa only [Nat.add_comm] using
      tendsto_one_div_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat N)
  simpa only [hsum, sub_zero] using
    (tendsto_const_nhds.sub hlim : Tendsto
      (fun M : ℕ => (1 / (N : ℝ)) - 1 / ((N + M : ℕ) : ℝ))
      atTop (𝓝 (1 / (N : ℝ) - 0)))

theorem stirlingLogStep_tail_hasSum (N : ℕ) (hN : 1 ≤ N) :
    HasSum (fun j : ℕ =>
      Real.log (Stirling.stirlingSeq (N + j)) -
        Real.log (Stirling.stirlingSeq (N + j + 1)))
      (logFactorialCorrection N) := by
  have hp (j : ℕ) : 0 ≤
      Real.log (Stirling.stirlingSeq (N + j)) -
        Real.log (Stirling.stirlingSeq (N + j + 1)) :=
    (stirlingStep_hasSum (N + j) (by omega)).nonneg
      (fun k => stirlingStepTerm_nonneg (N + j) k)
  apply (hasSum_iff_tendsto_nat_of_nonneg hp _).2
  have hsum : (fun M : ℕ => ∑ j ∈ Finset.range M,
      (Real.log (Stirling.stirlingSeq (N + j)) -
        Real.log (Stirling.stirlingSeq (N + j + 1)))) =
      fun M : ℕ => Real.log (Stirling.stirlingSeq N) -
        Real.log (Stirling.stirlingSeq (N + M)) := by
    funext M
    simpa only [Nat.add_zero, Nat.add_assoc] using
      Finset.sum_range_sub' (fun j : ℕ => Real.log (Stirling.stirlingSeq (N + j))) M
  have hlim : Tendsto (fun j : ℕ => Real.log (Stirling.stirlingSeq (N + j)))
      atTop (𝓝 (Real.log (Real.sqrt Real.pi))) := by
    simpa only [Nat.add_comm] using
      (Stirling.tendsto_stirlingSeq_sqrt_pi.log (by positivity)).comp
        (tendsto_add_atTop_nat N)
  rw [hsum, logFactorialCorrection_eq_stirling N hN]
  exact tendsto_const_nhds.sub hlim

theorem stirlingTailBlock_summable (N k : ℕ) (hN : 1 ≤ N) :
    Summable (fun j : ℕ => stirlingStepTerm (N + j) k) := by
  exact Summable.of_nonneg_of_le
    (fun j => stirlingStepTerm_nonneg (N + j) k)
    (fun j => le_hasSum (stirlingStep_hasSum (N + j) (by omega)) k
      (fun l hl => stirlingStepTerm_nonneg (N + j) l))
    (stirlingLogStep_tail_hasSum N hN).summable

theorem stirlingTailBlock_hasSum (N k : ℕ) (hN : 1 ≤ N) :
    HasSum (fun j : ℕ => stirlingStepTerm (N + j) k) (stirlingTailBlock N k) :=
  (stirlingTailBlock_summable N k hN).hasSum

theorem logFactorialCorrection_remainder_hasSum (N K : ℕ) (hN : 1 ≤ N) :
    HasSum (fun j : ℕ =>
      (Real.log (Stirling.stirlingSeq (N + j)) -
        Real.log (Stirling.stirlingSeq (N + j + 1))) -
        ∑ k ∈ Finset.range K, stirlingStepTerm (N + j) k)
      (logFactorialCorrection N - ∑ k ∈ Finset.range K, stirlingTailBlock N k) := by
  have hs : HasSum (fun j : ℕ => ∑ k ∈ Finset.range K, stirlingStepTerm (N + j) k)
      (∑ k ∈ Finset.range K, stirlingTailBlock N k) :=
    hasSum_sum (fun k hk => stirlingTailBlock_hasSum N k hN)
  exact (stirlingLogStep_tail_hasSum N hN).sub hs

theorem stirling_cumulative_term_bound (N K j : ℕ) (hN : 1 ≤ N) :
    (Real.log (Stirling.stirlingSeq (N + j)) -
        Real.log (Stirling.stirlingSeq (N + j + 1))) -
        ∑ k ∈ Finset.range K, stirlingStepTerm (N + j) k ≤
      (((1 / (2 * (N : ℝ) + 1)) ^ 2) ^ K / (4 * (2 * (K : ℝ) + 3))) *
        (1 / (((N + j : ℕ) : ℝ) * (((N + j : ℕ) : ℝ) + 1))) := by
  have hbase : (1 / (2 * (((N + j : ℕ) : ℝ)) + 1) : ℝ) ≤
      1 / (2 * (N : ℝ) + 1) := by
    apply one_div_le_one_div_of_le (by positivity)
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) j]
  have hpow := pow_le_pow_left₀ (by positivity) hbase 2
  have hpowK := pow_le_pow_left₀ (by positivity) hpow K
  calc
    _ ≤ ((1 / (2 * (((N + j : ℕ) : ℝ)) + 1)) ^ 2) ^ K /
        (4 * (2 * (K : ℝ) + 3) * ((N + j : ℕ) : ℝ) *
          (((N + j : ℕ) : ℝ) + 1)) :=
      (stirlingStep_truncation_bounds (N + j) K (by omega)).2
    _ ≤ ((1 / (2 * (N : ℝ) + 1)) ^ 2) ^ K /
        (4 * (2 * (K : ℝ) + 3) * ((N + j : ℕ) : ℝ) *
          (((N + j : ℕ) : ℝ) + 1)) :=
      div_le_div_of_nonneg_right hpowK (by positivity)
    _ = _ := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

theorem logFactorialCorrection_remainder (N K : ℕ) (hN : 1 ≤ N) :
    0 ≤ logFactorialCorrection N - ∑ k ∈ Finset.range K, stirlingTailBlock N k ∧
    logFactorialCorrection N - ∑ k ∈ Finset.range K, stirlingTailBlock N k ≤
      1 / (4 * (2 * (K : ℝ) + 3) * (N : ℝ) *
        (2 * (N : ℝ) + 1) ^ (2 * K)) := by
  have hs := logFactorialCorrection_remainder_hasSum N K hN
  refine ⟨hs.nonneg (fun j => (stirlingStep_truncation_bounds (N + j) K (by omega)).1), ?_⟩
  have ht := (reciprocal_telescope_hasSum N hN).mul_left
    (((1 / (2 * (N : ℝ) + 1)) ^ 2) ^ K / (4 * (2 * (K : ℝ) + 3)))
  have hb := hasSum_le (fun j => stirling_cumulative_term_bound N K j hN) hs ht
  have he : ((((1 / (2 * (N : ℝ) + 1)) ^ 2) ^ K /
      (4 * (2 * (K : ℝ) + 3))) * (1 / (N : ℝ))) =
      1 / (4 * (2 * (K : ℝ) + 3) * (N : ℝ) *
        (2 * (N : ℝ) + 1) ^ (2 * K)) := by
    simp only [one_div, inv_pow, ← pow_mul, div_eq_mul_inv, mul_inv_rev]
    ring
  exact he ▸ hb

theorem logFactorialCorrection_bounds (N : ℕ) (hN : 1 ≤ N) :
    0 ≤ logFactorialCorrection N ∧ logFactorialCorrection N ≤ 1 / (12 * (N : ℝ)) := by
  have h := logFactorialCorrection_remainder N 0 hN
  norm_num at h
  exact h

end Hardinian
