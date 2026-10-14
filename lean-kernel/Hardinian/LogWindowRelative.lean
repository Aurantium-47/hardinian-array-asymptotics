import Hardinian.IntervalKernel
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic

open Filter
open scoped Topology

namespace Hardinian

theorem log_nat_pow_div_tendsto (k : ℕ) :
    Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ k / (N : ℝ)) atTop (𝓝 0) := by
  simpa only [Function.comp_apply, id_eq] using
    (Real.isLittleO_pow_log_id_atTop (n := k)).tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop

theorem logWindow_error_tendsto (C : ℝ) :
    Tendsto (fun N : ℕ => 2 * (C * Real.log (N : ℝ) + 1) ^ 2 / (N : ℝ))
      atTop (𝓝 0) := by
  have h0 : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) := by
    simpa only [pow_zero] using log_nat_pow_div_tendsto 0
  have h1 : Tendsto (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
    simpa only [pow_one] using log_nat_pow_div_tendsto 1
  have h2 := log_nat_pow_div_tendsto 2
  have h : Tendsto (fun N : ℕ =>
      (2 * C ^ 2) * (Real.log (N : ℝ) ^ 2 / (N : ℝ)) +
      (4 * C) * (Real.log (N : ℝ) / (N : ℝ)) + 2 * (1 / (N : ℝ)))
      atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      ((h2.const_mul (2 * C ^ 2)).add (h1.const_mul (4 * C))).add (h0.const_mul 2)
  apply h.congr'
  exact Eventually.of_forall fun N => by ring

theorem logWindow_eventually_below_half (C : ℝ) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N ≥ N0, 2 * (C * Real.log (N : ℝ)) < (N : ℝ) := by
  have h : Tendsto (fun N : ℕ => (2 * C) * (Real.log (N : ℝ) / (N : ℝ)))
      atTop (𝓝 0) := by
    simpa only [pow_one, mul_zero] using (log_nat_pow_div_tendsto 1).const_mul (2 * C)
  obtain ⟨M, hM⟩ := eventually_atTop.mp ((tendsto_order.mp h).2 1 (by norm_num))
  refine ⟨max 2 M, le_max_left _ _, ?_⟩
  intro N hN
  have hn : (0 : ℝ) < N := by
    exact_mod_cast (show 0 < N by have := le_max_left 2 M; omega)
  have ht := hM N (le_trans (le_max_right _ _) hN)
  have hd : 2 * (C * Real.log (N : ℝ)) / (N : ℝ) < 1 := by
    convert ht using 1 <;> ring
  have hh := (div_lt_iff₀ hn).mp hd
  simpa only [one_mul] using hh

theorem uniform_kernel_relative_logWindow (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N ≥ N0, ∀ a b : ℕ,
      b < a → a ≤ N → (a : ℝ) ≤ C * Real.log (N : ℝ) →
      |binomialKernel (N - a) (N - b) /
          (((a : ℝ) - b) * centralMass ((N - a) + (N - b))) - 1| < ε := by
  obtain ⟨M, hM2, hM⟩ := logWindow_eventually_below_half C
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    ((tendsto_order.mp (logWindow_error_tendsto C)).2 ε hε)
  refine ⟨max M K, le_trans hM2 (le_max_left _ _), ?_⟩
  intro N hN a b hba ha hlog
  have hNM : M ≤ N := le_trans (le_max_left _ _) hN
  have hNK : K ≤ N := le_trans (le_max_right _ _) hN
  have hN2 : 2 ≤ N := le_trans hM2 hNM
  have hhalf := hM N hNM
  have hba' : (b : ℝ) ≤ a := by exact_mod_cast (Nat.le_of_lt hba)
  have hsum' : (a : ℝ) + b ≤ N := by linarith
  have hsum : a + b ≤ N := by exact_mod_cast hsum'
  have hb := binomialKernel_offset_error N a b (by omega) hba ha hsum
  have hL : 0 ≤ C * Real.log (N : ℝ) :=
    mul_nonneg hC.le (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega)))
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ (a : ℝ) + 1)
    (add_le_add_right hlog 1) 2
  have he : 2 * ((a : ℝ) + 1) ^ 2 / (N : ℝ) ≤
      2 * (C * Real.log (N : ℝ) + 1) ^ 2 / (N : ℝ) :=
    div_le_div_of_nonneg_right (by nlinarith only [hsq]) (Nat.cast_nonneg _)
  exact lt_of_le_of_lt (hb.trans he) (hK N hNK)

end Hardinian
