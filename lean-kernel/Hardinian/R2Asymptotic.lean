import Hardinian.R2FiniteAssembly
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic

open Filter Topology

namespace Hardinian

theorem array_normalization_eq_kernel (k : ℕ) :
    ((k + 3 : ℕ) : ℝ) * (Nat.card (R2Array k) : ℝ) / (16 : ℝ) ^ (k + 3) =
      (((k + 3 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) / 256) * weightedKernelSum (k + 1) := by
  rw [weightedKernelSum_eq_array_card]
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  have hp : (16 : ℝ) ^ k ≠ 0 := by positivity
  simp only [Nat.cast_add, Nat.cast_ofNat, pow_add]
  norm_num
  field_simp [hk, hp] <;> ring

theorem array_index_ratio_tendsto :
    Tendsto (fun k : ℕ => ((k + 3 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ))
      atTop (𝓝 (1 : ℝ)) := by
  have hrec := tendsto_one_div_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
  have h : Tendsto (fun k : ℕ => (1 : ℝ) + 2 * (1 / ((k + 1 : ℕ) : ℝ)))
      atTop (𝓝 ((1 : ℝ) + 2 * 0)) :=
    tendsto_const_nhds.add (hrec.const_mul 2)
  convert h using 1
  · funext k
    have hk : (k : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp [hk] <;> ring
  · norm_num

/-- The original side is n=k+3; no values at n=1 or n=2 are assigned. -/
theorem array_r2_normalized_tendsto :
    Tendsto (fun k : ℕ => ((k + 3 : ℕ) : ℝ) * (Nat.card (R2Array k) : ℝ) /
      (16 : ℝ) ^ (k + 3)) atTop (𝓝 (1 / (324 * Real.pi))) := by
  have h := (array_index_ratio_tendsto.div_const 256).mul
    (weightedKernelSum_tendsto.comp (tendsto_add_atTop_nat 1))
  convert h using 1
  · funext k
    exact array_normalization_eq_kernel k
  · field_simp [Real.pi_ne_zero] <;> ring

theorem array_r2_comparison_pos (k : ℕ) :
    0 < (16 : ℝ) ^ (k + 3) / (324 * Real.pi * ((k + 3 : ℕ) : ℝ)) := by
  positivity

theorem array_r2_ratio_tendsto :
    Tendsto (fun k : ℕ => (Nat.card (R2Array k) : ℝ) /
      ((16 : ℝ) ^ (k + 3) / (324 * Real.pi * ((k + 3 : ℕ) : ℝ))))
      atTop (𝓝 (1 : ℝ)) := by
  have h := array_r2_normalized_tendsto.const_mul (324 * Real.pi)
  convert h using 1
  · funext k
    have hk : ((k + 3 : ℕ) : ℝ) ≠ 0 := by positivity
    have hp : (16 : ℝ) ^ (k + 3) ≠ 0 := by positivity
    field_simp [hk, hp, Real.pi_ne_zero] <;> ring
  · field_simp [Real.pi_ne_zero]

theorem array_r2_isEquivalent :
    Asymptotics.IsEquivalent atTop
      (fun k : ℕ => (Nat.card (R2Array k) : ℝ))
      (fun k : ℕ => (16 : ℝ) ^ (k + 3) / (324 * Real.pi * ((k + 3 : ℕ) : ℝ))) := by
  apply (Asymptotics.isEquivalent_iff_tendsto_one
    (Eventually.of_forall (fun k => ne_of_gt (array_r2_comparison_pos k)))).2
  exact array_r2_ratio_tendsto

end Hardinian
