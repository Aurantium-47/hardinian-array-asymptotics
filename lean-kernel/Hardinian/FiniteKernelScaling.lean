import Hardinian.PascalKernelCast
import Hardinian.KernelWeightedLimit
import Mathlib.Data.Fin.Rev

open scoped BigOperators

namespace Hardinian.FiniteAlgebra

/-- Reflect both coordinates without swapping them. -/
def boundedOffsetEquiv (N : ℕ) :
    {p : Fin (N + 1) × Fin (N + 1) // p.1 < p.2} ≃
      {p : Fin (N + 1) × Fin (N + 1) // p.2 < p.1} where
  toFun p := ⟨(p.val.1.rev, p.val.2.rev), Fin.rev_strictAnti p.property⟩
  invFun p := ⟨(p.val.1.rev, p.val.2.rev), Fin.rev_strictAnti p.property⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact Fin.rev_rev p.val.1
    · exact Fin.rev_rev p.val.2
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact Fin.rev_rev p.val.1
    · exact Fin.rev_rev p.val.2

theorem boundedOffsetEquiv_val (N : ℕ)
    (p : {p : Fin (N + 1) × Fin (N + 1) // p.1 < p.2}) :
    ((boundedOffsetEquiv N p).val.1.val, (boundedOffsetEquiv N p).val.2.val) =
      (N - p.val.1.val, N - p.val.2.val) := by
  change (p.val.1.rev.val, p.val.2.rev.val) = _
  apply Prod.ext <;> simp only [Fin.val_rev] <;> omega

/-- The same two bounded reflections reindex every strict pair exactly once. -/
theorem sum_strict_fin_eq_offsets (N : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ u : Fin (N + 1),
      ∑ v ∈ (Finset.univ : Finset (Fin (N + 1))).filter (fun v => u < v),
        F u.val v.val) =
      ∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range a, F (N - a) (N - b) := by
  let T : ℕ → ℕ → ℝ := fun u v => if u < v then F u v else 0
  have hrefl :
      (∑ u ∈ Finset.range (N + 1), ∑ v ∈ Finset.range (N + 1), T u v) =
        ∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1), T (N - a) (N - b) := by
    calc
      (∑ u ∈ Finset.range (N + 1), ∑ v ∈ Finset.range (N + 1), T u v) =
          ∑ a ∈ Finset.range (N + 1), ∑ v ∈ Finset.range (N + 1), T (N - a) v := by
        simpa only [Nat.add_sub_cancel] using
          (Finset.sum_range_reflect
            (fun u => ∑ v ∈ Finset.range (N + 1), T u v) (N + 1)).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro a ha
        simpa only [Nat.add_sub_cancel] using
          (Finset.sum_range_reflect (fun v => T (N - a) v) (N + 1)).symm
  have hrestrict :
      (∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1), T (N - a) (N - b)) =
        ∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range a, F (N - a) (N - b) := by
    apply Finset.sum_congr rfl
    intro a ha
    have haN : a ≤ N := by
      have := Finset.mem_range.mp ha
      omega
    calc
      (∑ b ∈ Finset.range (N + 1), T (N - a) (N - b)) =
          ∑ b ∈ Finset.range (N + 1), if b < a then F (N - a) (N - b) else 0 := by
        apply Finset.sum_congr rfl
        intro b hb
        have hbN : b ≤ N := by
          have := Finset.mem_range.mp hb
          omega
        have hcond : N - a < N - b ↔ b < a := by omega
        simp only [T, hcond]
      _ = ∑ b ∈ (Finset.range (N + 1)).filter (fun b => b < a), F (N - a) (N - b) := by
        simp only [Finset.sum_filter]
      _ = _ := by
        have hset : (Finset.range (N + 1)).filter (fun b => b < a) = Finset.range a := by
          ext b
          simp only [Finset.mem_filter, Finset.mem_range]
          omega
        rw [hset]
  simp only [Finset.sum_filter]
  change (∑ u : Fin (N + 1), ∑ v : Fin (N + 1),
    if u.val < v.val then F u.val v.val else 0) = _
  simpa only [Finset.sum_range, T] using hrefl.trans hrestrict

theorem offset_power_ratio (N a b : ℕ) (ha : a ≤ N) (hb : b ≤ N) :
    (4 : ℝ) ^ ((N - a) + (N - b)) / (16 : ℝ) ^ N = (1 / 4 : ℝ) ^ (a + b) := by
  have hexp : ((N - a) + (N - b)) + (a + b) = 2 * N := by omega
  have hprod :
      (4 : ℝ) ^ ((N - a) + (N - b)) * (4 : ℝ) ^ (a + b) = (16 : ℝ) ^ N := by
    rw [← pow_add, hexp, pow_mul]
    norm_num
  have h4 : (4 : ℝ) ^ (a + b) ≠ 0 := by positivity
  have h16 : (16 : ℝ) ^ N ≠ 0 := by positivity
  rw [one_div_pow]
  apply (div_eq_div_iff h16 h4).2
  simpa only [one_mul] using hprod

theorem weightedKernelSum_eq_pascal_square_sum (N : ℕ) :
    Hardinian.weightedKernelSum N =
      ((N : ℝ) / (16 : ℝ) ^ N) *
        (∑ u : Fin (N + 1),
          ∑ v ∈ (Finset.univ : Finset (Fin (N + 1))).filter (fun v => u < v),
            ((pascalTwoRowSum (N + 1) u v : ℤ) : ℝ) ^ 2) := by
  have hrows :
      (∑ u : Fin (N + 1),
        ∑ v ∈ (Finset.univ : Finset (Fin (N + 1))).filter (fun v => u < v),
          ((pascalTwoRowSum (N + 1) u v : ℤ) : ℝ) ^ 2) =
        ∑ u : Fin (N + 1),
          ∑ v ∈ (Finset.univ : Finset (Fin (N + 1))).filter (fun v => u < v),
            (4 : ℝ) ^ (u.val + v.val) * Hardinian.binomialKernel u.val v.val ^ 2 := by
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    exact pascalTwoRowSum_cast_square (N + 1) u v (Finset.mem_filter.mp hv).2
  symm
  rw [hrows, sum_strict_fin_eq_offsets N
    (fun u v => (4 : ℝ) ^ (u + v) * Hardinian.binomialKernel u v ^ 2)]
  unfold Hardinian.weightedKernelSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  have haN : a ≤ N := by
    have := Finset.mem_range.mp ha
    omega
  have hbN : b ≤ N := by
    have := Finset.mem_range.mp hb
    omega
  have hp := offset_power_ratio N a b haN hbN
  calc
    (N : ℝ) / (16 : ℝ) ^ N *
        ((4 : ℝ) ^ ((N - a) + (N - b)) * Hardinian.binomialKernel (N - a) (N - b) ^ 2) =
        ((4 : ℝ) ^ ((N - a) + (N - b)) / (16 : ℝ) ^ N) *
          (N : ℝ) * Hardinian.binomialKernel (N - a) (N - b) ^ 2 := by
      simp only [div_eq_mul_inv]
      ring
    _ = _ := by rw [hp]

theorem weightedKernelSum_zero_exact : Hardinian.weightedKernelSum 0 = 0 := by
  simp [Hardinian.weightedKernelSum]

end Hardinian.FiniteAlgebra
