import Hardinian.KernelGlobalDomination
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Data.Nat.Choose.Cast

open Filter
open scoped Topology

namespace Hardinian

noncomputable def weightedKernelSum (N : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range a,
    (1 / 4 : ℝ) ^ (a + b) * (N : ℝ) * binomialKernel (N - a) (N - b) ^ 2

noncomputable def weightedKernelLimitTerm (p : ℕ × ℕ) : ℝ :=
  if p.2 < p.1 then
    (1 / 4 : ℝ) ^ (p.1 + p.2) * ((p.1 : ℝ) - p.2) ^ 2 / Real.pi
  else 0

theorem weightedKernelSum_eq_tsum (N : ℕ) :
    weightedKernelSum N = ∑' p : ℕ × ℕ, weightedKernelTerm N p := by
  rw [(weightedKernelTerm_summable N).tsum_prod]
  unfold weightedKernelSum
  symm
  have hout : ∀ a ∉ Finset.range (N + 1), (∑' b : ℕ, weightedKernelTerm N (a, b)) = 0 := by
    intro a ha
    have hNa : ¬ a ≤ N := by simp only [Finset.mem_range] at ha; omega
    simp [weightedKernelTerm, hNa]
  rw [tsum_eq_sum hout]
  apply Finset.sum_congr rfl
  intro a ha
  have haN : a ≤ N := by simp only [Finset.mem_range] at ha; omega
  have hbout : ∀ b ∉ Finset.range a, weightedKernelTerm N (a, b) = 0 := by
    intro b hb
    have hba : ¬ b < a := by simpa only [Finset.mem_range] using hb
    simp [weightedKernelTerm, hba]
  rw [tsum_eq_sum hbout]
  apply Finset.sum_congr rfl
  intro b hb
  simp only [weightedKernelTerm, Finset.mem_range.mp hb, haN, and_self, if_true]

theorem fixed_offset_normalized_kernel_tendsto (a b : ℕ) (hba : b < a) :
    Tendsto (fun N : ℕ => Real.sqrt (Real.pi * (N : ℝ)) *
      binomialKernel (N - a) (N - b) / ((a : ℝ) - b)) atTop (𝓝 1) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨M, hM2, hM⟩ := uniform_binomialKernel_logWindow 1 ε (by norm_num) hε
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hlog.eventually_ge_atTop (a : ℝ))
  refine ⟨max M (max a K), ?_⟩
  intro N hN
  have hMN : M ≤ N := le_trans (le_max_left _ _) hN
  have haKN : max a K ≤ N := le_trans (le_max_right _ _) hN
  have haN : a ≤ N := le_trans (le_max_left _ _) haKN
  have hKN : K ≤ N := le_trans (le_max_right _ _) haKN
  simpa only [Real.dist_eq] using hM N hMN a b hba haN (by simpa only [one_mul] using hK N hKN)

theorem fixed_offset_kernel_square_tendsto (a b : ℕ) (hba : b < a) :
    Tendsto (fun N : ℕ => (N : ℝ) * binomialKernel (N - a) (N - b) ^ 2)
      atTop (𝓝 (((a : ℝ) - b) ^ 2 / Real.pi)) := by
  have hba' : (b : ℝ) < a := by exact_mod_cast hba
  have hd : (a : ℝ) - b ≠ 0 := by linarith
  have h : Tendsto (fun N : ℕ => (((a : ℝ) - b) ^ 2 / Real.pi) *
      (Real.sqrt (Real.pi * (N : ℝ)) * binomialKernel (N - a) (N - b) /
        ((a : ℝ) - b)) ^ 2) atTop (𝓝 (((a : ℝ) - b) ^ 2 / Real.pi)) := by
    simpa only [one_pow, mul_one] using
      ((fixed_offset_normalized_kernel_tendsto a b hba).pow 2).const_mul
        (((a : ℝ) - b) ^ 2 / Real.pi)
  apply h.congr'
  exact Eventually.of_forall fun N => by
    dsimp only
    rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]
    field_simp [hd, Real.pi_ne_zero] <;> ring

theorem weightedKernelTerm_tendsto (p : ℕ × ℕ) :
    Tendsto (fun N : ℕ => weightedKernelTerm N p) atTop (𝓝 (weightedKernelLimitTerm p)) := by
  rcases p with ⟨a, b⟩
  by_cases hba : b < a
  · have h : Tendsto (fun N : ℕ => (1 / 4 : ℝ) ^ (a + b) *
        ((N : ℝ) * binomialKernel (N - a) (N - b) ^ 2))
        atTop (𝓝 (weightedKernelLimitTerm (a, b))) := by
      simpa only [weightedKernelLimitTerm, hba, if_true, mul_div_assoc] using
        (fixed_offset_kernel_square_tendsto a b hba).const_mul ((1 / 4 : ℝ) ^ (a + b))
    apply h.congr'
    filter_upwards [eventually_ge_atTop a] with N hN
    simp only [weightedKernelTerm, hba, hN, and_self, if_true]
    ring
  · simpa only [weightedKernelTerm, weightedKernelLimitTerm, hba, false_and, if_false] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

def strictPairEquiv : (ℕ × ℕ) ≃ {p : ℕ × ℕ // p.2 < p.1} where
  toFun p := ⟨(p.1 + p.2 + 1, p.1), by omega⟩
  invFun p := (p.1.2, p.1.1 - p.1.2 - 1)
  left_inv p := by
    rcases p with ⟨b, d⟩
    apply Prod.ext
    · rfl
    · dsimp; omega
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · dsimp; have h := p.property; omega
    · rfl

theorem shifted_square_geometric_hasSum :
    HasSum (fun d : ℕ => ((d : ℝ) + 1) ^ 2 * (1 / 4 : ℝ) ^ d) (80 / 27 : ℝ) := by
  have h2 := hasSum_choose_mul_geometric_of_norm_lt_one 2
    (show ‖(1 / 4 : ℝ)‖ < 1 by norm_num)
  have h1 := hasSum_choose_mul_geometric_of_norm_lt_one 1
    (show ‖(1 / 4 : ℝ)‖ < 1 by norm_num)
  have h := (h2.mul_left (2 : ℝ)).sub h1
  convert h using 1
  · funext d
    simp only [Nat.cast_choose_two, Nat.choose_one_right, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
    ring
  · norm_num

theorem weightedKernelLimitTerm_tsum :
    (∑' p : ℕ × ℕ, weightedKernelLimitTerm p) = 64 / (81 * Real.pi) := by
  let f : ℕ × ℕ → ℝ := fun p =>
    (1 / 4 : ℝ) ^ (p.1 + p.2) * ((p.1 : ℝ) - p.2) ^ 2 / Real.pi
  have hsub : (∑' p : ℕ × ℕ, weightedKernelLimitTerm p) =
      ∑' p : {p : ℕ × ℕ // p.2 < p.1}, f p := by
    symm
    simpa only [weightedKernelLimitTerm, f, Set.indicator, Set.mem_setOf_eq] using
      (tsum_subtype {p : ℕ × ℕ | p.2 < p.1} f)
  have hg : HasSum (fun b : ℕ => (1 / 16 : ℝ) ^ b) (16 / 15 : ℝ) := by
    convert hasSum_geometric_of_lt_one (show (0 : ℝ) ≤ 1 / 16 by norm_num)
      (show (1 / 16 : ℝ) < 1 by norm_num) using 1 <;> norm_num
  have hs := shifted_square_geometric_hasSum
  have hp := hg.mul hs
    (hg.summable.mul_of_nonneg hs.summable (fun b => by positivity) (fun d => by positivity))
  calc
    (∑' p : ℕ × ℕ, weightedKernelLimitTerm p) =
        ∑' p : {p : ℕ × ℕ // p.2 < p.1}, f p := hsub
    _ = ∑' p : ℕ × ℕ, f (strictPairEquiv p) := (strictPairEquiv.tsum_eq (fun p => f p)).symm
    _ = ∑' p : ℕ × ℕ, (1 / (4 * Real.pi)) *
        ((1 / 16 : ℝ) ^ p.1 * (((p.2 : ℝ) + 1) ^ 2 * (1 / 4 : ℝ) ^ p.2)) := by
      apply tsum_congr
      rintro ⟨b, d⟩
      have hpow : (1 / 4 : ℝ) ^ (b + d + 1 + b) =
          (1 / 4 : ℝ) * (1 / 16 : ℝ) ^ b * (1 / 4 : ℝ) ^ d := by
        rw [show b + d + 1 + b = 2 * b + d + 1 by omega,
          pow_add, pow_add, pow_mul, pow_one]
        norm_num <;> ring
      dsimp [f, strictPairEquiv]
      rw [hpow]
      push_cast
      field_simp [Real.pi_ne_zero] <;> ring
    _ = (1 / (4 * Real.pi)) * ((16 / 15 : ℝ) * (80 / 27 : ℝ)) :=
      (hp.mul_left (1 / (4 * Real.pi))).tsum_eq
    _ = 64 / (81 * Real.pi) := by field_simp [Real.pi_ne_zero] <;> ring

theorem weightedKernelSum_tendsto :
    Tendsto weightedKernelSum atTop (𝓝 (64 / (81 * Real.pi))) := by
  obtain ⟨B, hB, hs, hb⟩ := exists_weightedKernel_dominator
  have h := tendsto_tsum_of_dominated_convergence hs weightedKernelTerm_tendsto
    (Eventually.of_forall hb)
  simpa only [← weightedKernelSum_eq_tsum, weightedKernelLimitTerm_tsum] using h

end Hardinian
