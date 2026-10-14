import Hardinian.NormalizedKernel
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum

open Filter
open scoped Topology

namespace Hardinian

theorem centralMass_global_square_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ m : ℕ, (m : ℝ) * centralMass m ^ 2 ≤ B := by
  obtain ⟨K, hK⟩ := centralMass_square_tendsto.bddAbove_range
  have hmax : 0 < max K 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨(2 / Real.pi) * max K 1, by positivity, ?_⟩
  intro m
  have hm : Real.pi * (m : ℝ) / 2 * centralMass m ^ 2 ≤ K := hK ⟨m, rfl⟩
  calc
    (m : ℝ) * centralMass m ^ 2 =
        (2 / Real.pi) * (Real.pi * (m : ℝ) / 2 * centralMass m ^ 2) := by
      field_simp [Real.pi_ne_zero] <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hm.trans (le_max_left _ _)) (by positivity)

theorem kernel_le_width_mul_central (u v : ℕ) (huv : u < v) :
    binomialKernel u v ≤ ((v - u : ℕ) : ℝ) * centralMass (u + v) := by
  have h := binomialKernel_relative_error u v huv
  have hd : (0 : ℝ) < ((v - u : ℕ) : ℝ) := by exact_mod_cast (Nat.sub_pos_of_lt huv)
  exact (div_le_one (mul_pos hd (centralMass_pos _))).mp (by linarith [h.1])

theorem kernel_global_square_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ N a b : ℕ, b < a → a ≤ N →
      (N : ℝ) * binomialKernel (N - a) (N - b) ^ 2 ≤
        B * ((a : ℝ) + 1) * ((a : ℝ) - b) ^ 2 := by
  obtain ⟨B, hB, hc⟩ := centralMass_global_square_bound
  refine ⟨B, hB, ?_⟩
  intro N a b hba ha
  let m := (N - a) + (N - b)
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hNm : N ≤ (a + 1) * m := by
    calc
      N ≤ a + m := by dsimp [m]; omega
      _ ≤ a * m + m := Nat.add_le_add_right (by simpa using Nat.mul_le_mul_left a hm) m
      _ = _ := by ring
  have hNm' : (N : ℝ) ≤ ((a : ℝ) + 1) * (m : ℝ) := by exact_mod_cast hNm
  have hwidth : (N - b) - (N - a) = a - b := by omega
  have hQ := kernel_le_width_mul_central (N - a) (N - b) (by omega)
  rw [hwidth, Nat.cast_sub (Nat.le_of_lt hba)] at hQ
  have hs := pow_le_pow_left₀ (binomialKernel_nonneg (N - a) (N - b)) hQ 2
  have hmc := hc m
  calc
    (N : ℝ) * binomialKernel (N - a) (N - b) ^ 2 ≤
        (N : ℝ) * (((a : ℝ) - b) * centralMass m) ^ 2 :=
      mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)
    _ = ((a : ℝ) - b) ^ 2 * ((N : ℝ) * centralMass m ^ 2) := by ring
    _ ≤ ((a : ℝ) - b) ^ 2 * ((((a : ℝ) + 1) * (m : ℝ)) * centralMass m ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hNm' (sq_nonneg _)) (sq_nonneg _)
    _ = (((a : ℝ) + 1) * ((a : ℝ) - b) ^ 2) * ((m : ℝ) * centralMass m ^ 2) := by ring
    _ ≤ (((a : ℝ) + 1) * ((a : ℝ) - b) ^ 2) * B :=
      mul_le_mul_of_nonneg_left hmc (by positivity)
    _ = _ := by ring

noncomputable def weightedKernelTerm (N : ℕ) (p : ℕ × ℕ) : ℝ :=
  if p.2 < p.1 ∧ p.1 ≤ N then
    (1 / 4 : ℝ) ^ (p.1 + p.2) * (N : ℝ) * binomialKernel (N - p.1) (N - p.2) ^ 2
  else 0

noncomputable def kernelMajorant (B : ℝ) (p : ℕ × ℕ) : ℝ :=
  B * ((p.1 : ℝ) + 1) ^ 3 * (1 / 4 : ℝ) ^ (p.1 + p.2)

theorem weightedKernelTerm_nonneg (N : ℕ) (p : ℕ × ℕ) : 0 ≤ weightedKernelTerm N p := by
  unfold weightedKernelTerm
  split_ifs <;> positivity

theorem kernelMajorant_summable (B : ℝ) : Summable (kernelMajorant B) := by
  have hs (k : ℕ) : Summable (fun a : ℕ => (a : ℝ) ^ k * (1 / 4 : ℝ) ^ a) :=
    summable_pow_mul_geometric_of_norm_lt_one k (by norm_num)
  have hp : Summable (fun a : ℕ => ((a : ℝ) + 1) ^ 3 * (1 / 4 : ℝ) ^ a) := by
    apply ((((hs 3).add ((hs 2).mul_left 3)).add ((hs 1).mul_left 3)).add (hs 0)).congr
    intro a
    simp only [pow_zero, pow_one]
    ring
  have hg : Summable (fun b : ℕ => (1 / 4 : ℝ) ^ b) := by simpa only [pow_zero, one_mul] using hs 0
  have h := (hp.mul_of_nonneg hg (fun a => by positivity) (fun b => by positivity)).mul_left B
  apply h.congr
  intro p
  simp only [kernelMajorant, pow_add]
  ring

theorem exists_weightedKernel_dominator :
    ∃ B : ℝ, 0 < B ∧ Summable (kernelMajorant B) ∧
      ∀ N : ℕ, ∀ p : ℕ × ℕ, ‖weightedKernelTerm N p‖ ≤ kernelMajorant B p := by
  obtain ⟨B, hB, hbound⟩ := kernel_global_square_bound
  refine ⟨B, hB, kernelMajorant_summable B, ?_⟩
  intro N p
  rcases p with ⟨a, b⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (weightedKernelTerm_nonneg _ _)]
  by_cases h : b < a ∧ a ≤ N
  · have hba : (b : ℝ) ≤ a := by exact_mod_cast (Nat.le_of_lt h.1)
    have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
    have hs := pow_le_pow_left₀ (sub_nonneg.mpr hba)
      (by linarith : (a : ℝ) - b ≤ (a : ℝ) + 1) 2
    have hh : (N : ℝ) * binomialKernel (N - a) (N - b) ^ 2 ≤ B * ((a : ℝ) + 1) ^ 3 := by
      calc
        _ ≤ B * ((a : ℝ) + 1) * ((a : ℝ) - b) ^ 2 := hbound N a b h.1 h.2
        _ ≤ B * ((a : ℝ) + 1) * ((a : ℝ) + 1) ^ 2 :=
          mul_le_mul_of_nonneg_left hs (by positivity)
        _ = _ := by ring
    simp only [weightedKernelTerm, h, and_self, if_true, kernelMajorant]
    have hmul := mul_le_mul_of_nonneg_left hh (by positivity : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ (a + b))
    nlinarith only [hmul]
  · simp only [weightedKernelTerm, h, if_false, kernelMajorant]
    positivity

theorem weightedKernelTerm_summable (N : ℕ) : Summable (weightedKernelTerm N) := by
  obtain ⟨B, hB, hs, hb⟩ := exists_weightedKernel_dominator
  exact hs.of_norm_bounded _ (hb N)

end Hardinian
