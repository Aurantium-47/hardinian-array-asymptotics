import Hardinian.KernelError
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp

namespace Hardinian

noncomputable def binomialKernel (u v : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico u v, binomialMass (u + v) j

theorem binomialKernel_relative_sum (u v : ℕ) :
    binomialKernel u v / (((v - u : ℕ) : ℝ) * centralMass (u + v)) =
      (∑ j ∈ Finset.Ico u v, relativeMass (u + v) j) / ((v - u : ℕ) : ℝ) := by
  simp only [binomialKernel, relativeMass, ← Finset.sum_div, div_div, mul_comm]

theorem binomialKernel_deficit_sum (u v : ℕ) (huv : u < v) :
    ((v - u : ℕ) : ℝ) *
        (1 - binomialKernel u v / (((v - u : ℕ) : ℝ) * centralMass (u + v))) =
      ∑ j ∈ Finset.Ico u v, (1 - relativeMass (u + v) j) := by
  have hd : ((v - u : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt huv))
  rw [binomialKernel_relative_sum, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
  field_simp [hd] <;> ring

theorem interval_mass_deficit (u v j : ℕ) (huv : u < v) (hj : j ∈ Finset.Ico u v) :
    0 ≤ 1 - relativeMass (u + v) j ∧
      1 - relativeMass (u + v) j ≤
        2 * (((v - u : ℕ) : ℝ) + 1) ^ 2 / ((u + v : ℕ) : ℝ) := by
  have hju : u ≤ j := (Finset.mem_Ico.mp hj).1
  have hjv : j < v := (Finset.mem_Ico.mp hj).2
  have hc1 : u ≤ (u + v) / 2 := by omega
  have hc2 : (u + v) / 2 ≤ v := by omega
  have hju' : (u : ℝ) ≤ j := by exact_mod_cast hju
  have hjv' : (j : ℝ) ≤ v := by exact_mod_cast (Nat.le_of_lt hjv)
  have hc1' : (u : ℝ) ≤ (((u + v) / 2 : ℕ) : ℝ) := by exact_mod_cast hc1
  have hc2' : (((u + v) / 2 : ℕ) : ℝ) ≤ v := by exact_mod_cast hc2
  have hdist : |(j : ℝ) - (((u + v) / 2 : ℕ) : ℝ)| ≤ ((v - u : ℕ) : ℝ) := by
    rw [Nat.cast_sub (Nat.le_of_lt huv)]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hsq := pow_le_pow_left₀
    (by positivity : 0 ≤ |(j : ℝ) - (((u + v) / 2 : ℕ) : ℝ)| + 1)
    (add_le_add_right hdist 1) 2
  have h := binomial_relative_error (u + v) j (by omega) (by omega)
  change 0 ≤ 1 - relativeMass (u + v) j ∧ _ at h
  refine ⟨h.1, h.2.trans ?_⟩
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  nlinarith only [hsq]

theorem binomialKernel_relative_error (u v : ℕ) (huv : u < v) :
    0 ≤ 1 - binomialKernel u v / (((v - u : ℕ) : ℝ) * centralMass (u + v)) ∧
      1 - binomialKernel u v / (((v - u : ℕ) : ℝ) * centralMass (u + v)) ≤
        2 * (((v - u : ℕ) : ℝ) + 1) ^ 2 / ((u + v : ℕ) : ℝ) := by
  have hd : (0 : ℝ) < ((v - u : ℕ) : ℝ) := by
    exact_mod_cast (Nat.sub_pos_of_lt huv)
  have h0 : 0 ≤ ∑ j ∈ Finset.Ico u v, (1 - relativeMass (u + v) j) :=
    Finset.sum_nonneg fun j hj => (interval_mass_deficit u v j huv hj).1
  have hle : (∑ j ∈ Finset.Ico u v, (1 - relativeMass (u + v) j)) ≤
      ∑ _j ∈ Finset.Ico u v,
        (2 * (((v - u : ℕ) : ℝ) + 1) ^ 2 / ((u + v : ℕ) : ℝ)) :=
    Finset.sum_le_sum fun j hj => (interval_mass_deficit u v j huv hj).2
  rw [← binomialKernel_deficit_sum u v huv] at h0 hle
  simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at hle
  constructor
  · exact (mul_le_mul_left hd).mp (by simpa only [mul_zero] using h0)
  · exact (mul_le_mul_left hd).mp hle

theorem binomialKernel_offset_error (N a b : ℕ) (hN : 1 ≤ N)
    (hba : b < a) (ha : a ≤ N) (hsum : a + b ≤ N) :
    |binomialKernel (N - a) (N - b) /
        (((a : ℝ) - b) * centralMass ((N - a) + (N - b))) - 1| ≤
      2 * ((a : ℝ) + 1) ^ 2 / (N : ℝ) := by
  have hwidth : (N - b) - (N - a) = a - b := by omega
  have h := binomialKernel_relative_error (N - a) (N - b) (by omega)
  rw [hwidth, Nat.cast_sub (Nat.le_of_lt hba)] at h
  rw [abs_sub_comm, abs_of_nonneg h.1]
  apply h.2.trans
  have hba' : (b : ℝ) ≤ a := by exact_mod_cast (Nat.le_of_lt hba)
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hsq := pow_le_pow_left₀
    (by linarith : 0 ≤ (a : ℝ) - b + 1)
    (by linarith : (a : ℝ) - b + 1 ≤ (a : ℝ) + 1) 2
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmn : (N : ℝ) ≤ ((N - a + (N - b) : ℕ) : ℝ) := by
    exact_mod_cast (show N ≤ N - a + (N - b) by omega)
  calc
    2 * ((a : ℝ) - b + 1) ^ 2 / ((N - a + (N - b) : ℕ) : ℝ) ≤
        2 * ((a : ℝ) + 1) ^ 2 / ((N - a + (N - b) : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right (by nlinarith only [hsq]) (Nat.cast_nonneg _)
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hn hmn

end Hardinian
