import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.GeomSum
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace Hardinian

open scoped BigOperators

noncomputable def negativeBinomialPrefix (p M : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (M + 1), (-1 : ℝ) ^ j * (Nat.choose (p + j) j : ℝ) * x ^ j

noncomputable def negativeBinomialNumerator (p M : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (p + 1), (Nat.choose (M + j) j : ℝ) * (1 + x) ^ j

def inversePowerDifferenceCoeff (p j : ℕ) : ℚ :=
  (-1 : ℚ) ^ j * (Nat.choose (p + j + 1) (j + 1) : ℚ)

theorem inversePowerDifferenceCoeff_cast (p j : ℕ) :
    (inversePowerDifferenceCoeff p j : ℝ) =
      (-1 : ℝ) ^ j * (Nat.choose (p + j + 1) (j + 1) : ℝ) := by
  norm_num [inversePowerDifferenceCoeff]

theorem inversePowerDifferenceCoeff_zero (p : ℕ) :
    inversePowerDifferenceCoeff p 0 = (p : ℚ) + 1 := by
  norm_num [inversePowerDifferenceCoeff]

theorem negativeBinomial_edge_coeff (p M : ℕ) :
    Nat.choose (p + M + 1) (M + 1) = Nat.choose (M + p + 1) p := by
  rw [show p + M + 1 = M + p + 1 by omega]
  exact Nat.choose_symm_of_eq_add (by omega)

theorem negativeBinomialPrefix_succ (p M : ℕ) (x : ℝ) :
    negativeBinomialPrefix p (M + 1) x = negativeBinomialPrefix p M x +
      (-1 : ℝ) ^ (M + 1) * (Nat.choose (p + M + 1) (M + 1) : ℝ) * x ^ (M + 1) := by
  exact Finset.sum_range_succ _ (M + 1)

theorem negativeBinomialNumerator_succ (p M : ℕ) (x : ℝ) :
    negativeBinomialNumerator (p + 1) M x = negativeBinomialNumerator p M x +
      (Nat.choose (M + p + 1) (p + 1) : ℝ) * (1 + x) ^ (p + 1) := by
  exact Finset.sum_range_succ _ (p + 1)

theorem negativeBinomialNumerator_relation (p M : ℕ) (x : ℝ) :
    negativeBinomialNumerator p M x + x * negativeBinomialNumerator p (M + 1) x =
      (Nat.choose (M + p + 1) p : ℝ) * (1 + x) ^ (p + 1) := by
  induction p with
  | zero => norm_num [negativeBinomialNumerator]
  | succ p ih =>
      have hc : (Nat.choose (M + p + 2) (p + 1) : ℝ) =
          (Nat.choose (M + p + 1) p : ℝ) + (Nat.choose (M + p + 1) (p + 1) : ℝ) := by
        exact_mod_cast Nat.choose_succ_succ' (M + p + 1) p
      rw [negativeBinomialNumerator_succ, negativeBinomialNumerator_succ,
        show M + 1 + p + 1 = M + p + 2 by omega]
      calc
        _ = (negativeBinomialNumerator p M x + x * negativeBinomialNumerator p (M + 1) x) +
            ((Nat.choose (M + p + 1) (p + 1) : ℝ) +
              x * (Nat.choose (M + p + 2) (p + 1) : ℝ)) * (1 + x) ^ (p + 1) := by ring
        _ = _ := by
          rw [ih, pow_succ (1 + x) (p + 1)]
          simp only [Nat.add_assoc] at hc ⊢
          simp only [hc]
          ring

/-- Exact finite identity, valid for all real x, including x=-1. -/
theorem negativeBinomial_finite_identity (p M : ℕ) (x : ℝ) :
    (1 + x) ^ (p + 1) * negativeBinomialPrefix p M x +
      (-1 : ℝ) ^ (M + 1) * x ^ (M + 1) * negativeBinomialNumerator p M x = 1 := by
  induction M with
  | zero =>
      have hR : negativeBinomialNumerator p 0 x =
          ∑ j ∈ Finset.range (p + 1), (1 + x) ^ j := by
        simp [negativeBinomialNumerator]
      have hP : negativeBinomialPrefix p 0 x = 1 := by simp [negativeBinomialPrefix]
      rw [hR, hP]
      norm_num
      have hg := geom_sum_mul (1 + x) (p + 1)
      nlinarith [hg]
  | succ M ih =>
      rw [negativeBinomialPrefix_succ, negativeBinomial_edge_coeff]
      have hR := negativeBinomialNumerator_relation p M x
      have hc : (Nat.choose (M + p + 1) p : ℝ) * (1 + x) ^ (p + 1) -
          x * negativeBinomialNumerator p (M + 1) x = negativeBinomialNumerator p M x := by
        linarith
      calc
        _ = (1 + x) ^ (p + 1) * negativeBinomialPrefix p M x +
            (-1 : ℝ) ^ (M + 1) * x ^ (M + 1) *
              ((Nat.choose (M + p + 1) p : ℝ) * (1 + x) ^ (p + 1) -
                x * negativeBinomialNumerator p (M + 1) x) := by
          rw [pow_succ (-1 : ℝ) (M + 1), pow_succ x (M + 1)]
          ring
        _ = _ := by rw [hc]
        _ = 1 := ih

theorem negativeBinomial_hockey_stick (p M : ℕ) :
    (∑ j ∈ Finset.range (p + 1), Nat.choose (M + j) j) = Nat.choose (M + p + 1) p := by
  calc
    _ = ∑ j ∈ Finset.range (p + 1), Nat.choose (j + M) M := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [show M + j = j + M by omega]
      exact Nat.choose_symm_add
    _ = Nat.choose (p + M + 1) (M + 1) := Nat.sum_range_add_choose p M
    _ = _ := negativeBinomial_edge_coeff p M

theorem negativeBinomialNumerator_bounds (p M : ℕ) (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ negativeBinomialNumerator p M x ∧
      negativeBinomialNumerator p M x ≤ (2 : ℝ) ^ p * (Nat.choose (M + p + 1) p : ℝ) := by
  constructor
  · unfold negativeBinomialNumerator
    apply Finset.sum_nonneg
    intro j hj
    positivity
  · have hsum : (∑ j ∈ Finset.range (p + 1), (Nat.choose (M + j) j : ℝ)) =
        (Nat.choose (M + p + 1) p : ℝ) := by
      exact_mod_cast negativeBinomial_hockey_stick p M
    unfold negativeBinomialNumerator
    calc
      _ ≤ ∑ j ∈ Finset.range (p + 1), (Nat.choose (M + j) j : ℝ) * (2 : ℝ) ^ p := by
        apply Finset.sum_le_sum
        intro j hj
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        exact (pow_le_pow_left₀ (by linarith) (by linarith : 1 + x ≤ 2) j).trans
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by
            have := Finset.mem_range.mp hj
            omega))
      _ = (∑ j ∈ Finset.range (p + 1), (Nat.choose (M + j) j : ℝ)) * (2 : ℝ) ^ p := by
        rw [Finset.sum_mul]
      _ = _ := by rw [hsum]; ring

theorem negativeBinomial_remainder_identity (p M : ℕ) (x : ℝ) (hx : 1 + x ≠ 0) :
    1 / (1 + x) ^ (p + 1) - negativeBinomialPrefix p M x =
      ((-1 : ℝ) ^ (M + 1) * x ^ (M + 1) * negativeBinomialNumerator p M x) /
        (1 + x) ^ (p + 1) := by
  have hd := pow_ne_zero (p + 1) hx
  apply (eq_div_iff hd).2
  calc
    _ = 1 - (1 + x) ^ (p + 1) * negativeBinomialPrefix p M x := by
      field_simp [hd] <;> ring
    _ = _ := by linarith [negativeBinomial_finite_identity p M x]

theorem negativeBinomial_remainder_bound (p M : ℕ) (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    |1 / (1 + x) ^ (p + 1) - negativeBinomialPrefix p M x| ≤
      (2 : ℝ) ^ p * (Nat.choose (M + p + 1) p : ℝ) * x ^ (M + 1) := by
  have hr := negativeBinomialNumerator_bounds p M x hx hx1
  have hd : 0 < (1 + x) ^ (p + 1) := by positivity
  have hd1 : 1 ≤ (1 + x) ^ (p + 1) := one_le_pow₀ (by linarith)
  rw [negativeBinomial_remainder_identity p M x (by positivity)]
  simp only [abs_div, abs_mul, abs_neg_one_pow, one_mul,
    abs_of_nonneg (pow_nonneg hx (M + 1)), abs_of_nonneg hr.1, abs_of_pos hd]
  calc
    _ ≤ x ^ (M + 1) * negativeBinomialNumerator p M x :=
      div_le_self (mul_nonneg (pow_nonneg hx _) hr.1) hd1
    _ ≤ x ^ (M + 1) * ((2 : ℝ) ^ p * (Nat.choose (M + p + 1) p : ℝ)) :=
      mul_le_mul_of_nonneg_left hr.2 (pow_nonneg hx _)
    _ = _ := by ring

theorem inversePowerDifference_prefix (p M : ℕ) (x : ℝ) :
    1 - negativeBinomialPrefix p M x =
      ∑ j ∈ Finset.range M, (inversePowerDifferenceCoeff p j : ℝ) * x ^ (j + 1) := by
  have hP : negativeBinomialPrefix p M x =
      (∑ j ∈ Finset.range M,
        (-1 : ℝ) ^ (j + 1) * (Nat.choose (p + j + 1) (j + 1) : ℝ) * x ^ (j + 1)) + 1 := by
    unfold negativeBinomialPrefix
    rw [Finset.sum_range_succ']
    simp [Nat.add_assoc]
  rw [hP]
  calc
    _ = ∑ j ∈ Finset.range M,
        -((-1 : ℝ) ^ (j + 1) * (Nat.choose (p + j + 1) (j + 1) : ℝ) * x ^ (j + 1)) := by
      rw [Finset.sum_neg_distrib]
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [inversePowerDifferenceCoeff_cast, pow_succ (-1 : ℝ) j]
      ring

theorem inversePowerDifference_prefix_scaled (N p M : ℕ) :
    (∑ j ∈ Finset.range M,
      (inversePowerDifferenceCoeff p j : ℝ) / (N : ℝ) ^ (p + j + 2)) =
      (1 / (N : ℝ) ^ (p + 1)) * (1 - negativeBinomialPrefix p M (1 / (N : ℝ))) := by
  rw [inversePowerDifference_prefix, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [one_div, inv_pow, div_eq_mul_inv, one_mul, pow_add, pow_two, mul_inv_rev]
  ring

theorem inversePower_shift_identity (N p : ℕ) (hN : 1 ≤ N) :
    1 / ((N : ℝ) + 1) ^ (p + 1) =
      (1 / (N : ℝ) ^ (p + 1)) * (1 / (1 + 1 / (N : ℝ)) ^ (p + 1)) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [show ((N : ℝ) + 1) = (N : ℝ) * (1 + 1 / (N : ℝ)) by
    field_simp [hn] <;> ring]
  rw [mul_pow]
  simp only [one_div, mul_inv_rev]
  ring

theorem inversePowerDifference_error (N p M : ℕ) (hN : 1 ≤ N) :
    |1 / (N : ℝ) ^ (p + 1) - 1 / ((N : ℝ) + 1) ^ (p + 1) -
        ∑ j ∈ Finset.range M,
          (inversePowerDifferenceCoeff p j : ℝ) / (N : ℝ) ^ (p + j + 2)| ≤
      ((2 : ℝ) ^ p * (Nat.choose (M + p + 1) p : ℝ)) /
        (N : ℝ) ^ (p + M + 2) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have ht0 : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
  have ht1 : (1 / (N : ℝ) : ℝ) ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
      (show (1 : ℝ) ≤ N by exact_mod_cast hN)
  have he := negativeBinomial_remainder_bound p M (1 / (N : ℝ)) ht0 ht1
  rw [inversePowerDifference_prefix_scaled, inversePower_shift_identity N p hN]
  have hid : 1 / (N : ℝ) ^ (p + 1) -
      (1 / (N : ℝ) ^ (p + 1)) * (1 / (1 + 1 / (N : ℝ)) ^ (p + 1)) -
      (1 / (N : ℝ) ^ (p + 1)) * (1 - negativeBinomialPrefix p M (1 / (N : ℝ))) =
      -(1 / (N : ℝ) ^ (p + 1)) *
        (1 / (1 + 1 / (N : ℝ)) ^ (p + 1) - negativeBinomialPrefix p M (1 / (N : ℝ))) := by ring
  rw [hid, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 1 / (N : ℝ) ^ (p + 1))]
  calc
    _ ≤ (1 / (N : ℝ) ^ (p + 1)) *
        ((2 : ℝ) ^ p * (Nat.choose (M + p + 1) p : ℝ) * (1 / (N : ℝ)) ^ (M + 1)) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by
      simp only [one_div, inv_pow, div_eq_mul_inv, one_mul, pow_add, pow_two, mul_inv_rev]
      ring

end Hardinian
