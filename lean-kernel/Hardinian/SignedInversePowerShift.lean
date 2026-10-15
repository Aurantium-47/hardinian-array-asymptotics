import Hardinian.InversePowerDifferences

namespace Hardinian

open scoped BigOperators

theorem negativeBinomialNumerator_signed_bounds (p M : ℕ) (x : ℝ)
    (hx : |x| ≤ (1 / 2 : ℝ)) :
    0 ≤ negativeBinomialNumerator p M x ∧
      negativeBinomialNumerator p M x ≤
        (2 : ℝ) ^ p * (Nat.choose (M + p + 1) p : ℝ) := by
  have hxlo := (abs_le.mp hx).1
  have hxhi := (abs_le.mp hx).2
  have hbase : 0 ≤ 1 + x := by linarith
  have hup : 1 + x ≤ 2 := by linarith
  constructor
  · unfold negativeBinomialNumerator
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hbase _)
  · have hsum : (∑ j ∈ Finset.range (p + 1), (Nat.choose (M + j) j : ℝ)) =
        (Nat.choose (M + p + 1) p : ℝ) := by
      exact_mod_cast negativeBinomial_hockey_stick p M
    unfold negativeBinomialNumerator
    calc
      _ ≤ ∑ j ∈ Finset.range (p + 1), (Nat.choose (M + j) j : ℝ) * (2 : ℝ) ^ p := by
        apply Finset.sum_le_sum
        intro j hj
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        exact (pow_le_pow_left₀ hbase hup j).trans
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by
            have := Finset.mem_range.mp hj
            omega))
      _ = (∑ j ∈ Finset.range (p + 1), (Nat.choose (M + j) j : ℝ)) * (2 : ℝ) ^ p := by
        rw [Finset.sum_mul]
      _ = _ := by rw [hsum]; ring

theorem negativeBinomial_signed_denominator_bounds (p : ℕ) (x : ℝ)
    (hx : |x| ≤ (1 / 2 : ℝ)) :
    0 < (1 + x) ^ (p + 1) ∧
      (1 / (1 + x) ^ (p + 1) : ℝ) ≤ (2 : ℝ) ^ (p + 1) := by
  have hhalf : (1 / 2 : ℝ) ≤ 1 + x := by have := (abs_le.mp hx).1; linarith
  have hpos : 0 < 1 + x := by linarith
  refine ⟨pow_pos hpos _, ?_⟩
  calc
    _ ≤ 1 / ((1 / 2 : ℝ) ^ (p + 1)) :=
      one_div_le_one_div_of_le (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) _)
        (pow_le_pow_left₀ (by norm_num) hhalf (p + 1))
    _ = _ := by rw [div_pow, one_pow, one_div_div, div_one]

theorem negativeBinomial_signed_remainder_bound (p M : ℕ) (x : ℝ)
    (hx : |x| ≤ (1 / 2 : ℝ)) :
    |1 / (1 + x) ^ (p + 1) - negativeBinomialPrefix p M x| ≤
      (2 : ℝ) ^ (2 * p + 1) * (Nat.choose (M + p + 1) p : ℝ) * |x| ^ (M + 1) := by
  have hr := negativeBinomialNumerator_signed_bounds p M x hx
  have hd := negativeBinomial_signed_denominator_bounds p x hx
  have hpos : 0 < 1 + x := by have := (abs_le.mp hx).1; linarith
  rw [negativeBinomial_remainder_identity p M x hpos.ne']
  simp only [abs_div, abs_mul, abs_neg_one_pow, one_mul, abs_pow,
    abs_of_nonneg hpos.le, abs_of_nonneg hr.1]
  calc
    _ = (|x| ^ (M + 1) * negativeBinomialNumerator p M x) *
        (1 / (1 + x) ^ (p + 1)) := by simp only [div_eq_mul_inv, one_mul]
    _ ≤ (|x| ^ (M + 1) * ((2 : ℝ) ^ p * (Nat.choose (M + p + 1) p : ℝ))) *
        (2 : ℝ) ^ (p + 1) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hr.2 (by positivity)) hd.2
        (by positivity) (by positivity)
    _ = ((2 : ℝ) ^ p * (2 : ℝ) ^ (p + 1)) *
        (Nat.choose (M + p + 1) p : ℝ) * |x| ^ (M + 1) := by ring
    _ = _ := by rw [← pow_add, show p + (p + 1) = 2 * p + 1 by omega]

theorem negativeBinomialPrefix_signed_scale (p M : ℕ) (A h : ℝ) (hA : 0 < A) :
    (1 / A ^ (p + 1)) * negativeBinomialPrefix p M (h / A) =
      ∑ j ∈ Finset.range (M + 1),
        (-1 : ℝ) ^ j * (Nat.choose (p + j) j : ℝ) * h ^ j / A ^ (p + j + 1) := by
  unfold negativeBinomialPrefix
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [div_pow, show p + j + 1 = (p + 1) + j by omega, pow_add]
  field_simp [hA.ne'] <;> ring

theorem signedShift_domain (A h : ℝ) (hA : 0 < A) (hh : |h| ≤ A / 2) :
    |h / A| ≤ (1 / 2 : ℝ) ∧ 0 < A + h := by
  constructor
  · rw [abs_div, abs_of_pos hA]
    apply (div_le_iff₀ hA).2
    linarith
  · have := (abs_le.mp hh).1
    linarith

theorem shiftedInversePower_identity (p : ℕ) (A h : ℝ) (hA : 0 < A) :
    1 / (A + h) ^ (p + 1) =
      (1 / A ^ (p + 1)) * (1 / (1 + h / A) ^ (p + 1)) := by
  have he : A + h = A * (1 + h / A) := by field_simp [hA.ne'] <;> ring
  rw [he, mul_pow]
  simp only [one_div, mul_inv_rev]
  ring

theorem shiftedInversePower_remainder_bound (p M : ℕ) (A h : ℝ)
    (hA : 0 < A) (hh : |h| ≤ A / 2) :
    |1 / (A + h) ^ (p + 1) -
        (1 / A ^ (p + 1)) * negativeBinomialPrefix p M (h / A)| ≤
      (2 : ℝ) ^ (2 * p + 1) * (Nat.choose (M + p + 1) p : ℝ) *
        |h| ^ (M + 1) / A ^ (p + M + 2) := by
  have hdomain := signedShift_domain A h hA hh
  have hb := negativeBinomial_signed_remainder_bound p M (h / A) hdomain.1
  rw [shiftedInversePower_identity p A h hA, ← mul_sub, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / A ^ (p + 1))]
  calc
    _ ≤ (1 / A ^ (p + 1)) *
        ((2 : ℝ) ^ (2 * p + 1) * (Nat.choose (M + p + 1) p : ℝ) *
          |h / A| ^ (M + 1)) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by
      rw [abs_div, abs_of_pos hA, div_pow,
        show p + M + 2 = (p + 1) + (M + 1) by omega, pow_add]
      simp only [one_div, div_eq_mul_inv, one_mul, mul_inv_rev]
      ring

end Hardinian
