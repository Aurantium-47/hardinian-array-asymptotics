import Hardinian.StirlingIncrementRemainder
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum

namespace Hardinian

open scoped BigOperators

def stirlingIncrementCoeff (j : ℕ) : ℚ :=
  (-1 : ℚ) ^ j * ((j : ℚ) + 1) /
    (2 * ((j : ℚ) + 2) * ((j : ℚ) + 3))

theorem stirlingIncrementCoeff_zero : stirlingIncrementCoeff 0 = 1 / 12 := by
  norm_num [stirlingIncrementCoeff]

theorem stirlingIncrementCoeff_cast (j : ℕ) :
    (stirlingIncrementCoeff j : ℝ) =
      (-1 : ℝ) ^ j * ((j : ℝ) + 1) /
        (2 * ((j : ℝ) + 2) * ((j : ℝ) + 3)) := by
  norm_num [stirlingIncrementCoeff]

theorem stirlingIncrementCoeff_abs (j : ℕ) : |(stirlingIncrementCoeff j : ℝ)| ≤ 1 := by
  rw [stirlingIncrementCoeff_cast, abs_div, abs_mul, abs_neg_one_pow, one_mul,
    abs_of_pos (by positivity : (0 : ℝ) < (j : ℝ) + 1),
    abs_of_pos (by positivity : (0 : ℝ) < 2 * ((j : ℝ) + 2) * ((j : ℝ) + 3))]
  apply (div_le_one (by positivity)).2
  nlinarith [Nat.cast_nonneg (α := ℝ) j, sq_nonneg (j : ℝ)]

theorem stirlingIncrementCoeff_pair (j : ℕ) :
    (stirlingIncrementCoeff j : ℝ) =
      (-1 : ℝ) ^ (j + 1) / (2 * ((j : ℝ) + 2)) +
        (-1 : ℝ) ^ (j + 2) / ((j : ℝ) + 3) := by
  have h2 : (j : ℝ) + 2 ≠ 0 := by positivity
  have h3 : (j : ℝ) + 3 ≠ 0 := by positivity
  rw [stirlingIncrementCoeff_cast, pow_add (-1 : ℝ) j 1, pow_add (-1 : ℝ) j 2]
  norm_num
  field_simp [h2, h3] <;> ring

noncomputable def stirlingLogPrefix (L : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range L, (-1 : ℝ) ^ i * t ^ (i + 1) / ((i : ℝ) + 1)

noncomputable def stirlingIncrementPoly (K : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range K, (stirlingIncrementCoeff j : ℝ) * t ^ (j + 2)

theorem stirlingLogPrefix_succ (L : ℕ) (t : ℝ) :
    stirlingLogPrefix (L + 1) t = stirlingLogPrefix L t +
      (-1 : ℝ) ^ L * t ^ (L + 1) / ((L : ℝ) + 1) := by
  exact Finset.sum_range_succ _ L

theorem stirlingIncrementPoly_succ (K : ℕ) (t : ℝ) :
    stirlingIncrementPoly (K + 1) t = stirlingIncrementPoly K t +
      (stirlingIncrementCoeff K : ℝ) * t ^ (K + 2) := by
  exact Finset.sum_range_succ _ K

theorem stirlingIncrementPoly_inv (N K : ℕ) :
    stirlingIncrementPoly K (1 / (N : ℝ)) =
      ∑ j ∈ Finset.range K, (stirlingIncrementCoeff j : ℝ) / (N : ℝ) ^ (j + 2) := by
  unfold stirlingIncrementPoly
  apply Finset.sum_congr rfl
  intro j hj
  simp only [one_div, inv_pow, div_eq_mul_inv, one_mul]

theorem stirlingIncrement_log_identity (N : ℕ) (hN : 1 ≤ N) :
    Real.log (Stirling.stirlingSeq N) - Real.log (Stirling.stirlingSeq (N + 1)) =
      ((N : ℝ) + 1 / 2) * Real.log (1 + 1 / (N : ℝ)) - 1 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hn1 : (N : ℝ) + 1 ≠ 0 := by positivity
  have hfact : (N.factorial : ℝ) ≠ 0 := by positivity
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  have hlog : Real.log (1 + 1 / (N : ℝ)) = Real.log ((N : ℝ) + 1) - Real.log (N : ℝ) := by
    rw [show (1 + 1 / (N : ℝ)) = ((N : ℝ) + 1) / (N : ℝ) by
      field_simp [hn]]
    exact Real.log_div hn1 hn
  rw [Stirling.log_stirlingSeq_formula, Stirling.log_stirlingSeq_formula,
    Nat.factorial_succ]
  push_cast
  rw [Real.log_mul hn1 hfact, Real.log_mul htwo hn, Real.log_mul htwo hn1,
    Real.log_div hn (Real.exp_ne_zero 1), Real.log_div hn1 (Real.exp_ne_zero 1), hlog]
  simp only [Real.log_exp]
  ring

/-- A finite polynomial identity; no Taylor hypothesis is used. -/
theorem stirlingIncrement_polynomial_identity (K : ℕ) (t : ℝ) :
    (1 + t / 2) * stirlingLogPrefix (K + 2) t - t =
      t * stirlingIncrementPoly K t +
        ((-1 : ℝ) ^ (K + 1) / (2 * ((K : ℝ) + 2))) * t ^ (K + 3) := by
  induction K with
  | zero =>
      norm_num [stirlingLogPrefix, stirlingIncrementPoly, Finset.sum_range_succ]
      ring
  | succ K ih =>
      have h2 : (K : ℝ) + 2 ≠ 0 := by positivity
      have h3 : (K : ℝ) + 3 ≠ 0 := by positivity
      have hH : stirlingLogPrefix (K + 1 + 2) t = stirlingLogPrefix (K + 2) t +
          (-1 : ℝ) ^ (K + 2) * t ^ (K + 2 + 1) / (((K + 2 : ℕ) : ℝ) + 1) := by
        rw [show K + 1 + 2 = (K + 2) + 1 by omega]
        exact stirlingLogPrefix_succ (K + 2) t
      rw [hH, stirlingIncrementPoly_succ]
      calc
        _ = ((1 + t / 2) * stirlingLogPrefix (K + 2) t - t) +
            (1 + t / 2) * ((-1 : ℝ) ^ (K + 2) * t ^ (K + 2 + 1) /
              (((K + 2 : ℕ) : ℝ) + 1)) := by ring
        _ = _ := by
          rw [ih, stirlingIncrementCoeff_pair]
          push_cast
          simp only [pow_add]
          field_simp [h2, h3] <;> ring

theorem stirlingLogPrefix_negative (L : ℕ) (t : ℝ) :
    (∑ i ∈ Finset.range L, (-t) ^ (i + 1) / ((i : ℝ) + 1)) =
      -stirlingLogPrefix L t := by
  unfold stirlingLogPrefix
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← neg_one_mul t, mul_pow, pow_succ (-1 : ℝ) i]
  ring

theorem stirlingLogPrefix_remainder (L : ℕ) (t : ℝ) (ht : 0 ≤ t) (ht1 : t < 1) :
    |Real.log (1 + t) - stirlingLogPrefix L t| ≤ t ^ (L + 1) / (1 - t) := by
  have h := Real.abs_log_sub_add_sum_range_le
    (x := -t) (by simpa only [abs_neg, abs_of_nonneg ht] using ht1) L
  simp only [Nat.cast_add, Nat.cast_one] at h
  rw [stirlingLogPrefix_negative] at h
  simpa only [sub_neg_eq_add, abs_neg, abs_of_nonneg ht, neg_add_eq_sub] using h

theorem stirlingIncrement_remainder_identity (K : ℕ) (t : ℝ) (ht : t ≠ 0) :
    (1 / t + 1 / 2) * Real.log (1 + t) - 1 - stirlingIncrementPoly K t =
      (1 / t + 1 / 2) * (Real.log (1 + t) - stirlingLogPrefix (K + 2) t) +
        ((-1 : ℝ) ^ (K + 1) / (2 * ((K : ℝ) + 2))) * t ^ (K + 2) := by
  have hp := stirlingIncrement_polynomial_identity K t
  rw [show K + 3 = (K + 2) + 1 by omega, pow_succ] at hp
  have hrel : (1 / t + 1 / 2) * stirlingLogPrefix (K + 2) t - 1 =
      stirlingIncrementPoly K t +
        ((-1 : ℝ) ^ (K + 1) / (2 * ((K : ℝ) + 2))) * t ^ (K + 2) := by
    apply mul_left_cancel₀ ht
    calc
      _ = (1 + t / 2) * stirlingLogPrefix (K + 2) t - t := by
        field_simp [ht] <;> ring
      _ = _ := hp
      _ = _ := by ring
  calc
    _ = (1 / t + 1 / 2) * (Real.log (1 + t) - stirlingLogPrefix (K + 2) t) +
        ((1 / t + 1 / 2) * stirlingLogPrefix (K + 2) t - 1) -
        stirlingIncrementPoly K t := by ring
    _ = _ := by rw [hrel]; ring

theorem stirlingLogLastCoeff_abs (K : ℕ) :
    |(-1 : ℝ) ^ (K + 1) / (2 * ((K : ℝ) + 2))| ≤ 1 / 4 := by
  rw [abs_div, abs_neg_one_pow, abs_of_pos (by positivity : (0 : ℝ) < 2 * ((K : ℝ) + 2))]
  apply one_div_le_one_div_of_le (by norm_num)
  linarith [Nat.cast_nonneg (α := ℝ) K]

theorem stirlingIncrement_inversePower_error_ge_two (N K : ℕ) (hN : 2 ≤ N) :
    |(Real.log (Stirling.stirlingSeq N) - Real.log (Stirling.stirlingSeq (N + 1))) -
        ∑ j ∈ Finset.range K, (stirlingIncrementCoeff j : ℝ) / (N : ℝ) ^ (j + 2)| ≤
      3 / (N : ℝ) ^ (K + 2) := by
  let t : ℝ := 1 / (N : ℝ)
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hn2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have ht : 0 < t := by dsimp [t]; positivity
  have ht2 : t ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hn2
  have ht1 : t < 1 := by linarith
  have hd : 0 < 1 - t := by linarith
  have hnt : (1 / t : ℝ) = (N : ℝ) := by simp only [t, one_div, inv_inv]
  have hlog := stirlingLogPrefix_remainder (K + 2) t ht.le ht1
  have hfrac : (1 + t / 2) / (1 - t) ≤ (5 : ℝ) / 2 := by
    apply (div_le_iff₀ hd).2
    linarith
  have hlarge : |((N : ℝ) + 1 / 2) *
      (Real.log (1 + t) - stirlingLogPrefix (K + 2) t)| ≤
      (5 / 2) * t ^ (K + 2) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) + 1 / 2)]
    calc
      _ ≤ ((N : ℝ) + 1 / 2) * (t ^ (K + 2 + 1) / (1 - t)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = ((1 + t / 2) / (1 - t)) * t ^ (K + 2) := by
        rw [← hnt, pow_succ]
        field_simp [ht.ne', hd.ne'] <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hfrac (by positivity)
  have hsmall : |((-1 : ℝ) ^ (K + 1) / (2 * ((K : ℝ) + 2))) * t ^ (K + 2)| ≤
      (1 / 4) * t ^ (K + 2) := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg ht.le _)]
    exact mul_le_mul_of_nonneg_right (stirlingLogLastCoeff_abs K) (by positivity)
  have heq : (Real.log (Stirling.stirlingSeq N) - Real.log (Stirling.stirlingSeq (N + 1))) -
      stirlingIncrementPoly K t =
        ((N : ℝ) + 1 / 2) * (Real.log (1 + t) - stirlingLogPrefix (K + 2) t) +
          ((-1 : ℝ) ^ (K + 1) / (2 * ((K : ℝ) + 2))) * t ^ (K + 2) := by
    rw [stirlingIncrement_log_identity N (by omega)]
    simpa only [hnt] using stirlingIncrement_remainder_identity K t ht.ne'
  have hb : |(Real.log (Stirling.stirlingSeq N) - Real.log (Stirling.stirlingSeq (N + 1))) -
      stirlingIncrementPoly K t| ≤ 3 * t ^ (K + 2) := by
    rw [heq]
    exact (abs_add _ _).trans ((add_le_add hlarge hsmall).trans (by
      nlinarith [pow_nonneg ht.le (K + 2)]))
  change |(Real.log (Stirling.stirlingSeq N) - Real.log (Stirling.stirlingSeq (N + 1))) -
    stirlingIncrementPoly K (1 / (N : ℝ))| ≤ 3 * (1 / (N : ℝ)) ^ (K + 2) at hb
  rw [stirlingIncrementPoly_inv] at hb
  simpa only [one_div, inv_pow, div_eq_mul_inv, one_mul] using hb

theorem stirlingIncrement_abs_one :
    |Real.log (Stirling.stirlingSeq 1) - Real.log (Stirling.stirlingSeq 2)| ≤ 1 / 24 := by
  have h := stirlingStep_truncation_bounds 1 0 (by omega)
  norm_num only [Finset.range_zero, Finset.sum_empty, sub_zero,
    Nat.cast_zero, Nat.cast_one, pow_zero] at h
  simpa only [abs_of_nonneg h.1] using h.2

theorem stirlingIncrement_inversePower_error (N K : ℕ) (hN : 1 ≤ N) :
    |(Real.log (Stirling.stirlingSeq N) - Real.log (Stirling.stirlingSeq (N + 1))) -
        ∑ j ∈ Finset.range K, (stirlingIncrementCoeff j : ℝ) / (N : ℝ) ^ (j + 2)| ≤
      ((K : ℝ) + 3) / (N : ℝ) ^ (K + 2) := by
  by_cases h1 : N = 1
  · subst N
    simp only [Nat.cast_one, one_pow, div_one]
    have hs : |∑ j ∈ Finset.range K, (stirlingIncrementCoeff j : ℝ)| ≤ (K : ℝ) := by
      calc
        _ ≤ ∑ j ∈ Finset.range K, |(stirlingIncrementCoeff j : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j ∈ Finset.range K, (1 : ℝ) :=
          Finset.sum_le_sum (fun j hj => stirlingIncrementCoeff_abs j)
        _ = _ := by simp
    calc
      _ ≤ |Real.log (Stirling.stirlingSeq 1) - Real.log (Stirling.stirlingSeq 2)| +
          |∑ j ∈ Finset.range K, (stirlingIncrementCoeff j : ℝ)| := by
        simpa only [sub_eq_add_neg, abs_neg] using abs_add
          (Real.log (Stirling.stirlingSeq 1) - Real.log (Stirling.stirlingSeq 2))
          (-(∑ j ∈ Finset.range K, (stirlingIncrementCoeff j : ℝ)))
      _ ≤ (1 / 24) + (K : ℝ) := add_le_add stirlingIncrement_abs_one hs
      _ ≤ _ := by linarith
  · exact (stirlingIncrement_inversePower_error_ge_two N K (by omega)).trans
      (div_le_div_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℝ) K]) (by positivity))

end Hardinian
