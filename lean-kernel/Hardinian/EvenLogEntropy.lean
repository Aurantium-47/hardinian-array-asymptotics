import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Commute
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace Hardinian

open Finset

noncomputable def evenLogEntropy (x : ℝ) : ℝ :=
  (1 + x) * Real.log (1 + x) + (1 - x) * Real.log (1 - x)

noncomputable def evenLogEntropyPrefix (H : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ range H, x ^ (2 * i + 2) / (((i : ℝ) + 1) * (2 * (i : ℝ) + 1))

theorem evenLogEntropy_finite_identity (H : ℕ) (x : ℝ) :
    -(1 + x) * (∑ i ∈ range (2 * H + 1), (-x) ^ (i + 1) / ((i : ℝ) + 1))
      - (1 - x) * (∑ i ∈ range (2 * H + 1), x ^ (i + 1) / ((i : ℝ) + 1)) =
    evenLogEntropyPrefix H x + 2 * x ^ (2 * H + 2) / (2 * (H : ℝ) + 1) := by
  induction H with
  | zero =>
      simp [evenLogEntropyPrefix]
      <;> ring
  | succ H ih =>
      have hsum (z : ℝ) :
          (∑ i ∈ range (2 * (H + 1) + 1), z ^ (i + 1) / ((i : ℝ) + 1)) =
          (∑ i ∈ range (2 * H + 1), z ^ (i + 1) / ((i : ℝ) + 1)) +
            z ^ (2 * H + 2) / (2 * (H : ℝ) + 2) +
            z ^ (2 * H + 3) / (2 * (H : ℝ) + 3) := by
        rw [show 2 * (H + 1) + 1 = (2 * H + 1) + 1 + 1 by omega,
          sum_range_succ, sum_range_succ]
        simp only [show 2 * H + 1 + 1 = 2 * H + 2 by omega,
          show 2 * H + 2 + 1 = 2 * H + 3 by omega,
          Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
        ring
      have hnegEven : (-x) ^ (2 * H + 2) = x ^ (2 * H + 2) := by
        rw [show 2 * H + 2 = 2 * (H + 1) by omega, pow_mul, pow_mul, neg_sq]
      have hnegOdd : (-x) ^ (2 * H + 3) = -(x ^ (2 * H + 3)) := by
        calc
          _ = (-x) ^ (2 * H + 2) * (-x) := pow_succ _ _
          _ = -(x ^ (2 * H + 2) * x) := by rw [hnegEven]; ring
          _ = -(x ^ (2 * H + 3)) := congrArg Neg.neg (pow_succ x (2 * H + 2)).symm
      have hpowStep : x ^ (2 * H + 4) = x ^ (2 * H + 3) * x := pow_succ _ _
      have hpref : evenLogEntropyPrefix (H + 1) x = evenLogEntropyPrefix H x +
          x ^ (2 * H + 2) / (((H : ℝ) + 1) * (2 * (H : ℝ) + 1)) := by
        exact sum_range_succ _ H
      have d₁ : (2 * (H : ℝ) + 1) ≠ 0 := by positivity
      have d₂ : (2 * (H : ℝ) + 2) ≠ 0 := by positivity
      have d₃ : (2 * (H : ℝ) + 3) ≠ 0 := by positivity
      have d₄ : ((H : ℝ) + 1) ≠ 0 := by positivity
      change -(1 + x) * (∑ i ∈ range (2 * (H + 1) + 1),
          (-x) ^ (i + 1) / ((i : ℝ) + 1)) -
        (1 - x) * (∑ i ∈ range (2 * (H + 1) + 1),
          x ^ (i + 1) / ((i : ℝ) + 1)) = _
      calc
        _ = (-(1 + x) * (∑ i ∈ range (2 * H + 1),
              (-x) ^ (i + 1) / ((i : ℝ) + 1)) -
            (1 - x) * (∑ i ∈ range (2 * H + 1),
              x ^ (i + 1) / ((i : ℝ) + 1))) -
            2 * x ^ (2 * H + 2) / (2 * (H : ℝ) + 2) +
            2 * x ^ (2 * H + 4) / (2 * (H : ℝ) + 3) := by
          rw [hsum (-x), hsum x, hnegEven, hnegOdd, hpowStep]
          ring
        _ = evenLogEntropyPrefix (H + 1) x +
            2 * x ^ (2 * (H + 1) + 2) / (2 * ((H + 1 : ℕ) : ℝ) + 1) := by
          rw [ih, hpref, show 2 * (H + 1) + 2 = 2 * H + 4 by omega]
          simp only [Nat.cast_add, Nat.cast_one]
          rw [show 2 * ((H : ℝ) + 1) + 1 = 2 * (H : ℝ) + 3 by ring]
          field_simp [d₁, d₂, d₃, d₄]
          <;> ring

theorem evenLogEntropy_remainder_bound (H : ℕ) (x : ℝ) (hx : |x| ≤ 1 / 2) :
    |evenLogEntropy x - evenLogEntropyPrefix H x| ≤ 8 * |x| ^ (2 * H + 2) := by
  have hxlt : |x| < 1 := by linarith
  have hm : |-x| < 1 := by simpa only [abs_neg] using hxlt
  have hxlo := (abs_le.mp hx).1
  have hxhi := (abs_le.mp hx).2
  have hpluspos : 0 < 1 + x := by linarith
  have hminuspos : 0 < 1 - x := by linarith
  have hd : 0 < 1 - |x| := by linarith
  have hpow : 0 ≤ |x| ^ (2 * H + 2) := pow_nonneg (abs_nonneg x) _
  let Sm := ∑ i ∈ range (2 * H + 1), (-x) ^ (i + 1) / ((i : ℝ) + 1)
  let Sp := ∑ i ∈ range (2 * H + 1), x ^ (i + 1) / ((i : ℝ) + 1)
  have hp : |Sp + Real.log (1 - x)| ≤ |x| ^ (2 * H + 2) / (1 - |x|) := by
    simpa only [Sp, show 2 * H + 1 + 1 = 2 * H + 2 by omega] using
      Real.abs_log_sub_add_sum_range_le hxlt (2 * H + 1)
  have hn : |Sm + Real.log (1 + x)| ≤ |x| ^ (2 * H + 2) / (1 - |x|) := by
    simpa only [Sm, abs_neg, sub_neg_eq_add,
      show 2 * H + 1 + 1 = 2 * H + 2 by omega] using
      Real.abs_log_sub_add_sum_range_le hm (2 * H + 1)
  have hb : |x| ^ (2 * H + 2) / (1 - |x|) ≤ 2 * |x| ^ (2 * H + 2) := by
    apply (div_le_iff₀ hd).2
    nlinarith only [mul_le_mul_of_nonneg_left hx hpow]
  have he : 0 < 2 * (H : ℝ) + 1 := by positivity
  have hboundary : |2 * x ^ (2 * H + 2) / (2 * (H : ℝ) + 1)| ≤
      2 * |x| ^ (2 * H + 2) := by
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_pow, abs_of_pos he]
    apply (div_le_iff₀ he).2
    nlinarith only [mul_nonneg (Nat.cast_nonneg H : (0 : ℝ) ≤ H) hpow]
  have hf := evenLogEntropy_finite_identity H x
  change -(1 + x) * Sm - (1 - x) * Sp =
    evenLogEntropyPrefix H x + 2 * x ^ (2 * H + 2) / (2 * (H : ℝ) + 1) at hf
  have hid : evenLogEntropy x - evenLogEntropyPrefix H x =
      (1 + x) * (Sm + Real.log (1 + x)) + (1 - x) * (Sp + Real.log (1 - x)) +
        2 * x ^ (2 * H + 2) / (2 * (H : ℝ) + 1) := by
    unfold evenLogEntropy
    nlinarith only [hf]
  rw [hid]
  calc
    _ ≤ |(1 + x) * (Sm + Real.log (1 + x))| +
          |(1 - x) * (Sp + Real.log (1 - x))| +
          |2 * x ^ (2 * H + 2) / (2 * (H : ℝ) + 1)| := by
      exact (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)
    _ ≤ (1 + x) * (|x| ^ (2 * H + 2) / (1 - |x|)) +
          (1 - x) * (|x| ^ (2 * H + 2) / (1 - |x|)) +
          2 * |x| ^ (2 * H + 2) := by
      rw [abs_mul, abs_mul, abs_of_pos hpluspos, abs_of_pos hminuspos]
      exact add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left hn hpluspos.le)
          (mul_le_mul_of_nonneg_left hp hminuspos.le)) hboundary
    _ = 2 * (|x| ^ (2 * H + 2) / (1 - |x|)) + 2 * |x| ^ (2 * H + 2) := by ring
    _ ≤ 8 * |x| ^ (2 * H + 2) := by nlinarith only [hb, hpow]

end Hardinian
