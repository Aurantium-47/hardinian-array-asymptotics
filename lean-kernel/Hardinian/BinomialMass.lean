import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Hardinian

def binomialMass (m j : ℕ) : ℝ := (m.choose j : ℝ) / 2 ^ m

def centralMass (m : ℕ) : ℝ := binomialMass m (m / 2)

def relativeMass (m j : ℕ) : ℝ := binomialMass m j / centralMass m

theorem centralMass_pos (m : ℕ) : 0 < centralMass m := by
  unfold centralMass binomialMass
  exact div_pos (by exact_mod_cast Nat.choose_pos (Nat.div_le_self m 2)) (by positivity)

theorem relativeMass_eq_choose_ratio (m j : ℕ) :
    relativeMass m j = (m.choose j : ℝ) / (m.choose (m / 2) : ℝ) := by
  unfold relativeMass centralMass binomialMass
  have hpow : (2 : ℝ) ^ m ≠ 0 := by positivity
  exact div_div_div_cancel_right₀ hpow _ _

theorem relativeMass_nonneg (m j : ℕ) : 0 ≤ relativeMass m j := by
  rw [relativeMass_eq_choose_ratio]
  positivity

theorem relativeMass_le_one (m j : ℕ) : relativeMass m j ≤ 1 := by
  rw [relativeMass_eq_choose_ratio]
  have hc : (0 : ℝ) < (m.choose (m / 2) : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.div_le_self m 2)
  apply (div_le_one hc).2
  exact_mod_cast Nat.choose_le_middle j m

theorem relativeMass_center (m : ℕ) : relativeMass m (m / 2) = 1 := by
  exact div_self (ne_of_gt (centralMass_pos m))

theorem relativeMass_symm (m j : ℕ) (hj : j ≤ m) :
    relativeMass m (m - j) = relativeMass m j := by
  simp only [relativeMass_eq_choose_ratio, Nat.choose_symm hj]

theorem relativeMass_step (m k : ℕ) (hk : k ≤ m) :
    relativeMass m (k + 1) * ((k : ℝ) + 1) =
      relativeMass m k * ((m : ℝ) - k) := by
  have h : (m.choose (k + 1) : ℝ) * ((k : ℝ) + 1) =
      (m.choose k : ℝ) * ((m : ℝ) - k) := by
    have hn := congrArg (fun n : ℕ => (n : ℝ)) (Nat.choose_succ_right_eq m k)
    push_cast [Nat.cast_sub hk] at hn
    exact hn
  simp only [relativeMass_eq_choose_ratio]
  calc
    (m.choose (k + 1) : ℝ) / (m.choose (m / 2) : ℝ) * ((k : ℝ) + 1) =
        ((m.choose (k + 1) : ℝ) * ((k : ℝ) + 1)) /
          (m.choose (m / 2) : ℝ) := by ring
    _ = ((m.choose k : ℝ) * ((m : ℝ) - k)) /
          (m.choose (m / 2) : ℝ) := by rw [h]
    _ = _ := by ring

/-- An exact product for the actual relative binomial masses, including odd centers. -/
theorem relativeMass_product (m d : ℕ) (hd : m / 2 + d ≤ m) :
    relativeMass m (m / 2 + d) =
      ∏ i ∈ Finset.range d,
        ((m : ℝ) - ((m / 2 : ℕ) : ℝ) - i) /
          (((m / 2 : ℕ) : ℝ) + i + 1) := by
  revert hd
  induction d with
  | zero => intro hd; simpa using relativeMass_center m
  | succ d ih =>
      intro hd
      have hd' : m / 2 + d ≤ m := by omega
      have hstep := relativeMass_step m (m / 2 + d) hd'
      simp only [Nat.cast_add] at hstep
      rw [Finset.prod_range_succ, ← ih hd']
      rw [← mul_div_assoc]
      have hden : (((m / 2 : ℕ) : ℝ) + (d : ℝ) + 1) ≠ 0 := by positivity
      apply (eq_div_iff hden).2
      simpa only [Nat.add_assoc, Nat.succ_eq_add_one, sub_sub] using hstep

end Hardinian
