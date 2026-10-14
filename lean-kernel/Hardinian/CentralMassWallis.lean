import Hardinian.BinomialMass
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Tactic.FieldSimp

namespace Hardinian

theorem centralMass_even (n : ℕ) :
    centralMass (2 * n) = ((2 * n).choose n : ℝ) / 2 ^ (2 * n) := by
  have hh : 2 * n / 2 = n := by omega
  simp only [centralMass, binomialMass, hh]

theorem centralMass_odd (n : ℕ) :
    centralMass (2 * n + 1) =
      centralMass (2 * n) * ((2 * (n : ℝ) + 1) / (2 * n + 2)) := by
  have he : 2 * n / 2 = n := by omega
  have ho : (2 * n + 1) / 2 = n := by omega
  have hs : 2 * n + 1 - n = n + 1 := by omega
  have hn := Nat.choose_mul_succ_eq (2 * n) n
  rw [hs] at hn
  have hc : ((2 * n).choose n : ℝ) * (2 * (n : ℝ) + 1) =
      ((2 * n + 1).choose n : ℝ) * ((n : ℝ) + 1) := by exact_mod_cast hn
  have hp : (2 : ℝ) ^ (2 * n) ≠ 0 := by positivity
  have hd : 2 * (n : ℝ) + 2 ≠ 0 := by positivity
  simp only [centralMass, binomialMass, he, ho, pow_add, pow_one]
  field_simp [hp, hd]
  nlinarith only [congrArg (fun x : ℝ => x * ((2 : ℝ) ^ (2 * n) * 2)) hc]

theorem centralMass_wallis_identity (n : ℕ) :
    centralMass (2 * n) ^ 2 * (2 * (n : ℝ) + 1) * Real.Wallis.W n = 1 := by
  have hn := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
  have hs : 2 * n - n = n := by omega
  rw [hs] at hn
  have hc : ((2 * n).choose n : ℝ) * (n.factorial : ℝ) * (n.factorial : ℝ) =
      ((2 * n).factorial : ℝ) := by exact_mod_cast hn
  have hpow : (2 : ℝ) ^ (4 * n) = ((2 : ℝ) ^ (2 * n)) ^ 2 := by
    rw [← pow_mul]
    congr 1
    omega
  have hp : (2 : ℝ) ^ (2 * n) ≠ 0 := by positivity
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  have hchoose : ((2 * n).choose n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (show n ≤ 2 * n by omega)))
  have hd : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
  rw [centralMass_even, Real.Wallis.W_eq_factorial_ratio, hpow, ← hc]
  field_simp [hp, hf, hchoose, hd] <;> ring

theorem centralMass_even_square (n : ℕ) :
    Real.pi * (n : ℝ) * centralMass (2 * n) ^ 2 =
      (Real.pi * ((n : ℝ) / (2 * n + 1))) / Real.Wallis.W n := by
  have hw : Real.Wallis.W n ≠ 0 := ne_of_gt (Real.Wallis.W_pos n)
  have hd : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
  apply (eq_div_iff hw).2
  calc
    Real.pi * (n : ℝ) * centralMass (2 * n) ^ 2 * Real.Wallis.W n =
        (Real.pi * ((n : ℝ) / (2 * n + 1))) *
          (centralMass (2 * n) ^ 2 * (2 * n + 1) * Real.Wallis.W n) := by
            field_simp [hd] <;> ring
    _ = _ := by rw [centralMass_wallis_identity]; ring

theorem centralMass_odd_square (n : ℕ) :
    Real.pi * (2 * (n : ℝ) + 1) / 2 * centralMass (2 * n + 1) ^ 2 =
      ((Real.pi / 2) * ((2 * (n : ℝ) + 1) / (2 * n + 2)) ^ 2) /
        Real.Wallis.W n := by
  have hw : Real.Wallis.W n ≠ 0 := ne_of_gt (Real.Wallis.W_pos n)
  rw [centralMass_odd]
  apply (eq_div_iff hw).2
  calc
    Real.pi * (2 * (n : ℝ) + 1) / 2 *
        (centralMass (2 * n) * ((2 * (n : ℝ) + 1) / (2 * n + 2))) ^ 2 *
        Real.Wallis.W n =
      ((Real.pi / 2) * ((2 * (n : ℝ) + 1) / (2 * n + 2)) ^ 2) *
        (centralMass (2 * n) ^ 2 * (2 * n + 1) * Real.Wallis.W n) := by ring
    _ = _ := by rw [centralMass_wallis_identity]; ring

end Hardinian
