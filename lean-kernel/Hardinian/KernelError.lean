import Hardinian.BinomialMass

namespace Hardinian

/-- A uniform bound on the right half, proved from exact adjacent mass ratios. -/
theorem right_deficit_scaled (m d : ℕ) (hd : m / 2 + d ≤ m) :
    (m : ℝ) * (1 - relativeMass m (m / 2 + d)) ≤ 2 * (d : ℝ) ^ 2 := by
  revert hd
  induction d with
  | zero => intro hd; simp [relativeMass_center]
  | succ d ih =>
      intro hd
      have hd' : m / 2 + d ≤ m := by omega
      have hi := ih hd'
      have hstep := relativeMass_step m (m / 2 + d) hd'
      simp only [Nat.cast_add] at hstep
      have hh0 : 2 * (m / 2) ≤ m := by omega
      have hh1 : m ≤ 2 * (m / 2) + 1 := by omega
      have hh0r : 2 * ((m / 2 : ℕ) : ℝ) ≤ m := by exact_mod_cast hh0
      have hh1r : (m : ℝ) ≤ 2 * ((m / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hh1
      have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      have hh0' : (0 : ℝ) ≤ ((m / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
      let x := relativeMass m (m / 2 + d)
      let y := relativeMass m (m / 2 + (d + 1))
      let u : ℝ := ((m / 2 : ℕ) : ℝ) + d + 1
      let delta : ℝ := 2 * (((m / 2 : ℕ) : ℝ) + d) + 1 - m
      have hx0 : 0 ≤ x := relativeMass_nonneg _ _
      have hx1 : x ≤ 1 := relativeMass_le_one _ _
      have hu : 0 < u := by dsimp [u]; positivity
      have hdelta0 : 0 ≤ delta := by dsimp [delta]; linarith
      have hdeltaup : delta ≤ 2 * (d : ℝ) + 1 := by dsimp [delta]; linarith
      have hm : (m : ℝ) ≤ 2 * u := by dsimp [u]; linarith
      have hid : (x - y) * u = x * delta := by
        dsimp [x, y, u, delta]
        simp only [Nat.add_assoc] at hstep
        nlinarith [hstep]
      have hdiff0 : 0 ≤ x - y := by
        have hp := mul_nonneg hx0 hdelta0
        rw [← hid] at hp
        nlinarith
      have hmul := mul_le_mul_of_nonneg_left hm hdiff0
      have hxdelta : x * delta ≤ delta := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hx1) hdelta0]
      have hdiff : (x - y) * (m : ℝ) ≤ 4 * (d : ℝ) + 2 := by
        nlinarith [hid, hmul, hxdelta]
      change (m : ℝ) * (1 - x) ≤ 2 * (d : ℝ) ^ 2 at hi
      change (m : ℝ) * (1 - y) ≤ 2 * ((d + 1 : ℕ) : ℝ) ^ 2
      push_cast
      nlinarith [hi, hdiff]

/-- Both tails and both parities, with distance measured from the lower center. -/
theorem deficit_scaled (m j : ℕ) (hj : j ≤ m) :
    (m : ℝ) * (1 - relativeMass m j) ≤
      2 * (|(j : ℝ) - ((m / 2 : ℕ) : ℝ)| + 1) ^ 2 := by
  by_cases hc : m / 2 ≤ j
  · have heq : m / 2 + (j - m / 2) = j := by omega
    have hb := right_deficit_scaled m (j - m / 2) (by omega)
    rw [heq] at hb
    have hd : ((j - m / 2 : ℕ) : ℝ) = (j : ℝ) - ((m / 2 : ℕ) : ℝ) :=
      Nat.cast_sub hc
    rw [← hd, abs_of_nonneg (Nat.cast_nonneg _)]
    nlinarith [hb, Nat.cast_nonneg (α := ℝ) (j - m / 2)]
  · have heq : m / 2 + (m - j - m / 2) = m - j := by omega
    have hb := right_deficit_scaled m (m - j - m / 2) (by omega)
    rw [heq, relativeMass_symm m j hj] at hb
    have hd : ((m / 2 - j : ℕ) : ℝ) = ((m / 2 : ℕ) : ℝ) - (j : ℝ) :=
      Nat.cast_sub (by omega)
    have hle : m - j - m / 2 ≤ m / 2 - j + 1 := by omega
    have hler : ((m - j - m / 2 : ℕ) : ℝ) ≤ ((m / 2 - j : ℕ) : ℝ) + 1 := by
      exact_mod_cast hle
    rw [abs_sub_comm, ← hd, abs_of_nonneg (Nat.cast_nonneg _)]
    nlinarith [hb, Nat.cast_nonneg (α := ℝ) (m - j - m / 2),
      Nat.cast_nonneg (α := ℝ) (m / 2 - j)]

theorem binomial_relative_error (m j : ℕ) (hm : 1 ≤ m) (hj : j ≤ m) :
    0 ≤ 1 - binomialMass m j / centralMass m ∧
      1 - binomialMass m j / centralMass m ≤
        2 * (|(j : ℝ) - ((m / 2 : ℕ) : ℝ)| + 1) ^ 2 / (m : ℝ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  constructor
  · exact sub_nonneg.mpr (relativeMass_le_one m j)
  · apply (le_div_iff₀ hm0).2
    simpa only [relativeMass, mul_comm] using deficit_scaled m j hj

end Hardinian
