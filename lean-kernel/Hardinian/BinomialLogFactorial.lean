import Hardinian.StirlingCumulativePowers
import Hardinian.LogWindowRelative
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Hardinian

noncomputable def binomialLogBulk (N m j : ℕ) : ℝ :=
  ((m : ℝ) + 1 / 2) * Real.log (m : ℝ)
    - ((j : ℝ) + 1 / 2) * Real.log (j : ℝ)
    - (((m - j : ℕ) : ℝ) + 1 / 2) * Real.log ((m - j : ℕ) : ℝ)
    - (m : ℝ) * Real.log 2 + Real.log ((N : ℝ) / 2) / 2

theorem binomialMass_pos_of_le (m j : ℕ) (hj : j ≤ m) :
    0 < binomialMass m j := by
  unfold binomialMass
  exact div_pos (by exact_mod_cast Nat.choose_pos hj) (by positivity)

theorem logFactorial_correction_decomposition (m : ℕ) (hm : 1 ≤ m) :
    Real.log (m.factorial : ℝ) = logFactorialCorrection m +
      ((m : ℝ) + 1 / 2) * Real.log (m : ℝ) - (m : ℝ) + Real.log (2 * Real.pi) / 2 := by
  unfold logFactorialCorrection
  ring

theorem binomialMass_log_factorial (m j : ℕ) (hj : j ≤ m) :
    Real.log (binomialMass m j) =
      Real.log (m.factorial : ℝ) - Real.log (j.factorial : ℝ) -
        Real.log ((m - j).factorial : ℝ) - (m : ℝ) * Real.log 2 := by
  have hf (n : ℕ) : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have ht : (2 : ℝ) ≠ 0 := by norm_num
  unfold binomialMass
  rw [Nat.cast_choose ℝ hj,
    Real.log_div (div_ne_zero (hf m) (mul_ne_zero (hf j) (hf (m - j)))) (pow_ne_zero m ht),
    Real.log_div (hf m) (mul_ne_zero (hf j) (hf (m - j))),
    Real.log_mul (hf j) (hf (m - j)), Real.log_pow]
  ring

theorem normalizedBinomialLog_factorial (N m j : ℕ)
    (hN : 1 ≤ N) (hj : 1 ≤ j) (hjm : j < m) :
    Real.log (Real.sqrt (Real.pi * (N : ℝ)) * binomialMass m j) =
      binomialLogBulk N m j + logFactorialCorrection m -
        logFactorialCorrection j - logFactorialCorrection (m - j) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hm : 1 ≤ m := by omega
  have hq : 1 ≤ m - j := by omega
  have ht : (2 : ℝ) ≠ 0 := by norm_num
  rw [Real.log_mul (by positivity : Real.sqrt (Real.pi * (N : ℝ)) ≠ 0)
      (ne_of_gt (binomialMass_pos_of_le m j hjm.le)),
    Real.log_sqrt (by positivity), binomialMass_log_factorial m j hjm.le,
    logFactorial_correction_decomposition m hm,
    logFactorial_correction_decomposition j hj,
    logFactorial_correction_decomposition (m - j) hq]
  unfold binomialLogBulk
  simp only [Real.log_mul Real.pi_ne_zero hn.ne', Real.log_mul ht Real.pi_ne_zero,
    Real.log_div hn.ne' ht, Nat.cast_sub hjm.le]
  ring

theorem normalizedBinomialLog_prefix_error (N m j J : ℕ)
    (hN : 1 ≤ N) (hj : 1 ≤ j) (hjm : j < m) :
    |Real.log (Real.sqrt (Real.pi * (N : ℝ)) * binomialMass m j) -
        (binomialLogBulk N m j + stirlingCorrectionPrefix m J -
          stirlingCorrectionPrefix j J - stirlingCorrectionPrefix (m - j) J)| ≤
      2 * (stirlingResidualConstant J : ℝ) *
        (1 / (m : ℝ) ^ (J + 1) + 1 / (j : ℝ) ^ (J + 1) +
          1 / (((m - j : ℕ) : ℝ) ^ (J + 1))) := by
  have hm : 1 ≤ m := by omega
  have hq : 1 ≤ m - j := by omega
  have h1 := logFactorialCorrection_inversePower_error m J hm
  have h2 := logFactorialCorrection_inversePower_error j J hj
  have h3 := logFactorialCorrection_inversePower_error (m - j) J hq
  rw [normalizedBinomialLog_factorial N m j hN hj hjm]
  let R1 := logFactorialCorrection m - stirlingCorrectionPrefix m J
  let R2 := logFactorialCorrection j - stirlingCorrectionPrefix j J
  let R3 := logFactorialCorrection (m - j) - stirlingCorrectionPrefix (m - j) J
  have he : (binomialLogBulk N m j + logFactorialCorrection m -
      logFactorialCorrection j - logFactorialCorrection (m - j)) -
      (binomialLogBulk N m j + stirlingCorrectionPrefix m J -
        stirlingCorrectionPrefix j J - stirlingCorrectionPrefix (m - j) J) = R1 - R2 - R3 := by
    dsimp [R1, R2, R3]
    ring
  rw [he]
  calc
    _ ≤ |R1 - R2| + |R3| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add (R1 - R2) (-R3)
    _ ≤ |R1| + |R2| + |R3| := add_le_add_right (by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add R1 (-R2)) _
    _ ≤ 2 * (stirlingResidualConstant J : ℝ) / (m : ℝ) ^ (J + 1) +
        2 * (stirlingResidualConstant J : ℝ) / (j : ℝ) ^ (J + 1) +
        2 * (stirlingResidualConstant J : ℝ) / (((m - j : ℕ) : ℝ) ^ (J + 1)) :=
      add_le_add (add_le_add h1 h2) h3
    _ = _ := by ring

theorem binomialLog_window_geometry (N L a b j : ℕ)
    (hN : 4 ≤ N) (hba : b < a) (haL : a ≤ L)
    (hhalf : 2 * (L : ℝ) < (N : ℝ))
    (hj : j ∈ Finset.Ico (N - a) (N - b)) :
    let m := (N - a) + (N - b)
    a ≤ N ∧ b ≤ N ∧ N ≤ m ∧ m ≤ 2 * N ∧ 1 ≤ j ∧ j < m ∧
      (m : ℝ) = 2 * (N : ℝ) - (a : ℝ) - (b : ℝ) ∧
      ((m - j : ℕ) : ℝ) = (m : ℝ) - (j : ℝ) ∧
      (N : ℝ) / 2 ≤ (j : ℝ) ∧ (N : ℝ) / 2 ≤ ((m - j : ℕ) : ℝ) := by
  have h2L : 2 * L < N := by exact_mod_cast hhalf
  have hju := (Finset.mem_Ico.mp hj).1
  have hjv := (Finset.mem_Ico.mp hj).2
  let m := (N - a) + (N - b)
  have ha : a ≤ N := by omega
  have hb : b ≤ N := by omega
  have hmlo : N ≤ m := by dsimp [m]; omega
  have hmhi : m ≤ 2 * N := by dsimp [m]; omega
  have hjpos : 1 ≤ j := by omega
  have hjm : j < m := by dsimp [m]; omega
  have hmcast : (m : ℝ) = 2 * (N : ℝ) - (a : ℝ) - (b : ℝ) := by
    dsimp [m]
    rw [Nat.cast_add, Nat.cast_sub ha, Nat.cast_sub hb]
    ring
  have hqcast : ((m - j : ℕ) : ℝ) = (m : ℝ) - (j : ℝ) := Nat.cast_sub hjm.le
  have hjtwo : N ≤ 2 * j := by omega
  have hqtwo : N ≤ 2 * (m - j) := by dsimp [m]; omega
  have hjtwoR : (N : ℝ) ≤ 2 * (j : ℝ) := by exact_mod_cast hjtwo
  have hqtwoR : (N : ℝ) ≤ 2 * ((m - j : ℕ) : ℝ) := by exact_mod_cast hqtwo
  exact ⟨ha, hb, hmlo, hmhi, hjpos, hjm, hmcast, hqcast, by linarith, by linarith⟩

/-- The actual Ico point has a real signed center; no even-grid assumption is made. -/
theorem binomialLog_window_center (N a b j : ℕ) (hba : b < a) (ha : a ≤ N)
    (hj : j ∈ Finset.Ico (N - a) (N - b)) :
    j - (N - a) < a - b ∧
      (j : ℝ) - ((((N - a) + (N - b) : ℕ) : ℝ) / 2) =
        ((j - (N - a) : ℕ) : ℝ) - ((a - b : ℕ) : ℝ) / 2 := by
  have hb : b ≤ N := by omega
  have hju := (Finset.mem_Ico.mp hj).1
  have hjv := (Finset.mem_Ico.mp hj).2
  refine ⟨by omega, ?_⟩
  rw [Nat.cast_add, Nat.cast_sub ha, Nat.cast_sub hb, Nat.cast_sub hju,
    Nat.cast_sub ha, Nat.cast_sub hba.le]
  ring

theorem binomialLog_reciprocal_window_bound (N q J : ℕ) (hN : 1 ≤ N)
    (hq : (N : ℝ) / 2 ≤ (q : ℝ)) :
    (1 / (q : ℝ) ^ (J + 1) : ℝ) ≤ (2 : ℝ) ^ (J + 1) / (N : ℝ) ^ (J + 1) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ 1 / (((N : ℝ) / 2) ^ (J + 1)) :=
      one_div_le_one_div_of_le (pow_pos (by positivity) _)
        (pow_le_pow_left₀ (by positivity) hq (J + 1))
    _ = _ := by
      simp only [div_pow, one_div, div_eq_mul_inv, mul_inv_rev, inv_inv]
      ring

theorem uniform_normalizedBinomialLog_prefix_window (C : ℝ) (hC : 0 < C) :
    ∃ N0 : ℕ, 4 ≤ N0 ∧ ∀ N ≥ N0, ∀ L a b j J : ℕ,
      b < a → a ≤ L → (L : ℝ) ≤ C * Real.log (N : ℝ) →
      j ∈ Finset.Ico (N - a) (N - b) →
      let m := (N - a) + (N - b)
      1 ≤ j ∧ j < m ∧
      |Real.log (Real.sqrt (Real.pi * (N : ℝ)) * binomialMass m j) -
          (binomialLogBulk N m j + stirlingCorrectionPrefix m J -
            stirlingCorrectionPrefix j J - stirlingCorrectionPrefix (m - j) J)| ≤
        (6 * (2 : ℝ) ^ (J + 1) * (stirlingResidualConstant J : ℝ)) /
          (N : ℝ) ^ (J + 1) := by
  obtain ⟨M, hM2, hM⟩ := logWindow_eventually_below_half C
  refine ⟨max 4 M, le_max_left _ _, ?_⟩
  intro N hN L a b j J hba haL hlog hj
  have hN4 : 4 ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : 1 ≤ N := by omega
  have hhalf0 := hM N (le_trans (le_max_right _ _) hN)
  have hhalf : 2 * (L : ℝ) < (N : ℝ) := by linarith
  let m := (N - a) + (N - b)
  have hg := binomialLog_window_geometry N L a b j hN4 hba haL hhalf hj
  rcases hg with ⟨ha, hb, hmlo, hmhi, hjpos, hjm, hmcast, hqcast, hjhalf, hqhalf⟩
  change 1 ≤ j ∧ j < m ∧ _
  refine ⟨hjpos, hjm, ?_⟩
  have hmhalf : (N : ℝ) / 2 ≤ (m : ℝ) := by
    have hnm : (N : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmlo
    linarith [Nat.cast_nonneg (α := ℝ) N]
  have h1 := binomialLog_reciprocal_window_bound N m J hN1 hmhalf
  have h2 := binomialLog_reciprocal_window_bound N j J hN1 hjhalf
  have h3 := binomialLog_reciprocal_window_bound N (m - j) J hN1 hqhalf
  have hconst : (0 : ℝ) ≤ 2 * (stirlingResidualConstant J : ℝ) := by
    have hc : (0 : ℝ) ≤ (stirlingResidualConstant J : ℝ) := by
      exact_mod_cast stirlingResidualConstant_nonneg J
    positivity
  calc
    _ ≤ 2 * (stirlingResidualConstant J : ℝ) *
        (1 / (m : ℝ) ^ (J + 1) + 1 / (j : ℝ) ^ (J + 1) +
          1 / (((m - j : ℕ) : ℝ) ^ (J + 1))) :=
      normalizedBinomialLog_prefix_error N m j J hN1 hjpos hjm
    _ ≤ 2 * (stirlingResidualConstant J : ℝ) *
        ((2 : ℝ) ^ (J + 1) / (N : ℝ) ^ (J + 1) +
          (2 : ℝ) ^ (J + 1) / (N : ℝ) ^ (J + 1) +
          (2 : ℝ) ^ (J + 1) / (N : ℝ) ^ (J + 1)) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add h1 h2) h3) hconst
    _ = _ := by ring

end Hardinian
