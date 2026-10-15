import Hardinian.BinomialLogFactorial
import Hardinian.EvenLogEntropy

namespace Hardinian

theorem binomialEntropy_coordinate_domain (m j : ℕ)
    (hj : 1 ≤ j) (hjm : j < m) :
    let x : ℝ := (2 * (j : ℝ) - (m : ℝ)) / (m : ℝ)
    |x| < 1 ∧ 0 < 1 + x ∧ 0 < 1 - x ∧ 0 < 1 - x ^ 2 ∧
      (j : ℝ) = (m : ℝ) * (1 + x) / 2 ∧
      ((m - j : ℕ) : ℝ) = (m : ℝ) * (1 - x) / 2 := by
  let x : ℝ := (2 * (j : ℝ) - (m : ℝ)) / (m : ℝ)
  have hm2 : 2 ≤ m := by omega
  have hm : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hjr : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hjmr : (j : ℝ) < m := by exact_mod_cast hjm
  have hxlo : -1 < x := by
    dsimp [x]
    apply (lt_div_iff₀ hm).2
    linarith
  have hxhi : x < 1 := by
    dsimp [x]
    apply (div_lt_iff₀ hm).2
    linarith
  have hp : 0 < 1 + x := by linarith
  have hn : 0 < 1 - x := by linarith
  have hsq : 0 < 1 - x ^ 2 := by
    nlinarith only [mul_pos hp hn]
  have heqj : (j : ℝ) = (m : ℝ) * (1 + x) / 2 := by
    dsimp [x]
    field_simp [hm.ne']
    <;> ring
  have heqq : ((m - j : ℕ) : ℝ) = (m : ℝ) * (1 - x) / 2 := by
    rw [Nat.cast_sub hjm.le]
    dsimp [x]
    field_simp [hm.ne']
    <;> ring
  exact ⟨abs_lt.mpr ⟨hxlo, hxhi⟩, hp, hn, hsq, heqj, heqq⟩

theorem binomialLogBulk_entropy (N m j : ℕ)
    (hN : 1 ≤ N) (hj : 1 ≤ j) (hjm : j < m) :
    let x : ℝ := (2 * (j : ℝ) - (m : ℝ)) / (m : ℝ)
    binomialLogBulk N m j =
      -Real.log ((m : ℝ) / (2 * (N : ℝ))) / 2
        - ((m : ℝ) / 2) * evenLogEntropy x - Real.log (1 - x ^ 2) / 2 := by
  let x : ℝ := (2 * (j : ℝ) - (m : ℝ)) / (m : ℝ)
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hm : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hq : 1 ≤ m - j := by omega
  have hqpos : (0 : ℝ) < ((m - j : ℕ) : ℝ) := by exact_mod_cast (show 0 < m - j by omega)
  have ht : (2 : ℝ) ≠ 0 := by norm_num
  obtain ⟨hx, hp, hmns, hsq, heqj, heqq⟩ := binomialEntropy_coordinate_domain m j hj hjm
  have hlogj : Real.log (j : ℝ) = Real.log (m : ℝ) + Real.log (1 + x) - Real.log 2 := by
    rw [heqj, Real.log_div (mul_ne_zero hm.ne' hp.ne') ht, Real.log_mul hm.ne' hp.ne']
  have hlogq : Real.log ((m - j : ℕ) : ℝ) =
      Real.log (m : ℝ) + Real.log (1 - x) - Real.log 2 := by
    rw [heqq, Real.log_div (mul_ne_zero hm.ne' hmns.ne') ht, Real.log_mul hm.ne' hmns.ne']
  have hlogsum : Real.log (1 - x ^ 2) = Real.log (1 + x) + Real.log (1 - x) := by
    rw [← show (1 + x) * (1 - x) = 1 - x ^ 2 by ring, Real.log_mul hp.ne' hmns.ne']
  have hratio : 0 < (m : ℝ) / (2 * (N : ℝ)) := by positivity
  have hlogratio : Real.log ((m : ℝ) / (2 * (N : ℝ))) =
      Real.log (m : ℝ) - Real.log 2 - Real.log (N : ℝ) := by
    rw [Real.log_div hm.ne' (mul_ne_zero ht hn.ne'), Real.log_mul ht hn.ne']
    ring
  have hlogNhalf : Real.log ((N : ℝ) / 2) = Real.log (N : ℝ) - Real.log 2 :=
    Real.log_div hn.ne' ht
  change binomialLogBulk N m j = -Real.log ((m : ℝ) / (2 * (N : ℝ))) / 2 -
    ((m : ℝ) / 2) * evenLogEntropy x - Real.log (1 - x ^ 2) / 2
  unfold binomialLogBulk evenLogEntropy
  rw [hlogj, hlogq, hlogratio, hlogNhalf, hlogsum, heqj, heqq]
  ring

theorem normalizedBinomialLog_entropy (N m j : ℕ)
    (hN : 1 ≤ N) (hj : 1 ≤ j) (hjm : j < m) :
    let x : ℝ := (2 * (j : ℝ) - (m : ℝ)) / (m : ℝ)
    Real.log (Real.sqrt (Real.pi * (N : ℝ)) * binomialMass m j) =
      -Real.log ((m : ℝ) / (2 * (N : ℝ))) / 2
        - ((m : ℝ) / 2) * evenLogEntropy x - Real.log (1 - x ^ 2) / 2
        + logFactorialCorrection m - logFactorialCorrection j -
        logFactorialCorrection (m - j) := by
  dsimp only
  rw [normalizedBinomialLog_factorial N m j hN hj hjm, binomialLogBulk_entropy N m j hN hj hjm]

theorem uniform_binomial_entropy_coordinates (C : ℝ) (hC : 0 < C) :
    ∃ N0 : ℕ, 4 ≤ N0 ∧ ∀ N ≥ N0, ∀ L a b j : ℕ,
      b < a → a ≤ L → (L : ℝ) ≤ C * Real.log (N : ℝ) →
      j ∈ Finset.Ico (N - a) (N - b) →
      let m := (N - a) + (N - b)
      let x : ℝ := (2 * (j : ℝ) - (m : ℝ)) / (m : ℝ)
      let y : ℝ := ((a : ℝ) + (b : ℝ)) / (2 * (N : ℝ))
      (m : ℝ) / (2 * (N : ℝ)) = 1 - y ∧
        0 ≤ y ∧ y ≤ (L : ℝ) / (N : ℝ) ∧
        |x| ≤ (L : ℝ) / (N : ℝ) ∧ (L : ℝ) / (N : ℝ) < 1 / 2 := by
  obtain ⟨M, hM2, hM⟩ := logWindow_eventually_below_half C
  refine ⟨max 4 M, le_max_left _ _, ?_⟩
  intro N hN L a b j hba haL hlog hj
  have hN4 : 4 ≤ N := le_trans (le_max_left _ _) hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hhalf0 := hM N (le_trans (le_max_right _ _) hN)
  have hhalf : 2 * (L : ℝ) < (N : ℝ) := by linarith
  let m := (N - a) + (N - b)
  have hg := binomialLog_window_geometry N L a b j hN4 hba haL hhalf hj
  obtain ⟨ha, hb, hmlo, hmhi, hjpos, hjm, hmcast, hqcast, hjhalf, hqhalf⟩ := hg
  have hnm : (N : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmlo
  have hm : (0 : ℝ) < m := lt_of_lt_of_le hn hnm
  have hc := binomialLog_window_center N a b j hba ha hj
  let d := a - b
  let v := j - (N - a)
  have hvd : (v : ℝ) < (d : ℝ) := by exact_mod_cast hc.1
  have hv : (0 : ℝ) ≤ v := Nat.cast_nonneg _
  have hdL : (d : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast (le_trans (Nat.sub_le a b) haL)
  have hcenter : 2 * (j : ℝ) - (m : ℝ) = 2 * (v : ℝ) - (d : ℝ) := by
    nlinarith only [hc.2]
  have hz : |2 * (j : ℝ) - (m : ℝ)| ≤ (L : ℝ) := by
    rw [hcenter]
    exact abs_le.mpr ⟨by linarith only [hv, hdL], by linarith only [hvd, hdL]⟩
  have habL : (a : ℝ) + (b : ℝ) ≤ 2 * (L : ℝ) := by
    exact_mod_cast (show a + b ≤ 2 * L by omega)
  change (m : ℝ) / (2 * (N : ℝ)) = 1 - ((a : ℝ) + (b : ℝ)) / (2 * (N : ℝ)) ∧ _
  refine ⟨?_, by positivity, ?_, ?_, ?_⟩
  · rw [hmcast]
    field_simp [hn.ne']
    <;> ring
  · apply (div_le_div_iff₀ (by positivity : 0 < 2 * (N : ℝ)) hn).2
    nlinarith only [mul_le_mul_of_nonneg_right habL hn.le]
  · rw [abs_div, abs_of_pos hm]
    apply (div_le_div_iff₀ hm hn).2
    exact le_trans (mul_le_mul_of_nonneg_right hz hn.le)
      (mul_le_mul_of_nonneg_left hnm (Nat.cast_nonneg L))
  · apply (div_lt_iff₀ hn).2
    linarith only [hhalf]

end Hardinian
