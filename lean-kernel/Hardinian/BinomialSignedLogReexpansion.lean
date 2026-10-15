import Hardinian.BinomialLogFactorial
import Hardinian.SignedInversePowerShift

namespace Hardinian

open Finset

noncomputable def shiftedReciprocalPrefix (K r : ℕ) (A h : ℝ) : ℝ :=
  (1 / A ^ r) * negativeBinomialPrefix (r - 1) (K - r) (h / A)

theorem shiftedReciprocalPrefix_remainder (K r : ℕ) (A h : ℝ)
    (hr : 1 ≤ r) (hrK : r ≤ K) (hA : 0 < A) (hh : |h| ≤ A / 2) :
    |1 / (A + h) ^ r - shiftedReciprocalPrefix K r A h| ≤
      (2 : ℝ) ^ (2 * r - 1) * (Nat.choose K (r - 1) : ℝ) *
        |h| ^ (K - r + 1) / A ^ (K + 1) := by
  simpa only [shiftedReciprocalPrefix,
    show r - 1 + 1 = r by omega,
    show 2 * (r - 1) + 1 = 2 * r - 1 by omega,
    show (K - r) + (r - 1) + 1 = K by omega,
    show (r - 1) + (K - r) + 2 = K + 1 by omega] using
      shiftedInversePower_remainder_bound (r - 1) (K - r) A h hA hh

theorem shiftedReciprocalPrefix_scale (K r : ℕ) (A h : ℝ)
    (hr : 1 ≤ r) (hA : 0 < A) :
    shiftedReciprocalPrefix K r A h =
      ∑ i ∈ range (K - r + 1),
        (-1 : ℝ) ^ i * (Nat.choose (r - 1 + i) i : ℝ) * h ^ i / A ^ (r + i) := by
  calc
    _ = ∑ i ∈ range (K - r + 1),
        (-1 : ℝ) ^ i * (Nat.choose (r - 1 + i) i : ℝ) * h ^ i /
          A ^ (r - 1 + i + 1) := by
      simpa only [shiftedReciprocalPrefix, show r - 1 + 1 = r by omega] using
        negativeBinomialPrefix_signed_scale (r - 1) (K - r) A h hA
    _ = _ := by
      apply sum_congr rfl
      intro i hi
      rw [show r - 1 + i + 1 = r + i by omega]

theorem shiftedReciprocalPrefix_small_shift_bound (K r : ℕ) (N L h : ℝ)
    (hr : 1 ≤ r) (hrK : r ≤ K) (hN : 0 < N)
    (hLhalf : L ≤ N / 2) (hh : |h| ≤ L) :
    |1 / (N + h) ^ r - shiftedReciprocalPrefix K r N h| ≤
      (2 : ℝ) ^ (2 * r - 1) * (Nat.choose K (r - 1) : ℝ) *
        L ^ (K - r + 1) / N ^ (K + 1) := by
  calc
    _ ≤ (2 : ℝ) ^ (2 * r - 1) * (Nat.choose K (r - 1) : ℝ) *
        |h| ^ (K - r + 1) / N ^ (K + 1) :=
      shiftedReciprocalPrefix_remainder K r N h hr hrK hN (hh.trans hLhalf)
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg h) hh _) (by positivity))
      (by positivity)

theorem shiftedReciprocalPrefix_doubled_shift_bound (K r : ℕ) (N L s : ℝ)
    (hr : 1 ≤ r) (hrK : r ≤ K) (hN : 0 < N)
    (hhalf : 2 * L ≤ N) (hs0 : 0 ≤ s) (hsL : s ≤ 2 * L) :
    |1 / (2 * N - s) ^ r - shiftedReciprocalPrefix K r (2 * N) (-s)| ≤
      (2 : ℝ) ^ (r - 1) * (Nat.choose K (r - 1) : ℝ) *
        L ^ (K - r + 1) / N ^ (K + 1) := by
  have hdomain : |-s| ≤ (2 * N) / 2 := by
    rw [abs_neg, abs_of_nonneg hs0]
    linarith
  have hb := shiftedReciprocalPrefix_remainder K r (2 * N) (-s) hr hrK
    (by positivity) hdomain
  rw [abs_neg, abs_of_nonneg hs0] at hb
  have hp : (2 : ℝ) ^ (2 * r - 1) * 2 ^ (K - r + 1) =
      (2 : ℝ) ^ (r - 1) * 2 ^ (K + 1) := by
    rw [← pow_add, ← pow_add,
      show (2 * r - 1) + (K - r + 1) = (r - 1) + (K + 1) by omega]
  calc
    _ ≤ (2 : ℝ) ^ (2 * r - 1) * (Nat.choose K (r - 1) : ℝ) *
        s ^ (K - r + 1) / (2 * N) ^ (K + 1) := by
      simpa only [sub_eq_add_neg] using hb
    _ ≤ (2 : ℝ) ^ (2 * r - 1) * (Nat.choose K (r - 1) : ℝ) *
        (2 * L) ^ (K - r + 1) / (2 * N) ^ (K + 1) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs0 hsL _) (by positivity)) (by positivity)
    _ = ((2 : ℝ) ^ (2 * r - 1) * 2 ^ (K - r + 1)) *
        (Nat.choose K (r - 1) : ℝ) * L ^ (K - r + 1) /
          (2 ^ (K + 1) * N ^ (K + 1)) := by
      rw [mul_pow, mul_pow]
      ring
    _ = _ := by
      rw [hp]
      field_simp [hN.ne']
      <;> ring

theorem binomialSharpShift_geometry (N L a b j : ℕ)
    (hN : 4 ≤ N) (hba : b < a) (haL : a ≤ L)
    (hhalf : 2 * (L : ℝ) < (N : ℝ)) (hj : j ∈ Ico (N - a) (N - b)) :
    let m := (N - a) + (N - b)
    let q := m - j
    let s : ℝ := (a : ℝ) + (b : ℝ)
    let t : ℝ := (j : ℝ) - (m : ℝ) / 2
    a ≤ N ∧ b ≤ N ∧ 1 ≤ j ∧ j < m ∧ 1 ≤ q ∧ N - a < q ∧ q ≤ N - b ∧
      (m : ℝ) = 2 * (N : ℝ) - s ∧
      (j : ℝ) = (N : ℝ) + (t - s / 2) ∧
      (q : ℝ) = (N : ℝ) + (-t - s / 2) ∧
      0 ≤ s ∧ s ≤ 2 * (L : ℝ) ∧ |t| ≤ (L : ℝ) / 2 ∧
      |(j : ℝ) - (N : ℝ)| ≤ (L : ℝ) ∧ |(q : ℝ) - (N : ℝ)| ≤ (L : ℝ) := by
  let m := (N - a) + (N - b)
  let q := m - j
  let s : ℝ := (a : ℝ) + (b : ℝ)
  let t : ℝ := (j : ℝ) - (m : ℝ) / 2
  obtain ⟨ha, hb, hmlo, hmhi, hjpos, hjm, hmcast, hqcast, hjhalf, hqhalf⟩ :=
    binomialLog_window_geometry N L a b j hN hba haL hhalf hj
  have hju := (mem_Ico.mp hj).1
  have hjv := (mem_Ico.mp hj).2
  have hqpos : 1 ≤ q := by dsimp only [q]; omega
  have hqlo : N - a < q := by dsimp only [q, m]; omega
  have hqhi : q ≤ N - b := by dsimp only [q, m]; omega
  have hmR : (m : ℝ) = 2 * (N : ℝ) - s := by
    dsimp only [s]
    linarith only [hmcast]
  have hjR : (j : ℝ) = (N : ℝ) + (t - s / 2) := by
    dsimp only [t]
    linarith only [hmR]
  have hqR : (q : ℝ) = (N : ℝ) + (-t - s / 2) := by
    dsimp only [t]
    linarith only [hmR, hqcast]
  have hs0 : 0 ≤ s := by dsimp only [s]; positivity
  have hsL : s ≤ 2 * (L : ℝ) := by
    dsimp only [s]
    exact_mod_cast (show a + b ≤ 2 * L by omega)
  have hAL : (a : ℝ) ≤ (L : ℝ) := by exact_mod_cast haL
  have hjloR : (N : ℝ) - (a : ℝ) ≤ (j : ℝ) := by
    rw [← Nat.cast_sub ha]
    exact_mod_cast hju
  have hjN : (j : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (le_trans hjv.le (Nat.sub_le N b))
  have hqloR : (N : ℝ) - (a : ℝ) ≤ (q : ℝ) := by
    rw [← Nat.cast_sub ha]
    exact_mod_cast hqlo.le
  have hqN : (q : ℝ) ≤ (N : ℝ) := by exact_mod_cast (le_trans hqhi (Nat.sub_le N b))
  have hdj : |(j : ℝ) - (N : ℝ)| ≤ (L : ℝ) := by
    rw [abs_of_nonpos (sub_nonpos.mpr hjN)]
    linarith only [hjloR, hAL]
  have hdq : |(q : ℝ) - (N : ℝ)| ≤ (L : ℝ) := by
    rw [abs_of_nonpos (sub_nonpos.mpr hqN)]
    linarith only [hqloR, hAL]
  have hc := binomialLog_window_center N a b j hba ha hj
  let v := j - (N - a)
  let d := a - b
  have hv0 : (0 : ℝ) ≤ v := Nat.cast_nonneg _
  have hvd : (v : ℝ) < (d : ℝ) := by exact_mod_cast hc.1
  have hdL : (d : ℝ) ≤ (L : ℝ) := by exact_mod_cast (le_trans (Nat.sub_le a b) haL)
  have ht : t = (v : ℝ) - (d : ℝ) / 2 := hc.2
  have htL : |t| ≤ (L : ℝ) / 2 := by
    rw [ht]
    exact abs_le.mpr ⟨by linarith only [hv0, hdL], by linarith only [hvd, hdL]⟩
  exact ⟨ha, hb, hjpos, hjm, hqpos, hqlo, hqhi, hmR, hjR, hqR, hs0, hsL, htL, hdj, hdq⟩

theorem binomialSharpShift_reciprocal_bounds (N L a b j K r : ℕ)
    (hN : 4 ≤ N) (hba : b < a) (haL : a ≤ L)
    (hhalf : 2 * (L : ℝ) < (N : ℝ)) (hj : j ∈ Ico (N - a) (N - b))
    (hr : 1 ≤ r) (hrK : r ≤ K) :
    let m := (N - a) + (N - b)
    let q := m - j
    let s : ℝ := (a : ℝ) + (b : ℝ)
    let t : ℝ := (j : ℝ) - (m : ℝ) / 2
    |1 / (m : ℝ) ^ r - shiftedReciprocalPrefix K r (2 * (N : ℝ)) (-s)| ≤
        (2 : ℝ) ^ (r - 1) * (Nat.choose K (r - 1) : ℝ) *
          (L : ℝ) ^ (K - r + 1) / (N : ℝ) ^ (K + 1) ∧
      |1 / (j : ℝ) ^ r - shiftedReciprocalPrefix K r (N : ℝ) (t - s / 2)| ≤
        (2 : ℝ) ^ (2 * r - 1) * (Nat.choose K (r - 1) : ℝ) *
          (L : ℝ) ^ (K - r + 1) / (N : ℝ) ^ (K + 1) ∧
      |1 / (q : ℝ) ^ r - shiftedReciprocalPrefix K r (N : ℝ) (-t - s / 2)| ≤
        (2 : ℝ) ^ (2 * r - 1) * (Nat.choose K (r - 1) : ℝ) *
          (L : ℝ) ^ (K - r + 1) / (N : ℝ) ^ (K + 1) := by
  let m := (N - a) + (N - b)
  let q := m - j
  let s : ℝ := (a : ℝ) + (b : ℝ)
  let t : ℝ := (j : ℝ) - (m : ℝ) / 2
  obtain ⟨ha, hb, hjpos, hjm, hqpos, hqlo, hqhi, hmR, hjR, hqR, hs0, hsL, htL, hdj, hdq⟩ :=
    binomialSharpShift_geometry N L a b j hN hba haL hhalf hj
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLhalf : (L : ℝ) ≤ (N : ℝ) / 2 := by linarith only [hhalf]
  have hhj : |t - s / 2| ≤ (L : ℝ) := by
    have he : t - s / 2 = (j : ℝ) - (N : ℝ) := by linarith only [hjR]
    rw [he]
    exact hdj
  have hhq : |-t - s / 2| ≤ (L : ℝ) := by
    have he : -t - s / 2 = (q : ℝ) - (N : ℝ) := by linarith only [hqR]
    rw [he]
    exact hdq
  have bm := shiftedReciprocalPrefix_doubled_shift_bound K r (N : ℝ) (L : ℝ) s
    hr hrK hn hhalf.le hs0 hsL
  have bj := shiftedReciprocalPrefix_small_shift_bound K r (N : ℝ) (L : ℝ) (t - s / 2)
    hr hrK hn hLhalf hhj
  have bq := shiftedReciprocalPrefix_small_shift_bound K r (N : ℝ) (L : ℝ) (-t - s / 2)
    hr hrK hn hLhalf hhq
  rw [← hmR] at bm
  rw [← hjR] at bj
  rw [← hqR] at bq
  exact ⟨bm, bj, bq⟩

theorem uniform_binomialSharpShift_reciprocal_bounds (C : ℝ) (hC : 0 < C) :
    ∃ N0 : ℕ, 4 ≤ N0 ∧ ∀ N ≥ N0, ∀ L a b j K r : ℕ,
      b < a → a ≤ L → (L : ℝ) ≤ C * Real.log (N : ℝ) →
      j ∈ Ico (N - a) (N - b) → 1 ≤ r → r ≤ K →
      let m := (N - a) + (N - b)
      let q := m - j
      let s : ℝ := (a : ℝ) + (b : ℝ)
      let t : ℝ := (j : ℝ) - (m : ℝ) / 2
      |1 / (m : ℝ) ^ r - shiftedReciprocalPrefix K r (2 * (N : ℝ)) (-s)| ≤
          (2 : ℝ) ^ (r - 1) * (Nat.choose K (r - 1) : ℝ) *
            (L : ℝ) ^ (K - r + 1) / (N : ℝ) ^ (K + 1) ∧
        |1 / (j : ℝ) ^ r - shiftedReciprocalPrefix K r (N : ℝ) (t - s / 2)| ≤
          (2 : ℝ) ^ (2 * r - 1) * (Nat.choose K (r - 1) : ℝ) *
            (L : ℝ) ^ (K - r + 1) / (N : ℝ) ^ (K + 1) ∧
        |1 / (q : ℝ) ^ r - shiftedReciprocalPrefix K r (N : ℝ) (-t - s / 2)| ≤
          (2 : ℝ) ^ (2 * r - 1) * (Nat.choose K (r - 1) : ℝ) *
            (L : ℝ) ^ (K - r + 1) / (N : ℝ) ^ (K + 1) := by
  obtain ⟨M, hM2, hM⟩ := logWindow_eventually_below_half C
  refine ⟨max 4 M, le_max_left _ _, ?_⟩
  intro N hN L a b j K r hba haL hlog hj hr hrK
  have hN4 : 4 ≤ N := le_trans (le_max_left _ _) hN
  have ht := hM N (le_trans (le_max_right _ _) hN)
  have hhalf : 2 * (L : ℝ) < (N : ℝ) := by linarith
  exact binomialSharpShift_reciprocal_bounds N L a b j K r hN4 hba haL hhalf hj hr hrK

end Hardinian
