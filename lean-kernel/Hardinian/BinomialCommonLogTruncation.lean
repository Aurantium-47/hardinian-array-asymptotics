import Hardinian.BinomialEntropyIdentity

namespace Hardinian

open Finset

noncomputable def binomialCommonLogApprox (N m j K : ℕ) : ℝ :=
  let x : ℝ := (2 * (j : ℝ) - (m : ℝ)) / (m : ℝ)
  let y : ℝ := 1 - (m : ℝ) / (2 * (N : ℝ))
  (∑ i ∈ range K, y ^ (i + 1) / ((i : ℝ) + 1)) / 2
    - ((m : ℝ) / 2) * evenLogEntropyPrefix ((K + 1) / 2) x
    + (∑ i ∈ range (K / 2), (x ^ 2) ^ (i + 1) / ((i : ℝ) + 1)) / 2
    + stirlingCorrectionPrefix m K - stirlingCorrectionPrefix j K
    - stirlingCorrectionPrefix (m - j) K

theorem halfLog_truncation_error (K : ℕ) (z : ℝ)
    (hz0 : 0 ≤ z) (hzhalf : z ≤ 1 / 2) :
    |-Real.log (1 - z) / 2
      - (∑ i ∈ range K, z ^ (i + 1) / ((i : ℝ) + 1)) / 2| ≤ z ^ (K + 1) := by
  have hzlt : |z| < 1 := by rw [abs_of_nonneg hz0]; linarith
  have hb := Real.abs_log_sub_add_sum_range_le hzlt K
  rw [abs_of_nonneg hz0] at hb
  have hd : 0 < 1 - z := by linarith
  have hp : 0 ≤ z ^ (K + 1) := pow_nonneg hz0 _
  have hbd : z ^ (K + 1) / (1 - z) ≤ 2 * z ^ (K + 1) := by
    apply (div_le_iff₀ hd).2
    nlinarith only [mul_le_mul_of_nonneg_left hzhalf hp]
  have he : -Real.log (1 - z) / 2 -
      (∑ i ∈ range K, z ^ (i + 1) / ((i : ℝ) + 1)) / 2 =
      -((∑ i ∈ range K, z ^ (i + 1) / ((i : ℝ) + 1)) + Real.log (1 - z)) / 2 := by ring
  rw [he, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
  nlinarith only [hb.trans hbd]

theorem evenLogEntropy_order_error (K : ℕ) (x v : ℝ)
    (hv0 : 0 ≤ v) (hvhalf : v ≤ 1 / 2) (hx : |x| ≤ v) :
    |evenLogEntropy x - evenLogEntropyPrefix ((K + 1) / 2) x| ≤ 8 * v ^ (K + 2) := by
  have hexp : K + 2 ≤ 2 * ((K + 1) / 2) + 2 := by omega
  have hv1 : v ≤ 1 := by linarith
  calc
    _ ≤ 8 * |x| ^ (2 * ((K + 1) / 2) + 2) :=
      evenLogEntropy_remainder_bound _ x (hx.trans hvhalf)
    _ ≤ 8 * v ^ (2 * ((K + 1) / 2) + 2) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg x) hx _) (by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hv0 hv1 hexp) (by norm_num)

theorem halfSquareLog_truncation_error (K : ℕ) (x v : ℝ)
    (hv0 : 0 ≤ v) (hvhalf : v ≤ 1 / 2) (hx : |x| ≤ v) :
    |-Real.log (1 - x ^ 2) / 2 -
      (∑ i ∈ range (K / 2), (x ^ 2) ^ (i + 1) / ((i : ℝ) + 1)) / 2| ≤ v ^ (K + 1) := by
  have hx2 : x ^ 2 = |x| ^ 2 := by rw [← abs_pow, abs_of_nonneg (sq_nonneg x)]
  have hsmall : x ^ 2 ≤ 1 / 2 := by
    have ht := pow_le_pow_left₀ (abs_nonneg x) (hx.trans hvhalf) 2
    rw [← hx2] at ht
    norm_num at ht
    linarith
  have hv1 : v ≤ 1 := by linarith
  have hexp : K + 1 ≤ 2 * (K / 2) + 2 := by omega
  calc
    _ ≤ (x ^ 2) ^ (K / 2 + 1) := halfLog_truncation_error (K / 2) (x ^ 2) (sq_nonneg x) hsmall
    _ = |x| ^ (2 * (K / 2) + 2) := by
      rw [hx2, ← pow_mul]
      <;> congr 1
      <;> omega
    _ ≤ v ^ (2 * (K / 2) + 2) := pow_le_pow_left₀ (abs_nonneg x) hx _
    _ ≤ _ := pow_le_pow_of_le_one hv0 hv1 hexp

theorem uniform_normalizedBinomialLog_common_truncation (C : ℝ) (hC : 0 < C) :
    ∃ N0 : ℕ, 4 ≤ N0 ∧ ∀ N ≥ N0, ∀ L a b j K : ℕ,
      b < a → a ≤ L → (L : ℝ) ≤ C * Real.log (N : ℝ) →
      j ∈ Ico (N - a) (N - b) →
      let m := (N - a) + (N - b)
      |Real.log (Real.sqrt (Real.pi * (N : ℝ)) * binomialMass m j) -
        binomialCommonLogApprox N m j K| ≤
        (10 + 6 * (2 : ℝ) ^ (K + 1) * (stirlingResidualConstant K : ℝ)) *
          (1 + (L : ℝ)) ^ (K + 2) / (N : ℝ) ^ (K + 1) := by
  obtain ⟨NM, hNM4, hM⟩ := uniform_normalizedBinomialLog_prefix_window C hC
  obtain ⟨NI, hNI4, hI⟩ := uniform_binomial_entropy_coordinates C hC
  refine ⟨max NM NI, le_trans hNM4 (le_max_left _ _), ?_⟩
  intro N hN L a b j K hba haL hlog hj
  have hNM : NM ≤ N := le_trans (le_max_left _ _) hN
  have hNI : NI ≤ N := le_trans (le_max_right _ _) hN
  have hN4 : 4 ≤ N := le_trans hNM4 hNM
  have hN1 : 1 ≤ N := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let m := (N - a) + (N - b)
  let x : ℝ := (2 * (j : ℝ) - (m : ℝ)) / (m : ℝ)
  let y : ℝ := 1 - (m : ℝ) / (2 * (N : ℝ))
  let v : ℝ := (L : ℝ) / (N : ℝ)
  obtain ⟨hjpos, hjm, herr⟩ := hM N hNM L a b j K hba haL hlog hj
  obtain ⟨hrel, hy0, hyv, hxv, hvhalf⟩ := hI N hNI L a b j hba haL hlog hj
  change (m : ℝ) / (2 * (N : ℝ)) = 1 - ((a : ℝ) + (b : ℝ)) / (2 * (N : ℝ)) at hrel
  change |x| ≤ v at hxv
  change v < 1 / 2 at hvhalf
  have hyEq : y = ((a : ℝ) + (b : ℝ)) / (2 * (N : ℝ)) := by
    dsimp only [y]
    linarith only [hrel]
  have hy0' : 0 ≤ y := by rw [hyEq]; exact hy0
  have hyv' : y ≤ v := by rw [hyEq]; exact hyv
  have hv0 : 0 ≤ v := by dsimp only [v]; positivity
  have hm2N : m ≤ 2 * N := by
    dsimp only [m]
    have ha0 := Nat.sub_le N a
    have hb0 := Nat.sub_le N b
    omega
  have hmle : (m : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hm2N
  have hmhalf : 0 ≤ (m : ℝ) / 2 := by positivity
  have hweight : (m : ℝ) / 2 ≤ (N : ℝ) := by linarith only [hmle]
  let B := binomialLogBulk N m j + stirlingCorrectionPrefix m K -
    stirlingCorrectionPrefix j K - stirlingCorrectionPrefix (m - j) K
  let c : ℝ := 6 * (2 : ℝ) ^ (K + 1) * (stirlingResidualConstant K : ℝ)
  let P : ℝ := (1 + (L : ℝ)) ^ (K + 2)
  change |Real.log (Real.sqrt (Real.pi * (N : ℝ)) * binomialMass m j) - B| ≤
    c / (N : ℝ) ^ (K + 1) at herr
  let rY := -Real.log (1 - y) / 2 -
    (∑ i ∈ range K, y ^ (i + 1) / ((i : ℝ) + 1)) / 2
  let rE := -((m : ℝ) / 2) * (evenLogEntropy x - evenLogEntropyPrefix ((K + 1) / 2) x)
  let rX := -Real.log (1 - x ^ 2) / 2 -
    (∑ i ∈ range (K / 2), (x ^ 2) ^ (i + 1) / ((i : ℝ) + 1)) / 2
  have hbulk := binomialLogBulk_entropy N m j hN1 hjpos hjm
  change binomialLogBulk N m j = -Real.log ((m : ℝ) / (2 * (N : ℝ))) / 2 -
    ((m : ℝ) / 2) * evenLogEntropy x - Real.log (1 - x ^ 2) / 2 at hbulk
  have hratio : (m : ℝ) / (2 * (N : ℝ)) = 1 - y := by dsimp only [y]; ring
  rw [hratio] at hbulk
  have hbId : B - binomialCommonLogApprox N m j K = rY + rE + rX := by
    dsimp only [B, binomialCommonLogApprox]
    rw [hbulk]
    dsimp only [rY, rE, rX, x, y]
    ring
  have hyr : |rY| ≤ v ^ (K + 1) :=
    (halfLog_truncation_error K y hy0' (hyv'.trans hvhalf.le)).trans
      (pow_le_pow_left₀ hy0' hyv' _)
  have hxr : |rX| ≤ v ^ (K + 1) := halfSquareLog_truncation_error K x v hv0 hvhalf.le hxv
  have her : |rE| ≤ 8 * (N : ℝ) * v ^ (K + 2) := by
    dsimp only [rE]
    rw [abs_mul, abs_neg, abs_of_nonneg hmhalf]
    calc
      _ ≤ ((m : ℝ) / 2) * (8 * v ^ (K + 2)) :=
        mul_le_mul_of_nonneg_left (evenLogEntropy_order_error K x v hv0 hvhalf.le hxv) hmhalf
      _ ≤ (N : ℝ) * (8 * v ^ (K + 2)) :=
        mul_le_mul_of_nonneg_right hweight (by positivity)
      _ = _ := by ring
  have hbBound : |B - binomialCommonLogApprox N m j K| ≤
      2 * v ^ (K + 1) + 8 * (N : ℝ) * v ^ (K + 2) := by
    rw [hbId]
    calc
      _ ≤ |rY| + |rE| + |rX| := (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)
      _ ≤ v ^ (K + 1) + 8 * (N : ℝ) * v ^ (K + 2) + v ^ (K + 1) :=
        add_le_add (add_le_add hyr her) hxr
      _ = _ := by ring
  have hvpow1 : v ^ (K + 1) = (L : ℝ) ^ (K + 1) / (N : ℝ) ^ (K + 1) := by
    dsimp only [v]
    rw [div_pow]
  have hvpow2 : (N : ℝ) * v ^ (K + 2) = (L : ℝ) ^ (K + 2) / (N : ℝ) ^ (K + 1) := by
    dsimp only [v]
    rw [div_pow, show (N : ℝ) ^ (K + 2) = (N : ℝ) ^ (K + 1) * (N : ℝ) from pow_succ _ _]
    field_simp [hn.ne']
    <;> ring
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have hbase : (1 : ℝ) ≤ 1 + (L : ℝ) := by linarith only [hL0]
  have hP1 : 1 ≤ P := one_le_pow₀ hbase
  have hL1 : (L : ℝ) ^ (K + 1) ≤ P :=
    (pow_le_pow_left₀ hL0 (show (L : ℝ) ≤ 1 + (L : ℝ) by linarith) _).trans
      (pow_le_pow_right₀ hbase (by omega))
  have hL2 : (L : ℝ) ^ (K + 2) ≤ P :=
    pow_le_pow_left₀ hL0 (by linarith) _
  have hden : 0 < (N : ℝ) ^ (K + 1) := pow_pos hn _
  have hscale : 2 * v ^ (K + 1) + 8 * (N : ℝ) * v ^ (K + 2) ≤
      10 * P / (N : ℝ) ^ (K + 1) := by
    calc
      _ = 2 * v ^ (K + 1) + 8 * ((N : ℝ) * v ^ (K + 2)) := by ring
      _ = (2 * (L : ℝ) ^ (K + 1) + 8 * (L : ℝ) ^ (K + 2)) / (N : ℝ) ^ (K + 1) := by
        rw [hvpow1, hvpow2]
        ring
      _ ≤ _ := by
        apply (div_le_div_iff_of_pos_right hden).2
        nlinarith only [hL1, hL2]
  have hconst : (0 : ℝ) ≤ (stirlingResidualConstant K : ℝ) := by
    exact_mod_cast stirlingResidualConstant_nonneg K
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hcscale : c / (N : ℝ) ^ (K + 1) ≤ c * P / (N : ℝ) ^ (K + 1) := by
    apply (div_le_div_iff_of_pos_right hden).2
    nlinarith only [mul_le_mul_of_nonneg_left hP1 hc]
  change |Real.log (Real.sqrt (Real.pi * (N : ℝ)) * binomialMass m j) -
    binomialCommonLogApprox N m j K| ≤ (10 + c) * P / (N : ℝ) ^ (K + 1)
  calc
    _ = |(Real.log (Real.sqrt (Real.pi * (N : ℝ)) * binomialMass m j) - B) +
        (B - binomialCommonLogApprox N m j K)| := by congr 1; ring
    _ ≤ |Real.log (Real.sqrt (Real.pi * (N : ℝ)) * binomialMass m j) - B| +
        |B - binomialCommonLogApprox N m j K| := abs_add _ _
    _ ≤ c / (N : ℝ) ^ (K + 1) + 10 * P / (N : ℝ) ^ (K + 1) :=
      add_le_add herr (hbBound.trans hscale)
    _ ≤ c * P / (N : ℝ) ^ (K + 1) + 10 * P / (N : ℝ) ^ (K + 1) :=
      add_le_add_right hcscale _
    _ = _ := by ring

end Hardinian
