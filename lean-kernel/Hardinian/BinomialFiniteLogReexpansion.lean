import Hardinian.BinomialCommonLogTruncation
import Hardinian.BinomialSignedLogReexpansion

namespace Hardinian

open Finset

noncomputable def binomialReexpandedLogApprox (N m j K : ℕ) : ℝ :=
  let s : ℝ := 2 * (N : ℝ) - (m : ℝ)
  let t : ℝ := (j : ℝ) - (m : ℝ) / 2
  (∑ i ∈ range K, (s / (2 * (N : ℝ))) ^ (i + 1) / ((i : ℝ) + 1)) / 2
    - (∑ i ∈ range ((K + 1) / 2),
        ((2 : ℝ) ^ (2 * i + 1) * t ^ (2 * i + 2) /
          (((i : ℝ) + 1) * (2 * (i : ℝ) + 1))) *
        shiftedReciprocalPrefix K (2 * i + 1) (2 * (N : ℝ)) (-s))
    + (∑ i ∈ range (K / 2),
        ((2 : ℝ) ^ (2 * i + 1) * t ^ (2 * i + 2) / ((i : ℝ) + 1)) *
        shiftedReciprocalPrefix K (2 * i + 2) (2 * (N : ℝ)) (-s))
    + (∑ i ∈ range K, (stirlingCorrectionCoeff i : ℝ) *
        (shiftedReciprocalPrefix K (i + 1) (2 * (N : ℝ)) (-s)
          - shiftedReciprocalPrefix K (i + 1) (N : ℝ) (t - s / 2)
          - shiftedReciprocalPrefix K (i + 1) (N : ℝ) (-t - s / 2)))

def binomialLogReexpansionConstant (K : ℕ) : ℚ :=
  (∑ i ∈ range ((K + 1) / 2),
      (2 : ℚ) ^ (4 * i + 1) * (Nat.choose K (2 * i) : ℚ) /
        (((i : ℚ) + 1) * (2 * (i : ℚ) + 1)))
    + (∑ i ∈ range (K / 2),
        (2 : ℚ) ^ (4 * i + 2) * (Nat.choose K (2 * i + 1) : ℚ) / ((i : ℚ) + 1))
    + (∑ i ∈ range K, |stirlingCorrectionCoeff i| *
        ((2 : ℚ) ^ i + (2 : ℚ) ^ (2 * i + 2)) * (Nat.choose K i : ℚ))

theorem binomialLogReexpansionConstant_nonneg (K : ℕ) :
    0 ≤ binomialLogReexpansionConstant K := by
  unfold binomialLogReexpansionConstant
  apply add_nonneg
  · apply add_nonneg
    · exact sum_nonneg fun i hi => by positivity
    · exact sum_nonneg fun i hi => by positivity
  · exact sum_nonneg fun i hi => by positivity

theorem binomialLogReexpansionConstant_cast (K : ℕ) :
    (binomialLogReexpansionConstant K : ℝ) =
      (∑ i ∈ range ((K + 1) / 2),
        (2 : ℝ) ^ (4 * i + 1) * (Nat.choose K (2 * i) : ℝ) /
          (((i : ℝ) + 1) * (2 * (i : ℝ) + 1)))
      + (∑ i ∈ range (K / 2),
          (2 : ℝ) ^ (4 * i + 2) * (Nat.choose K (2 * i + 1) : ℝ) / ((i : ℝ) + 1))
      + (∑ i ∈ range K, |(stirlingCorrectionCoeff i : ℝ)| *
          ((2 : ℝ) ^ i + (2 : ℝ) ^ (2 * i + 2)) * (Nat.choose K i : ℝ)) := by
  unfold binomialLogReexpansionConstant
  push_cast <;> rfl

theorem binomialFiniteReexpansion_zero (N m j : ℕ) :
    binomialCommonLogApprox N m j 0 = 0 ∧
      binomialReexpandedLogApprox N m j 0 = 0 ∧
      binomialLogReexpansionConstant 0 = 0 := by
  simp [binomialCommonLogApprox, binomialReexpandedLogApprox,
    binomialLogReexpansionConstant, evenLogEntropyPrefix, stirlingCorrectionPrefix]

theorem binomialEntropyTerm_reciprocal (i : ℕ) (m t : ℝ) (hm : m ≠ 0) :
    (m / 2) * ((2 * t / m) ^ (2 * i + 2) /
      (((i : ℝ) + 1) * (2 * (i : ℝ) + 1))) =
      ((2 : ℝ) ^ (2 * i + 1) * t ^ (2 * i + 2) /
        (((i : ℝ) + 1) * (2 * (i : ℝ) + 1))) * (1 / m ^ (2 * i + 1)) := by
  have hd1 : (i : ℝ) + 1 ≠ 0 := by positivity
  have hd2 : 2 * (i : ℝ) + 1 ≠ 0 := by positivity
  rw [div_pow, mul_pow,
    show (2 : ℝ) ^ (2 * i + 2) = 2 ^ (2 * i + 1) * 2 from pow_succ _ _,
    show m ^ (2 * i + 2) = m ^ (2 * i + 1) * m from pow_succ _ _]
  field_simp [hm, hd1, hd2]
  <;> ring

theorem binomialSquareTerm_reciprocal (i : ℕ) (m t : ℝ) (hm : m ≠ 0) :
    (((2 * t / m) ^ 2) ^ (i + 1) / ((i : ℝ) + 1)) / 2 =
      ((2 : ℝ) ^ (2 * i + 1) * t ^ (2 * i + 2) / ((i : ℝ) + 1)) *
        (1 / m ^ (2 * i + 2)) := by
  have hd : (i : ℝ) + 1 ≠ 0 := by positivity
  rw [← pow_mul, show 2 * (i + 1) = 2 * i + 2 by omega, div_pow, mul_pow,
    show (2 : ℝ) ^ (2 * i + 2) = 2 ^ (2 * i + 1) * 2 from pow_succ _ _]
  field_simp [hm, hd]
  <;> ring

theorem binomialCommonLogApprox_reciprocal_sums (N m j K : ℕ)
    (hN : 0 < N) (hm : 0 < m) :
    let s : ℝ := 2 * (N : ℝ) - (m : ℝ)
    let t : ℝ := (j : ℝ) - (m : ℝ) / 2
    binomialCommonLogApprox N m j K =
      (∑ i ∈ range K, (s / (2 * (N : ℝ))) ^ (i + 1) / ((i : ℝ) + 1)) / 2
      - (∑ i ∈ range ((K + 1) / 2),
          ((2 : ℝ) ^ (2 * i + 1) * t ^ (2 * i + 2) /
            (((i : ℝ) + 1) * (2 * (i : ℝ) + 1))) * (1 / (m : ℝ) ^ (2 * i + 1)))
      + (∑ i ∈ range (K / 2),
          ((2 : ℝ) ^ (2 * i + 1) * t ^ (2 * i + 2) / ((i : ℝ) + 1)) *
            (1 / (m : ℝ) ^ (2 * i + 2)))
      + (∑ i ∈ range K, (stirlingCorrectionCoeff i : ℝ) *
          (1 / (m : ℝ) ^ (i + 1) - 1 / (j : ℝ) ^ (i + 1)
            - 1 / ((m - j : ℕ) : ℝ) ^ (i + 1))) := by
  let s : ℝ := 2 * (N : ℝ) - (m : ℝ)
  let t : ℝ := (j : ℝ) - (m : ℝ) / 2
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hmr : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hx : (2 * (j : ℝ) - (m : ℝ)) / (m : ℝ) = 2 * t / (m : ℝ) := by
    dsimp only [t]
    congr 1
    ring
  have hy : 1 - (m : ℝ) / (2 * (N : ℝ)) = s / (2 * (N : ℝ)) := by
    dsimp only [s]
    field_simp [hn]
    <;> ring
  have he : ((m : ℝ) / 2) * evenLogEntropyPrefix ((K + 1) / 2) (2 * t / (m : ℝ)) =
      ∑ i ∈ range ((K + 1) / 2),
        ((2 : ℝ) ^ (2 * i + 1) * t ^ (2 * i + 2) /
          (((i : ℝ) + 1) * (2 * (i : ℝ) + 1))) * (1 / (m : ℝ) ^ (2 * i + 1)) := by
    unfold evenLogEntropyPrefix
    rw [mul_sum]
    exact sum_congr rfl fun i hi => binomialEntropyTerm_reciprocal i (m : ℝ) t hmr
  have hxsum : (∑ i ∈ range (K / 2),
      ((2 * t / (m : ℝ)) ^ 2) ^ (i + 1) / ((i : ℝ) + 1)) / 2 =
      ∑ i ∈ range (K / 2),
        ((2 : ℝ) ^ (2 * i + 1) * t ^ (2 * i + 2) / ((i : ℝ) + 1)) *
          (1 / (m : ℝ) ^ (2 * i + 2)) := by
    rw [sum_div]
    exact sum_congr rfl fun i hi => binomialSquareTerm_reciprocal i (m : ℝ) t hmr
  have hf : stirlingCorrectionPrefix m K - stirlingCorrectionPrefix j K -
      stirlingCorrectionPrefix (m - j) K =
      ∑ i ∈ range K, (stirlingCorrectionCoeff i : ℝ) *
        (1 / (m : ℝ) ^ (i + 1) - 1 / (j : ℝ) ^ (i + 1) -
          1 / ((m - j : ℕ) : ℝ) ^ (i + 1)) := by
    unfold stirlingCorrectionPrefix
    rw [← sum_sub_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i hi
    ring
  dsimp only [binomialCommonLogApprox]
  rw [hx, hy, he, hxsum]
  linarith only [hf]

theorem finiteReexpansion_monomial_bound (K e d : ℕ) (N L t c b z : ℝ)
    (hN : 0 < N) (hL : 0 ≤ L) (ht : |t| ≤ L) (hc : 0 ≤ c) (hb : 0 ≤ b)
    (hd : e + d ≤ K + 2)
    (hz : |z| ≤ b * L ^ d / N ^ (K + 1)) :
    |c * t ^ e * z| ≤ c * b * (1 + L) ^ (K + 2) / N ^ (K + 1) := by
  have hp : L ^ (e + d) ≤ (1 + L) ^ (K + 2) :=
    (pow_le_pow_left₀ hL (show L ≤ 1 + L by linarith) _).trans
      (pow_le_pow_right₀ (show (1 : ℝ) ≤ 1 + L by linarith) hd)
  rw [abs_mul, abs_mul, abs_of_nonneg hc, abs_pow]
  calc
    _ ≤ (c * L ^ e) * (b * L ^ d / N ^ (K + 1)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg t) ht _) hc)
        hz (abs_nonneg z) (by positivity)
    _ = c * b * L ^ (e + d) / N ^ (K + 1) := by rw [pow_add]; ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hp (mul_nonneg hc hb)) (by positivity)

theorem finiteReexpansion_entropy_bound (K i : ℕ) (N L t z : ℝ)
    (hi : i < (K + 1) / 2) (hN : 0 < N) (hL : 0 ≤ L) (ht : |t| ≤ L)
    (hz : |z| ≤ (2 : ℝ) ^ (2 * i) * (Nat.choose K (2 * i) : ℝ) *
      L ^ (K - (2 * i + 1) + 1) / N ^ (K + 1)) :
    |((2 : ℝ) ^ (2 * i + 1) * t ^ (2 * i + 2) /
      (((i : ℝ) + 1) * (2 * (i : ℝ) + 1))) * z| ≤
      ((2 : ℝ) ^ (4 * i + 1) * (Nat.choose K (2 * i) : ℝ) /
        (((i : ℝ) + 1) * (2 * (i : ℝ) + 1))) *
        (1 + L) ^ (K + 2) / N ^ (K + 1) := by
  have h := finiteReexpansion_monomial_bound K (2 * i + 2) (K - (2 * i + 1) + 1)
    N L t ((2 : ℝ) ^ (2 * i + 1) / (((i : ℝ) + 1) * (2 * (i : ℝ) + 1)))
    ((2 : ℝ) ^ (2 * i) * (Nat.choose K (2 * i) : ℝ)) z
    hN hL ht (by positivity) (by positivity) (by omega) hz
  have he : (2 : ℝ) ^ (2 * i + 1) * 2 ^ (2 * i) = 2 ^ (4 * i + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hc : ((2 : ℝ) ^ (2 * i + 1) / (((i : ℝ) + 1) * (2 * (i : ℝ) + 1))) *
      (2 ^ (2 * i) * (Nat.choose K (2 * i) : ℝ)) =
      2 ^ (4 * i + 1) * (Nat.choose K (2 * i) : ℝ) /
        (((i : ℝ) + 1) * (2 * (i : ℝ) + 1)) := by
    calc
      _ = ((2 : ℝ) ^ (2 * i + 1) * 2 ^ (2 * i)) * (Nat.choose K (2 * i) : ℝ) /
          (((i : ℝ) + 1) * (2 * (i : ℝ) + 1)) := by ring
      _ = _ := by rw [he]
  calc
    _ = |((2 : ℝ) ^ (2 * i + 1) / (((i : ℝ) + 1) * (2 * (i : ℝ) + 1))) *
        t ^ (2 * i + 2) * z| := by congr 1; ring
    _ ≤ _ := h
    _ = _ := by rw [hc]

theorem finiteReexpansion_square_bound (K i : ℕ) (N L t z : ℝ)
    (hi : i < K / 2) (hN : 0 < N) (hL : 0 ≤ L) (ht : |t| ≤ L)
    (hz : |z| ≤ (2 : ℝ) ^ (2 * i + 1) * (Nat.choose K (2 * i + 1) : ℝ) *
      L ^ (K - (2 * i + 2) + 1) / N ^ (K + 1)) :
    |((2 : ℝ) ^ (2 * i + 1) * t ^ (2 * i + 2) / ((i : ℝ) + 1)) * z| ≤
      ((2 : ℝ) ^ (4 * i + 2) * (Nat.choose K (2 * i + 1) : ℝ) / ((i : ℝ) + 1)) *
        (1 + L) ^ (K + 2) / N ^ (K + 1) := by
  have h := finiteReexpansion_monomial_bound K (2 * i + 2) (K - (2 * i + 2) + 1)
    N L t ((2 : ℝ) ^ (2 * i + 1) / ((i : ℝ) + 1))
    ((2 : ℝ) ^ (2 * i + 1) * (Nat.choose K (2 * i + 1) : ℝ)) z
    hN hL ht (by positivity) (by positivity) (by omega) hz
  have he : (2 : ℝ) ^ (2 * i + 1) * 2 ^ (2 * i + 1) = 2 ^ (4 * i + 2) := by
    rw [← pow_add]
    congr 1
    omega
  have hc : ((2 : ℝ) ^ (2 * i + 1) / ((i : ℝ) + 1)) *
      (2 ^ (2 * i + 1) * (Nat.choose K (2 * i + 1) : ℝ)) =
      2 ^ (4 * i + 2) * (Nat.choose K (2 * i + 1) : ℝ) / ((i : ℝ) + 1) := by
    calc
      _ = ((2 : ℝ) ^ (2 * i + 1) * 2 ^ (2 * i + 1)) * (Nat.choose K (2 * i + 1) : ℝ) /
          ((i : ℝ) + 1) := by ring
      _ = _ := by rw [he]
  calc
    _ = |((2 : ℝ) ^ (2 * i + 1) / ((i : ℝ) + 1)) * t ^ (2 * i + 2) * z| := by
      congr 1
      ring
    _ ≤ _ := h
    _ = _ := by rw [hc]

theorem finiteReexpansion_factorial_bound (K i : ℕ) (N L zm zj zq : ℝ)
    (hi : i < K) (hN : 0 < N) (hL : 0 ≤ L)
    (hm : |zm| ≤ (2 : ℝ) ^ i * (Nat.choose K i : ℝ) * L ^ (K - i) / N ^ (K + 1))
    (hj : |zj| ≤ (2 : ℝ) ^ (2 * i + 1) * (Nat.choose K i : ℝ) *
      L ^ (K - i) / N ^ (K + 1))
    (hq : |zq| ≤ (2 : ℝ) ^ (2 * i + 1) * (Nat.choose K i : ℝ) *
      L ^ (K - i) / N ^ (K + 1)) :
    |(stirlingCorrectionCoeff i : ℝ) * (zm - zj - zq)| ≤
      (|(stirlingCorrectionCoeff i : ℝ)| * ((2 : ℝ) ^ i + (2 : ℝ) ^ (2 * i + 2)) *
        (Nat.choose K i : ℝ)) * (1 + L) ^ (K + 2) / N ^ (K + 1) := by
  have hz : |zm - zj - zq| ≤
      (((2 : ℝ) ^ i + (2 : ℝ) ^ (2 * i + 2)) * (Nat.choose K i : ℝ)) *
        L ^ (K - i) / N ^ (K + 1) := by
    calc
      _ ≤ |zm| + |zj| + |zq| := (abs_sub _ _).trans (add_le_add_right (abs_sub _ _) _)
      _ ≤ (2 : ℝ) ^ i * (Nat.choose K i : ℝ) * L ^ (K - i) / N ^ (K + 1) +
          (2 : ℝ) ^ (2 * i + 1) * (Nat.choose K i : ℝ) * L ^ (K - i) / N ^ (K + 1) +
          (2 : ℝ) ^ (2 * i + 1) * (Nat.choose K i : ℝ) * L ^ (K - i) / N ^ (K + 1) :=
        add_le_add (add_le_add hm hj) hq
      _ = _ := by rw [show (2 : ℝ) ^ (2 * i + 2) = 2 ^ (2 * i + 1) * 2 from pow_succ _ _]; ring
  have hh := finiteReexpansion_monomial_bound K 0 (K - i) N L 0
    |(stirlingCorrectionCoeff i : ℝ)|
    (((2 : ℝ) ^ i + (2 : ℝ) ^ (2 * i + 2)) * (Nat.choose K i : ℝ)) (zm - zj - zq)
    hN hL (by simpa using hL) (abs_nonneg _) (by positivity) (by omega) hz
  simpa only [pow_zero, mul_one, abs_mul, abs_abs, mul_assoc] using hh

theorem binomialLog_finite_reexpansion_bound (N L a b j K : ℕ)
    (hN : 4 ≤ N) (hba : b < a) (haL : a ≤ L)
    (hhalf : 2 * (L : ℝ) < (N : ℝ)) (hj : j ∈ Ico (N - a) (N - b)) :
    let m := (N - a) + (N - b)
    |binomialCommonLogApprox N m j K - binomialReexpandedLogApprox N m j K| ≤
      (binomialLogReexpansionConstant K : ℝ) *
        (1 + (L : ℝ)) ^ (K + 2) / (N : ℝ) ^ (K + 1) := by
  let m := (N - a) + (N - b)
  let q := m - j
  let s : ℝ := (a : ℝ) + (b : ℝ)
  let t : ℝ := (j : ℝ) - (m : ℝ) / 2
  let P : ℝ := (1 + (L : ℝ)) ^ (K + 2)
  let D : ℝ := (N : ℝ) ^ (K + 1)
  obtain ⟨ha, hb, hjpos, hjm, hqpos, hqlo, hqhi, hmR, hjR, hqR, hs0, hsL, htL, hdj, hdq⟩ :=
    binomialSharpShift_geometry N L a b j hN hba haL hhalf hj
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have ht : |t| ≤ (L : ℝ) := htL.trans (by linarith only [hL])
  have hs : 2 * (N : ℝ) - (m : ℝ) = s := by linarith only [hmR]
  let em := fun r => 1 / (m : ℝ) ^ r - shiftedReciprocalPrefix K r (2 * (N : ℝ)) (-s)
  let ej := fun r => 1 / (j : ℝ) ^ r - shiftedReciprocalPrefix K r (N : ℝ) (t - s / 2)
  let eq := fun r => 1 / (q : ℝ) ^ r - shiftedReciprocalPrefix K r (N : ℝ) (-t - s / 2)
  let cE := fun i => (2 : ℝ) ^ (4 * i + 1) * (Nat.choose K (2 * i) : ℝ) /
    (((i : ℝ) + 1) * (2 * (i : ℝ) + 1))
  let cX := fun i => (2 : ℝ) ^ (4 * i + 2) * (Nat.choose K (2 * i + 1) : ℝ) / ((i : ℝ) + 1)
  let cF := fun i => |(stirlingCorrectionCoeff i : ℝ)| *
    ((2 : ℝ) ^ i + (2 : ℝ) ^ (2 * i + 2)) * (Nat.choose K i : ℝ)
  let e := ∑ i ∈ range ((K + 1) / 2),
    ((2 : ℝ) ^ (2 * i + 1) * t ^ (2 * i + 2) /
      (((i : ℝ) + 1) * (2 * (i : ℝ) + 1))) * em (2 * i + 1)
  let x := ∑ i ∈ range (K / 2),
    ((2 : ℝ) ^ (2 * i + 1) * t ^ (2 * i + 2) / ((i : ℝ) + 1)) * em (2 * i + 2)
  let f := ∑ i ∈ range K, (stirlingCorrectionCoeff i : ℝ) *
    (em (i + 1) - ej (i + 1) - eq (i + 1))
  have he : |e| ≤ (∑ i ∈ range ((K + 1) / 2), cE i) * P / D := by
    calc
      _ ≤ ∑ i ∈ range ((K + 1) / 2),
          |((2 : ℝ) ^ (2 * i + 1) * t ^ (2 * i + 2) /
            (((i : ℝ) + 1) * (2 * (i : ℝ) + 1))) * em (2 * i + 1)| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ range ((K + 1) / 2), cE i * P / D := by
        apply sum_le_sum
        intro i hi
        have hir : i < (K + 1) / 2 := mem_range.mp hi
        have h := (binomialSharpShift_reciprocal_bounds N L a b j K (2 * i + 1)
          hN hba haL hhalf hj (by omega) (by omega)).1
        have h' : |em (2 * i + 1)| ≤ (2 : ℝ) ^ (2 * i) * (Nat.choose K (2 * i) : ℝ) *
            (L : ℝ) ^ (K - (2 * i + 1) + 1) / (N : ℝ) ^ (K + 1) := by
          simpa only [show 2 * i + 1 - 1 = 2 * i by omega] using h
        exact finiteReexpansion_entropy_bound K i (N : ℝ) (L : ℝ) t (em (2 * i + 1))
          hir hn hL ht h'
      _ = _ := by simp only [div_eq_mul_inv, sum_mul]
  have hx : |x| ≤ (∑ i ∈ range (K / 2), cX i) * P / D := by
    calc
      _ ≤ ∑ i ∈ range (K / 2),
          |((2 : ℝ) ^ (2 * i + 1) * t ^ (2 * i + 2) / ((i : ℝ) + 1)) * em (2 * i + 2)| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ range (K / 2), cX i * P / D := by
        apply sum_le_sum
        intro i hi
        have hir : i < K / 2 := mem_range.mp hi
        have h := (binomialSharpShift_reciprocal_bounds N L a b j K (2 * i + 2)
          hN hba haL hhalf hj (by omega) (by omega)).1
        have h' : |em (2 * i + 2)| ≤ (2 : ℝ) ^ (2 * i + 1) *
            (Nat.choose K (2 * i + 1) : ℝ) * (L : ℝ) ^ (K - (2 * i + 2) + 1) /
              (N : ℝ) ^ (K + 1) := by
          simpa only [show 2 * i + 2 - 1 = 2 * i + 1 by omega] using h
        exact finiteReexpansion_square_bound K i (N : ℝ) (L : ℝ) t (em (2 * i + 2))
          hir hn hL ht h'
      _ = _ := by simp only [div_eq_mul_inv, sum_mul]
  have hf : |f| ≤ (∑ i ∈ range K, cF i) * P / D := by
    calc
      _ ≤ ∑ i ∈ range K,
          |(stirlingCorrectionCoeff i : ℝ) * (em (i + 1) - ej (i + 1) - eq (i + 1))| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ range K, cF i * P / D := by
        apply sum_le_sum
        intro i hi
        have hir : i < K := mem_range.mp hi
        have h := binomialSharpShift_reciprocal_bounds N L a b j K (i + 1)
          hN hba haL hhalf hj (by omega) (by omega)
        simp only [show i + 1 - 1 = i by omega,
          show 2 * (i + 1) - 1 = 2 * i + 1 by omega,
          show K - (i + 1) + 1 = K - i by omega] at h
        exact finiteReexpansion_factorial_bound K i (N : ℝ) (L : ℝ)
          (em (i + 1)) (ej (i + 1)) (eq (i + 1)) hir hn hL h.1 h.2.1 h.2.2
      _ = _ := by simp only [div_eq_mul_inv, sum_mul]
  have hA := binomialCommonLogApprox_reciprocal_sums N m j K (by omega) (by omega)
  dsimp only at hA
  rw [hs] at hA
  have hdiff : binomialCommonLogApprox N m j K - binomialReexpandedLogApprox N m j K =
      -e + x + f := by
    rw [hA]
    dsimp only [binomialReexpandedLogApprox]
    rw [hs]
    dsimp only [e, x, f, em, ej, eq, q, t]
    simp only [mul_sub, sum_sub_distrib]
    ring
  have hc := binomialLogReexpansionConstant_cast K
  change (binomialLogReexpansionConstant K : ℝ) =
    (∑ i ∈ range ((K + 1) / 2), cE i) + (∑ i ∈ range (K / 2), cX i) +
      (∑ i ∈ range K, cF i) at hc
  rw [hdiff]
  calc
    _ ≤ |e| + |x| + |f| := by
      simpa only [abs_neg] using (abs_add (-e + x) f).trans (add_le_add_right (abs_add (-e) x) _)
    _ ≤ (∑ i ∈ range ((K + 1) / 2), cE i) * P / D +
        (∑ i ∈ range (K / 2), cX i) * P / D + (∑ i ∈ range K, cF i) * P / D :=
      add_le_add (add_le_add he hx) hf
    _ = _ := by rw [hc]; ring

theorem uniform_binomialLog_finite_reexpansion (C : ℝ) (hC : 0 < C) :
    ∃ N0 : ℕ, 4 ≤ N0 ∧ ∀ N ≥ N0, ∀ L a b j K : ℕ,
      b < a → a ≤ L → (L : ℝ) ≤ C * Real.log (N : ℝ) →
      j ∈ Ico (N - a) (N - b) →
      let m := (N - a) + (N - b)
      |binomialCommonLogApprox N m j K - binomialReexpandedLogApprox N m j K| ≤
        (binomialLogReexpansionConstant K : ℝ) *
          (1 + (L : ℝ)) ^ (K + 2) / (N : ℝ) ^ (K + 1) := by
  obtain ⟨M, hM2, hM⟩ := logWindow_eventually_below_half C
  refine ⟨max 4 M, le_max_left _ _, ?_⟩
  intro N hN L a b j K hba haL hlog hj
  have hN4 : 4 ≤ N := le_trans (le_max_left _ _) hN
  have ht := hM N (le_trans (le_max_right _ _) hN)
  have hhalf : 2 * (L : ℝ) < (N : ℝ) := by linarith
  exact binomialLog_finite_reexpansion_bound N L a b j K hN4 hba haL hhalf hj

end Hardinian
