import Hardinian.BinomialScalarCoefficientCollection
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Degrees

namespace Hardinian

open Finset MvPolynomial

noncomputable def binomialLogCoeff (n : ℕ) : MvPolynomial (Fin 2) ℚ :=
  let S : MvPolynomial (Fin 2) ℚ := X 0
  let T : MvPolynomial (Fin 2) ℚ := X 1
  let U := C (1 / 2 : ℚ) * S
  if n = 0 then 0 else
    C ((1 : ℚ) / ((2 : ℚ) ^ (n + 1) * (n : ℚ))) * S ^ n
      - (∑ i ∈ range ((n + 1) / 2),
          C ((Nat.choose (n - 1) (2 * i) : ℚ) /
            (((i : ℚ) + 1) * (2 * (i : ℚ) + 1))) *
          T ^ (2 * i + 2) * U ^ (n - (2 * i + 1)))
      + (∑ i ∈ range (n / 2),
          C ((Nat.choose (n - 1) (2 * i + 1) : ℚ) / (2 * ((i : ℚ) + 1))) *
          T ^ (2 * i + 2) * U ^ (n - (2 * i + 2)))
      + (∑ i ∈ range n,
          C (stirlingCorrectionCoeff i * (Nat.choose (n - 1) i : ℚ)) *
          (C ((1 : ℚ) / (2 : ℚ) ^ (i + 1)) * U ^ (n - (i + 1))
            - (U - T) ^ (n - (i + 1)) - (U + T) ^ (n - (i + 1))))

theorem binomialLogCoeff_zero : binomialLogCoeff 0 = 0 := by
  simp [binomialLogCoeff]

theorem binomialLogCoeff_eval (n : ℕ) (s t : ℝ) :
    eval₂Hom (Rat.castHom ℝ) (fun i : Fin 2 => if i = 0 then s else t) (binomialLogCoeff n) =
      binomialScalarLogCoeff n s t := by
  classical
  unfold binomialLogCoeff binomialScalarLogCoeff
  dsimp only
  split_ifs <;> simp [map_sum, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

theorem binomialReexpandedLogApprox_eq_polynomial_coeff_sum
    (N m j K : ℕ) (hN : 1 ≤ N) :
    let s : ℝ := 2 * (N : ℝ) - (m : ℝ)
    let t : ℝ := (j : ℝ) - (m : ℝ) / 2
    binomialReexpandedLogApprox N m j K =
      ∑ n ∈ Icc 1 K,
        eval₂Hom (Rat.castHom ℝ) (fun i : Fin 2 => if i = 0 then s else t)
          (binomialLogCoeff n) / (N : ℝ) ^ n := by
  simpa only [binomialLogCoeff_eval] using
    binomialReexpandedLogApprox_eq_scalar_coeff_sum N m j K hN

theorem binomialLogCoeff_reflect (n : ℕ) :
    eval₂Hom C (fun i : Fin 2 => if i = 0 then X 0 else -X 1) (binomialLogCoeff n) =
      binomialLogCoeff n := by
  classical
  have heven (i : ℕ) : (-(X 1 : MvPolynomial (Fin 2) ℚ)) ^ (2 * i + 2) =
      (X 1 : MvPolynomial (Fin 2) ℚ) ^ (2 * i + 2) := by
    rw [show 2 * i + 2 = 2 * (i + 1) by omega]
    simp only [pow_mul, neg_sq]
  by_cases hn : n = 0
  · simp [binomialLogCoeff, hn]
  · simp only [binomialLogCoeff, if_neg hn, map_add, map_sub, map_sum, map_mul, map_pow,
      eval₂Hom_C, eval₂Hom_X', if_pos (rfl : (0 : Fin 2) = 0),
      if_neg (by decide : (1 : Fin 2) ≠ 0)]
    simp only [heven, sub_neg_eq_add, ← sub_eq_add_neg, if_pos True.intro]
    congr 1
    apply sum_congr rfl
    intro i hi
    ring

theorem binomialPoly_degree_neg (p : MvPolynomial (Fin 2) ℚ) :
    (-p).totalDegree ≤ p.totalDegree := by
  have h := totalDegree_mul (C (-1 : ℚ)) p
  rw [totalDegree_C, zero_add] at h
  simpa only [map_neg, map_one, neg_one_mul] using h

theorem binomialPoly_degree_sub (p q : MvPolynomial (Fin 2) ℚ) :
    (p - q).totalDegree ≤ max p.totalDegree q.totalDegree := by
  rw [sub_eq_add_neg]
  exact (totalDegree_add _ _).trans (max_le_max le_rfl (binomialPoly_degree_neg q))

theorem binomialPoly_degree_product (c : ℚ) (p q : MvPolynomial (Fin 2) ℚ) (a b : ℕ)
    (hp : p.totalDegree ≤ 1) (hq : q.totalDegree ≤ 1) :
    (C c * p ^ a * q ^ b).totalDegree ≤ a + b := by
  have hpa : (p ^ a).totalDegree ≤ a :=
    (totalDegree_pow p a).trans (by simpa using Nat.mul_le_mul_left a hp)
  have hqb : (q ^ b).totalDegree ≤ b :=
    (totalDegree_pow q b).trans (by simpa using Nat.mul_le_mul_left b hq)
  have hc : (C c * p ^ a).totalDegree ≤ a :=
    (totalDegree_mul _ _).trans (by simpa only [totalDegree_C, zero_add] using hpa)
  exact (totalDegree_mul _ _).trans (add_le_add hc hqb)

theorem binomialLogCoeff_totalDegree (n : ℕ) :
    (binomialLogCoeff n).totalDegree ≤ n + 1 := by
  classical
  by_cases hn : n = 0
  · simp [hn, binomialLogCoeff_zero]
  have hn1 : 1 ≤ n := by omega
  let S : MvPolynomial (Fin 2) ℚ := X 0
  let T : MvPolynomial (Fin 2) ℚ := X 1
  let U : MvPolynomial (Fin 2) ℚ := C (1 / 2 : ℚ) * S
  have hS : S.totalDegree ≤ 1 := by dsimp only [S]; simp
  have hT : T.totalDegree ≤ 1 := by dsimp only [T]; simp
  have hU : U.totalDegree ≤ 1 :=
    (totalDegree_mul _ _).trans (by simpa only [totalDegree_C, zero_add] using hS)
  have hminus : (U - T).totalDegree ≤ 1 :=
    (binomialPoly_degree_sub _ _).trans (max_le hU hT)
  have hplus : (U + T).totalDegree ≤ 1 := (totalDegree_add _ _).trans (max_le hU hT)
  let Y : MvPolynomial (Fin 2) ℚ := C ((1 : ℚ) / (2 ^ (n + 1) * (n : ℚ))) * S ^ n
  let E : MvPolynomial (Fin 2) ℚ := ∑ i ∈ range ((n + 1) / 2),
    C ((Nat.choose (n - 1) (2 * i) : ℚ) / (((i : ℚ) + 1) * (2 * (i : ℚ) + 1))) *
      T ^ (2 * i + 2) * U ^ (n - (2 * i + 1))
  let Xs : MvPolynomial (Fin 2) ℚ := ∑ i ∈ range (n / 2),
    C ((Nat.choose (n - 1) (2 * i + 1) : ℚ) / (2 * ((i : ℚ) + 1))) *
      T ^ (2 * i + 2) * U ^ (n - (2 * i + 2))
  let F : MvPolynomial (Fin 2) ℚ := ∑ i ∈ range n,
    C (stirlingCorrectionCoeff i * (Nat.choose (n - 1) i : ℚ)) *
      (C ((1 : ℚ) / 2 ^ (i + 1)) * U ^ (n - (i + 1))
        - (U - T) ^ (n - (i + 1)) - (U + T) ^ (n - (i + 1)))
  have hY : Y.totalDegree ≤ n := by
    simpa only [Y, pow_zero, mul_one, Nat.add_zero] using
      binomialPoly_degree_product ((1 : ℚ) / (2 ^ (n + 1) * (n : ℚ))) S U n 0 hS hU
  have hE : E.totalDegree ≤ n + 1 := by
    apply totalDegree_finsetSum_le
    intro i hi
    have hir : 2 * i + 1 ≤ n := by have := mem_range.mp hi; omega
    exact (binomialPoly_degree_product _ T U (2 * i + 2) (n - (2 * i + 1)) hT hU).trans
      (by omega)
  have hX : Xs.totalDegree ≤ n := by
    apply totalDegree_finsetSum_le
    intro i hi
    have hir : 2 * i + 2 ≤ n := by have := mem_range.mp hi; omega
    exact (binomialPoly_degree_product _ T U (2 * i + 2) (n - (2 * i + 2)) hT hU).trans
      (by omega)
  have hF : F.totalDegree ≤ n - 1 := by
    apply totalDegree_finsetSum_le
    intro i hi
    have hir : i + 1 ≤ n := by have := mem_range.mp hi; omega
    let e := n - (i + 1)
    have hu : (U ^ e).totalDegree ≤ e :=
      (totalDegree_pow U e).trans (by simpa using Nat.mul_le_mul_left e hU)
    have hm : ((U - T) ^ e).totalDegree ≤ e :=
      (totalDegree_pow _ e).trans (by simpa using Nat.mul_le_mul_left e hminus)
    have hp : ((U + T) ^ e).totalDegree ≤ e :=
      (totalDegree_pow _ e).trans (by simpa using Nat.mul_le_mul_left e hplus)
    have hc : (C ((1 : ℚ) / 2 ^ (i + 1)) * U ^ e).totalDegree ≤ e :=
      (totalDegree_mul _ _).trans (by simpa only [totalDegree_C, zero_add] using hu)
    have hd : (C ((1 : ℚ) / 2 ^ (i + 1)) * U ^ e - (U - T) ^ e - (U + T) ^ e).totalDegree ≤ e :=
      (binomialPoly_degree_sub _ _).trans
        (max_le ((binomialPoly_degree_sub _ _).trans (max_le hc hm)) hp)
    have hcF : (C (stirlingCorrectionCoeff i * (Nat.choose (n - 1) i : ℚ)) *
        (C ((1 : ℚ) / 2 ^ (i + 1)) * U ^ e - (U - T) ^ e - (U + T) ^ e)).totalDegree ≤ e :=
      (totalDegree_mul _ _).trans (by simpa only [totalDegree_C, zero_add] using hd)
    exact hcF.trans (by dsimp only [e]; omega)
  unfold binomialLogCoeff
  rw [if_neg hn]
  change (Y - E + Xs + F).totalDegree ≤ n + 1
  have hYE : (Y - E).totalDegree ≤ n + 1 :=
    (binomialPoly_degree_sub _ _).trans (max_le (hY.trans (by omega)) hE)
  have hYEX : (Y - E + Xs).totalDegree ≤ n + 1 :=
    (totalDegree_add _ _).trans (max_le hYE (hX.trans (by omega)))
  exact (totalDegree_add _ _).trans (max_le hYEX (hF.trans (by omega)))

theorem binomialLogCoeff_one :
    binomialLogCoeff 1 = -((X 1 : MvPolynomial (Fin 2) ℚ) ^ 2)
      + C (1 / 4 : ℚ) * X 0 - C (1 / 8 : ℚ) := by
  have hc : (C (1 / 12 : ℚ) : MvPolynomial (Fin 2) ℚ) * (C (1 / 2 : ℚ) - 1 - 1) =
      -C (1 / 8 : ℚ) := by
    calc
      _ = C ((1 / 12 : ℚ) * (1 / 2 - 1 - 1)) := by simp
      _ = _ := by norm_num
  have he : binomialLogCoeff 1 =
      C (1 / 4 : ℚ) * (X 0 : MvPolynomial (Fin 2) ℚ) - (X 1) ^ 2 +
        C (1 / 12 : ℚ) * (C (1 / 2 : ℚ) - 1 - 1) := by
    norm_num [binomialLogCoeff, sum_range_succ, stirlingCorrectionCoeff_zero]
  rw [he, hc]
  ring

theorem uniform_normalizedBinomialLog_coeff_window (C : ℝ) (hC : 0 < C) :
    ∃ N0 : ℕ, 4 ≤ N0 ∧ ∀ N ≥ N0, ∀ L a b j K : ℕ,
      b < a → a ≤ L → (L : ℝ) ≤ C * Real.log (N : ℝ) →
      j ∈ Ico (N - a) (N - b) →
      let m := (N - a) + (N - b)
      let s : ℝ := (a : ℝ) + (b : ℝ)
      let t : ℝ := (j : ℝ) - (m : ℝ) / 2
      |Real.log (Real.sqrt (Real.pi * (N : ℝ)) * binomialMass m j) -
        (∑ n ∈ Icc 1 K,
          eval₂Hom (Rat.castHom ℝ) (fun i : Fin 2 => if i = 0 then s else t)
            (binomialLogCoeff n) / (N : ℝ) ^ n)| ≤
        (10 + 6 * (2 : ℝ) ^ (K + 1) * (stirlingResidualConstant K : ℝ) +
          (binomialLogReexpansionConstant K : ℝ)) *
          (1 + (L : ℝ)) ^ (K + 2) / (N : ℝ) ^ (K + 1) := by
  obtain ⟨NA, hNA4, hA⟩ := uniform_normalizedBinomialLog_common_truncation C hC
  obtain ⟨NR, hNR4, hR⟩ := uniform_binomialLog_finite_reexpansion C hC
  obtain ⟨NG, hNG2, hG⟩ := logWindow_eventually_below_half C
  refine ⟨max NA (max NR NG), le_trans hNA4 (le_max_left _ _), ?_⟩
  intro N hN L a b j K hba haL hlog hj
  have hNA : NA ≤ N := le_trans (le_max_left _ _) hN
  have hNR : NR ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hN)
  have hNG : NG ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN)
  have hN4 : 4 ≤ N := le_trans hNA4 hNA
  have hN1 : 1 ≤ N := by omega
  have ht := hG N hNG
  have hhalf : 2 * (L : ℝ) < (N : ℝ) := by linarith
  let m := (N - a) + (N - b)
  let s : ℝ := (a : ℝ) + (b : ℝ)
  let t : ℝ := (j : ℝ) - (m : ℝ) / 2
  obtain ⟨ha, hb, hjpos, hjm, hqpos, hqlo, hqhi, hmR, hrest⟩ :=
    binomialSharpShift_geometry N L a b j hN4 hba haL hhalf hj
  have hs : 2 * (N : ℝ) - (m : ℝ) = s := by
    dsimp only [m, s]
    rw [hmR]
    ring
  have hB := binomialReexpandedLogApprox_eq_polynomial_coeff_sum N m j K hN1
  dsimp only at hB
  rw [hs] at hB
  have hAe := hA N hNA L a b j K hba haL hlog hj
  have hRe := hR N hNR L a b j K hba haL hlog hj
  change |Real.log (Real.sqrt (Real.pi * (N : ℝ)) * binomialMass m j) -
    (∑ n ∈ Icc 1 K, eval₂Hom (Rat.castHom ℝ)
      (fun i : Fin 2 => if i = 0 then s else t) (binomialLogCoeff n) / (N : ℝ) ^ n)| ≤ _
  rw [← hB]
  calc
    _ = |(Real.log (Real.sqrt (Real.pi * (N : ℝ)) * binomialMass m j) -
          binomialCommonLogApprox N m j K) +
        (binomialCommonLogApprox N m j K - binomialReexpandedLogApprox N m j K)| := by
      congr 1
      ring
    _ ≤ |Real.log (Real.sqrt (Real.pi * (N : ℝ)) * binomialMass m j) -
          binomialCommonLogApprox N m j K| +
        |binomialCommonLogApprox N m j K - binomialReexpandedLogApprox N m j K| := abs_add _ _
    _ ≤ (10 + 6 * (2 : ℝ) ^ (K + 1) * (stirlingResidualConstant K : ℝ)) *
          (1 + (L : ℝ)) ^ (K + 2) / (N : ℝ) ^ (K + 1) +
        (binomialLogReexpansionConstant K : ℝ) *
          (1 + (L : ℝ)) ^ (K + 2) / (N : ℝ) ^ (K + 1) := add_le_add hAe hRe
    _ = _ := by ring

end Hardinian
