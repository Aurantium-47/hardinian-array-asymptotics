import Hardinian.BinomialExponentialCoefficients

open Filter
open scoped Topology

namespace Hardinian

open Finset MvPolynomial

noncomputable def binomialLogCoeffMajorant (i : ℕ) : ℚ :=
  (2 : ℚ) ^ (i + 1) * ∑ d ∈ (binomialLogCoeff i).support,
    |MvPolynomial.coeff d (binomialLogCoeff i)|

noncomputable def binomialLogPrefixMajorant (K : ℕ) : ℚ :=
  ∑ i ∈ Icc 1 K, binomialLogCoeffMajorant i

def binomialExpLogErrorConstant (K : ℕ) : ℚ :=
  10 + 6 * (2 : ℚ) ^ (K + 1) * stirlingResidualConstant K + binomialLogReexpansionConstant K

noncomputable def binomialExpDroppedMajorant (K : ℕ) : ℚ :=
  ∑ k ∈ range (K + 1), binomialLogPrefixMajorant K ^ k / (k.factorial : ℚ)

noncomputable def binomialExpWindowConstant (K : ℕ) : ℝ :=
  Real.exp 1 * ((binomialExpLogErrorConstant K : ℝ) +
    (binomialLogPrefixMajorant K : ℝ) ^ (K + 1) / ((K + 1).factorial : ℝ)) +
      (binomialExpDroppedMajorant K : ℝ)

theorem binomialLogCoeffMajorant_nonneg (i : ℕ) : 0 ≤ binomialLogCoeffMajorant i := by
  unfold binomialLogCoeffMajorant
  positivity

theorem binomialLogCoeffMajorant_cast (i : ℕ) :
    (binomialLogCoeffMajorant i : ℝ) =
      (2 : ℝ) ^ (i + 1) * ∑ d ∈ (binomialLogCoeff i).support,
        |((MvPolynomial.coeff d (binomialLogCoeff i) : ℚ) : ℝ)| := by
  norm_num [binomialLogCoeffMajorant]

theorem binomialLogPrefixMajorant_nonneg (K : ℕ) : 0 ≤ binomialLogPrefixMajorant K := by
  exact sum_nonneg fun i hi => binomialLogCoeffMajorant_nonneg i

theorem binomialLogPrefixMajorant_cast (K : ℕ) :
    (binomialLogPrefixMajorant K : ℝ) =
      ∑ i ∈ Icc 1 K, (binomialLogCoeffMajorant i : ℝ) := by
  simp [binomialLogPrefixMajorant]

theorem binomialExpLogErrorConstant_nonneg (K : ℕ) :
    0 ≤ binomialExpLogErrorConstant K := by
  have hC := stirlingResidualConstant_nonneg K
  have hR := binomialLogReexpansionConstant_nonneg K
  unfold binomialExpLogErrorConstant
  positivity

theorem binomialExpLogErrorConstant_cast (K : ℕ) :
    (binomialExpLogErrorConstant K : ℝ) =
      10 + 6 * (2 : ℝ) ^ (K + 1) * (stirlingResidualConstant K : ℝ) +
        (binomialLogReexpansionConstant K : ℝ) := by
  norm_num [binomialExpLogErrorConstant]

theorem binomialExpDroppedMajorant_nonneg (K : ℕ) :
    0 ≤ binomialExpDroppedMajorant K := by
  have hA := binomialLogPrefixMajorant_nonneg K
  unfold binomialExpDroppedMajorant
  apply sum_nonneg
  intro k hk
  positivity

theorem binomialExpDroppedMajorant_cast (K : ℕ) :
    (binomialExpDroppedMajorant K : ℝ) =
      ∑ k ∈ range (K + 1), (binomialLogPrefixMajorant K : ℝ) ^ k / (k.factorial : ℝ) := by
  norm_num [binomialExpDroppedMajorant]

theorem binomialExpWindowConstant_nonneg (K : ℕ) :
    0 ≤ binomialExpWindowConstant K := by
  have hA : (0 : ℝ) ≤ (binomialLogPrefixMajorant K : ℝ) := by
    exact_mod_cast binomialLogPrefixMajorant_nonneg K
  have hD : (0 : ℝ) ≤ (binomialExpLogErrorConstant K : ℝ) := by
    exact_mod_cast binomialExpLogErrorConstant_nonneg K
  have hV : (0 : ℝ) ≤ (binomialExpDroppedMajorant K : ℝ) := by
    exact_mod_cast binomialExpDroppedMajorant_nonneg K
  unfold binomialExpWindowConstant
  positivity

theorem binomialExpConstants_zero :
    binomialLogCoeffMajorant 0 = 0 ∧ binomialLogPrefixMajorant 0 = 0 ∧
    binomialExpLogErrorConstant 0 = 46 ∧ binomialExpDroppedMajorant 0 = 1 ∧
    binomialExpWindowConstant 0 = 46 * Real.exp 1 + 1 := by
  norm_num [binomialLogCoeffMajorant, binomialLogCoeff_zero, binomialLogPrefixMajorant,
    binomialExpLogErrorConstant, stirlingResidualConstant, binomialLogReexpansionConstant,
    binomialExpDroppedMajorant, binomialExpWindowConstant] <;> ring

theorem binomialLogCoeff_eval_majorant (i : ℕ) (s t B : ℝ)
    (hB : 1 ≤ B) (hs : |s| ≤ 2 * B) (ht : |t| ≤ 2 * B) :
    |eval₂Hom (Rat.castHom ℝ) (fun a : Fin 2 => if a = 0 then s else t)
      (binomialLogCoeff i)| ≤ (binomialLogCoeffMajorant i : ℝ) * B ^ (i + 1) := by
  classical
  let φ : Fin 2 → ℝ := fun a => if a = 0 then s else t
  have hφ (a : Fin 2) : |φ a| ≤ 2 * B := by
    dsimp only [φ]
    split_ifs <;> assumption
  have h2B : 1 ≤ 2 * B := by linarith
  change |MvPolynomial.eval₂ (Rat.castHom ℝ) φ (binomialLogCoeff i)| ≤ _
  rw [MvPolynomial.eval₂_eq]
  calc
    _ ≤ ∑ d ∈ (binomialLogCoeff i).support,
        |((MvPolynomial.coeff d (binomialLogCoeff i) : ℚ) : ℝ) * ∏ a ∈ d.support, φ a ^ d a| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ (binomialLogCoeff i).support,
        |((MvPolynomial.coeff d (binomialLogCoeff i) : ℚ) : ℝ)| * (2 * B) ^ (i + 1) := by
      apply sum_le_sum
      intro d hd
      rw [abs_mul, abs_prod]
      simp_rw [abs_pow]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      calc
        _ ≤ ∏ a ∈ d.support, (2 * B) ^ d a :=
          prod_le_prod (fun a ha => pow_nonneg (abs_nonneg _) _)
            (fun a ha => pow_le_pow_left₀ (abs_nonneg _) (hφ a) _)
        _ = (2 * B) ^ (d.sum fun _ e => e) := by rw [prod_pow_eq_pow_sum]; rfl
        _ ≤ (2 * B) ^ (i + 1) :=
          pow_le_pow_right₀ h2B ((le_totalDegree hd).trans (binomialLogCoeff_totalDegree i))
    _ = (binomialLogCoeffMajorant i : ℝ) * B ^ (i + 1) := by
      rw [← sum_mul, binomialLogCoeffMajorant_cast, mul_pow]
      ring

theorem binomialLogCoeff_reciprocal_majorant (i N : ℕ) (hi : 1 ≤ i) (hN : 1 ≤ N)
    (s t B : ℝ) (hB : 1 ≤ B) (hs : |s| ≤ 2 * B) (ht : |t| ≤ 2 * B) :
    |eval₂Hom (Rat.castHom ℝ) (fun a : Fin 2 => if a = 0 then s else t)
        (binomialLogCoeff i) * (1 / (N : ℝ)) ^ i| ≤
      (binomialLogCoeffMajorant i : ℝ) * (B ^ 2 / (N : ℝ)) ^ i := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hAi : (0 : ℝ) ≤ (binomialLogCoeffMajorant i : ℝ) := by
    exact_mod_cast binomialLogCoeffMajorant_nonneg i
  have hpow : B ^ (i + 1) ≤ B ^ (2 * i) := pow_le_pow_right₀ hB (by omega)
  have hw : (0 : ℝ) ≤ 1 / (N : ℝ) := le_of_lt (one_div_pos.mpr hNr)
  rw [abs_mul, abs_pow, abs_of_nonneg hw]
  calc
    _ ≤ ((binomialLogCoeffMajorant i : ℝ) * B ^ (i + 1)) * (1 / (N : ℝ)) ^ i :=
      mul_le_mul_of_nonneg_right (binomialLogCoeff_eval_majorant i s t B hB hs ht) (pow_nonneg hw _)
    _ ≤ ((binomialLogCoeffMajorant i : ℝ) * B ^ (2 * i)) * (1 / (N : ℝ)) ^ i :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hAi) (pow_nonneg hw _)
    _ = _ := by simp only [div_eq_mul_inv, one_mul, mul_pow, pow_mul]; ring

theorem binomialLogPrefix_eval_majorant (K N : ℕ) (hN : 1 ≤ N) (s t B : ℝ)
    (hB : 1 ≤ B) (hs : |s| ≤ 2 * B) (ht : |t| ≤ 2 * B)
    (hz : B ^ 2 / (N : ℝ) ≤ 1) :
    |∑ i ∈ Icc 1 K, eval₂Hom (Rat.castHom ℝ)
      (fun a : Fin 2 => if a = 0 then s else t) (binomialLogCoeff i) / (N : ℝ) ^ i| ≤
      (binomialLogPrefixMajorant K : ℝ) * (B ^ 2 / (N : ℝ)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hz0 : 0 ≤ B ^ 2 / (N : ℝ) := div_nonneg (sq_nonneg B) hNr.le
  calc
    _ ≤ ∑ i ∈ Icc 1 K, |eval₂Hom (Rat.castHom ℝ)
        (fun a : Fin 2 => if a = 0 then s else t) (binomialLogCoeff i) / (N : ℝ) ^ i| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Icc 1 K, (binomialLogCoeffMajorant i : ℝ) * (B ^ 2 / (N : ℝ)) ^ i := by
      apply sum_le_sum
      intro i hi
      simpa only [div_pow, one_pow, mul_one_div] using
        binomialLogCoeff_reciprocal_majorant i N (mem_Icc.mp hi).1 hN s t B hB hs ht
    _ ≤ ∑ i ∈ Icc 1 K, (binomialLogCoeffMajorant i : ℝ) * (B ^ 2 / (N : ℝ)) := by
      apply sum_le_sum
      intro i hi
      have hAi : (0 : ℝ) ≤ (binomialLogCoeffMajorant i : ℝ) := by
        exact_mod_cast binomialLogCoeffMajorant_nonneg i
      apply mul_le_mul_of_nonneg_left _ hAi
      simpa only [pow_one] using pow_le_pow_of_le_one hz0 hz (mem_Icc.mp hi).1
    _ = _ := by rw [← sum_mul, binomialLogPrefixMajorant_cast]

theorem binomial_exp_sub_exp_le (x u : ℝ) (hx : |x| ≤ 1) (hu : |u| ≤ 1) :
    |Real.exp x - Real.exp u| ≤ Real.exp 1 * |x - u| := by
  have hf : ∀ y ∈ Set.Icc (-1 : ℝ) 1, DifferentiableAt ℝ Real.exp y :=
    fun y hy => Real.differentiableAt_exp
  have hb : ∀ y ∈ Set.Icc (-1 : ℝ) 1, ‖deriv Real.exp y‖ ≤ Real.exp 1 := by
    intro y hy
    rw [Real.deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos y)]
    exact Real.exp_le_exp.mpr hy.2
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_deriv_le hf hb (convex_Icc (-1 : ℝ) 1)
      (abs_le.mp hu) (abs_le.mp hx)

theorem binomial_exp_taylor_bound (K : ℕ) (u : ℝ) (hu : |u| ≤ 1) :
    |Real.exp u - ∑ k ∈ range (K + 1), u ^ k / (k.factorial : ℝ)| ≤
      Real.exp 1 * |u| ^ (K + 1) / ((K + 1).factorial : ℝ) := by
  let n := K + 1
  have hn : 0 < n := by dsimp [n]; omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
  have hnum : ((n + 1 : ℕ) : ℝ) ≤ Real.exp 1 * (n : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right he hnR.le
    norm_num only [Nat.cast_add, Nat.cast_one]
    nlinarith
  have hratio : ((n + 1 : ℕ) : ℝ) / ((n.factorial : ℝ) * (n : ℝ)) ≤
      Real.exp 1 / (n.factorial : ℝ) := by
    apply (div_le_div_iff₀ (mul_pos hfac hnR) hfac).mpr
    calc
      _ ≤ (Real.exp 1 * (n : ℝ)) * (n.factorial : ℝ) :=
        mul_le_mul_of_nonneg_right hnum hfac.le
      _ = _ := by ring
  have hbase := Real.exp_bound hu (n := n) hn
  have hbase' : |Real.exp u - ∑ k ∈ range n, u ^ k / (k.factorial : ℝ)| ≤
      |u| ^ n * (((n + 1 : ℕ) : ℝ) / ((n.factorial : ℝ) * (n : ℝ))) := by
    simpa only [Nat.succ_eq_add_one, Nat.cast_mul] using hbase
  calc
    _ ≤ |u| ^ n * (((n + 1 : ℕ) : ℝ) / ((n.factorial : ℝ) * (n : ℝ))) := hbase'
    _ ≤ |u| ^ n * (Real.exp 1 / (n.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left hratio (pow_nonneg (abs_nonneg u) _)
    _ = _ := by dsimp only [n]; ring

theorem binomialComposition_eval_majorant (K k N : ℕ) (hN : 1 ≤ N)
    (v : Fin k → Fin K) (s t B : ℝ) (hB : 1 ≤ B)
    (hs : |s| ≤ 2 * B) (ht : |t| ≤ 2 * B) :
    |(∏ i : Fin k, eval₂Hom (Rat.castHom ℝ)
        (fun a : Fin 2 => if a = 0 then s else t) (binomialLogCoeff ((v i).val + 1))) *
      (1 / (N : ℝ)) ^ binomialCompositionOrder v| ≤
    (∏ i : Fin k, (binomialLogCoeffMajorant ((v i).val + 1) : ℝ)) *
      (B ^ 2 / (N : ℝ)) ^ binomialCompositionOrder v := by
  classical
  calc
    _ = |∏ i : Fin k, eval₂Hom (Rat.castHom ℝ)
          (fun a : Fin 2 => if a = 0 then s else t) (binomialLogCoeff ((v i).val + 1)) *
          (1 / (N : ℝ)) ^ ((v i).val + 1)| := by
      congr 1
      rw [prod_mul_distrib, prod_pow_eq_pow_sum]
      rfl
    _ = ∏ i : Fin k, |eval₂Hom (Rat.castHom ℝ)
          (fun a : Fin 2 => if a = 0 then s else t) (binomialLogCoeff ((v i).val + 1)) *
          (1 / (N : ℝ)) ^ ((v i).val + 1)| := abs_prod _ _
    _ ≤ ∏ i : Fin k, (binomialLogCoeffMajorant ((v i).val + 1) : ℝ) *
          (B ^ 2 / (N : ℝ)) ^ ((v i).val + 1) :=
      prod_le_prod (fun i hi => abs_nonneg _) (fun i hi =>
        binomialLogCoeff_reciprocal_majorant _ N (by omega) hN s t B hB hs ht)
    _ = _ := by rw [prod_mul_distrib, prod_pow_eq_pow_sum]; rfl

theorem binomialExpDropped_le (K N : ℕ) (hN : 1 ≤ N) (s t B : ℝ)
    (hB : 1 ≤ B) (hs : |s| ≤ 2 * B) (ht : |t| ≤ 2 * B)
    (hz : B ^ 2 / (N : ℝ) ≤ 1) :
    |binomialExpDropped K s t (1 / (N : ℝ))| ≤
      (binomialExpDroppedMajorant K : ℝ) * (B ^ 2 / (N : ℝ)) ^ (K + 1) := by
  classical
  let z := B ^ 2 / (N : ℝ)
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hz0 : 0 ≤ z := div_nonneg (sq_nonneg B) hNr.le
  have hA (i : ℕ) : (0 : ℝ) ≤ (binomialLogCoeffMajorant i : ℝ) := by
    exact_mod_cast binomialLogCoeffMajorant_nonneg i
  have hprod (k : ℕ) (v : Fin k → Fin K) :
      (0 : ℝ) ≤ ∏ i : Fin k, (binomialLogCoeffMajorant ((v i).val + 1) : ℝ) :=
    prod_nonneg fun i hi => hA _
  have hsumA : (∑ i : Fin K, (binomialLogCoeffMajorant (i.val + 1) : ℝ)) =
      (binomialLogPrefixMajorant K : ℝ) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => (binomialLogCoeffMajorant (i + 1) : ℝ)) K,
      range_succ_sum_Icc K (fun i => (binomialLogCoeffMajorant i : ℝ))]
    exact (binomialLogPrefixMajorant_cast K).symm
  have hinner (k : ℕ) :
      |∑ v ∈ (univ : Finset (Fin k → Fin K)).filter (fun v => K < binomialCompositionOrder v),
        (∏ i : Fin k, eval₂Hom (Rat.castHom ℝ)
          (fun a : Fin 2 => if a = 0 then s else t) (binomialLogCoeff ((v i).val + 1))) *
          (1 / (N : ℝ)) ^ binomialCompositionOrder v| ≤
      (binomialLogPrefixMajorant K : ℝ) ^ k * z ^ (K + 1) := by
    calc
      _ ≤ ∑ v ∈ (univ : Finset (Fin k → Fin K)).filter (fun v => K < binomialCompositionOrder v),
          |(∏ i : Fin k, eval₂Hom (Rat.castHom ℝ)
            (fun a : Fin 2 => if a = 0 then s else t) (binomialLogCoeff ((v i).val + 1))) *
            (1 / (N : ℝ)) ^ binomialCompositionOrder v| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ v ∈ (univ : Finset (Fin k → Fin K)).filter (fun v => K < binomialCompositionOrder v),
          (∏ i : Fin k, (binomialLogCoeffMajorant ((v i).val + 1) : ℝ)) * z ^ (K + 1) := by
        apply sum_le_sum
        intro v hv
        have horder : K + 1 ≤ binomialCompositionOrder v := by have := (mem_filter.mp hv).2; omega
        exact (binomialComposition_eval_majorant K k N hN v s t B hB hs ht).trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hz0 hz horder) (hprod k v))
      _ ≤ ∑ v : Fin k → Fin K,
          (∏ i : Fin k, (binomialLogCoeffMajorant ((v i).val + 1) : ℝ)) * z ^ (K + 1) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun v hv hnot =>
          mul_nonneg (hprod k v) (pow_nonneg hz0 _))
      _ = _ := by
        rw [← sum_mul]
        have hp := Fintype.sum_pow (fun a : Fin K => (binomialLogCoeffMajorant (a.val + 1) : ℝ)) k
        rw [hsumA] at hp
        rw [← hp]
  unfold binomialExpDropped
  calc
    _ ≤ ∑ k ∈ range (K + 1), |(1 / (k.factorial : ℝ)) *
        ∑ v ∈ (univ : Finset (Fin k → Fin K)).filter (fun v => K < binomialCompositionOrder v),
          (∏ i : Fin k, eval₂Hom (Rat.castHom ℝ)
            (fun a : Fin 2 => if a = 0 then s else t) (binomialLogCoeff ((v i).val + 1))) *
            (1 / (N : ℝ)) ^ binomialCompositionOrder v| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ range (K + 1), (1 / (k.factorial : ℝ)) *
        ((binomialLogPrefixMajorant K : ℝ) ^ k * z ^ (K + 1)) := by
      apply sum_le_sum
      intro k hk
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (k.factorial : ℝ))]
      exact mul_le_mul_of_nonneg_left (hinner k) (by positivity)
    _ = _ := by
      rw [binomialExpDroppedMajorant_cast, sum_mul]
      apply sum_congr rfl
      intro k hk
      dsimp only [z]
      ring

theorem uniform_normalizedBinomialMass_exp_window (C : ℝ) (hC : 0 < C) (K : ℕ) :
    ∃ N0 : ℕ, 4 ≤ N0 ∧ ∀ N ≥ N0, ∀ L a b j : ℕ,
      b < a → a ≤ L → (L : ℝ) ≤ C * Real.log (N : ℝ) →
      j ∈ Ico (N - a) (N - b) →
      let m := (N - a) + (N - b)
      let s : ℝ := (a : ℝ) + (b : ℝ)
      let t : ℝ := (j : ℝ) - (m : ℝ) / 2
      |Real.sqrt (Real.pi * (N : ℝ)) * binomialMass m j -
        (∑ n ∈ Icc 0 K, eval₂Hom (Rat.castHom ℝ)
          (fun i : Fin 2 => if i = 0 then s else t) (binomialExpCoeff n) / (N : ℝ) ^ n)| ≤
        binomialExpWindowConstant K * (1 + (L : ℝ)) ^ (2 * K + 2) / (N : ℝ) ^ (K + 1) := by
  classical
  let A : ℝ := (binomialLogPrefixMajorant K : ℝ)
  let D : ℝ := (binomialExpLogErrorConstant K : ℝ)
  have hA : 0 ≤ A := by dsimp only [A]; exact_mod_cast binomialLogPrefixMajorant_nonneg K
  have hD : 0 ≤ D := by dsimp only [D]; exact_mod_cast binomialExpLogErrorConstant_nonneg K
  let δ : ℝ := 1 / (1 + A + D)
  have hden : 0 < 1 + A + D := by positivity
  have hδ : 0 < δ := one_div_pos.mpr hden
  have hδ1 : δ ≤ 1 := by
    apply (div_le_iff₀ hden).mpr
    linarith only [hA, hD]
  obtain ⟨NL, hNL4, hlog⟩ := uniform_normalizedBinomialLog_coeff_window C hC
  obtain ⟨NG, hNG2, hgeo⟩ := logWindow_eventually_below_half C
  obtain ⟨M, hsmall⟩ := eventually_atTop.mp
    ((tendsto_order.mp (logWindow_error_tendsto C)).2 (2 * δ) (by positivity))
  refine ⟨max NL (max NG (max 4 M)), le_trans hNL4 (le_max_left _ _), ?_⟩
  intro N hN L a b j hba haL hL hj
  have hNL : NL ≤ N := le_trans (le_max_left _ _) hN
  have hNG : NG ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hN)
  have hNM : M ≤ N := le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN))
  have hN4 : 4 ≤ N := le_trans hNL4 hNL
  have hN1 : 1 ≤ N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hhalf : 2 * (L : ℝ) < (N : ℝ) := by linarith only [hgeo N hNG, hL]
  let m := (N - a) + (N - b)
  let s : ℝ := (a : ℝ) + (b : ℝ)
  let t : ℝ := (j : ℝ) - (m : ℝ) / 2
  let B : ℝ := 1 + (L : ℝ)
  let z : ℝ := B ^ 2 / (N : ℝ)
  let x : ℝ := Real.log (Real.sqrt (Real.pi * (N : ℝ)) * binomialMass m j)
  let u : ℝ := ∑ i ∈ Icc 1 K, eval₂Hom (Rat.castHom ℝ)
    (fun q : Fin 2 => if q = 0 then s else t) (binomialLogCoeff i) / (N : ℝ) ^ i
  let P : ℝ := ∑ k ∈ range (K + 1), u ^ k / (k.factorial : ℝ)
  obtain ⟨ha, hb, hjpos, hjm, hqpos, hqlo, hqhi, hmR, hjR, hqR, hs0, hsL, htL, hjshift, hqshift⟩ :=
    binomialSharpShift_geometry N L a b j hN4 hba haL hhalf hj
  have hB : 1 ≤ B := by
    have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    dsimp only [B]
    linarith only [hL0]
  have hs : |s| ≤ 2 * B := by rw [abs_of_nonneg hs0]; dsimp only [B]; linarith only [hsL]
  have ht : |t| ≤ 2 * B := by dsimp only [B]; linarith only [htL, (show (0 : ℝ) ≤ (L : ℝ) from Nat.cast_nonneg L)]
  have hz0 : 0 ≤ z := div_nonneg (sq_nonneg B) hNr.le
  have hBup : B ≤ C * Real.log (N : ℝ) + 1 := by dsimp only [B]; linarith only [hL]
  have hsq := pow_le_pow_left₀ (le_trans (by norm_num) hB) hBup 2
  have hzδ : z < δ := by
    have hh := hsmall N hNM
    have hcomp : 2 * B ^ 2 / (N : ℝ) ≤
        2 * (C * Real.log (N : ℝ) + 1) ^ 2 / (N : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num)) hNr.le
    have hcomp' : 2 * z ≤ 2 * (C * Real.log (N : ℝ) + 1) ^ 2 / (N : ℝ) := by
      simpa only [z, mul_div_assoc] using hcomp
    linarith only [hh, hcomp']
  have hz : z ≤ 1 := le_trans hzδ.le hδ1
  have hu : |u| ≤ A * z := binomialLogPrefix_eval_majorant K N hN1 s t B hB hs ht hz
  have herror : |x - u| ≤ D * B ^ (K + 2) / (N : ℝ) ^ (K + 1) := by
    simpa only [x, u, D, B, m, s, t, binomialExpLogErrorConstant_cast] using
      hlog N hNL L a b j K hba haL hL hj
  have hpow : B ^ (K + 2) ≤ B ^ (2 * (K + 1)) := pow_le_pow_right₀ hB (by omega)
  have herrz : |x - u| ≤ D * z ^ (K + 1) := by
    calc
      _ ≤ D * B ^ (K + 2) / (N : ℝ) ^ (K + 1) := herror
      _ ≤ D * B ^ (2 * (K + 1)) / (N : ℝ) ^ (K + 1) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hD) (pow_nonneg hNr.le _)
      _ = _ := by dsimp only [z]; rw [div_pow, pow_mul]; ring
  have hzp : z ^ (K + 1) ≤ z := by
    simpa only [pow_one] using pow_le_pow_of_le_one hz0 hz (show 1 ≤ K + 1 by omega)
  have herrlin : |x - u| ≤ D * z := herrz.trans (mul_le_mul_of_nonneg_left hzp hD)
  have hsmallprod : z * (1 + A + D) < 1 := (lt_div_iff₀ hden).mp hzδ
  have hu1 : |u| ≤ 1 := by
    apply hu.trans
    calc
      A * z ≤ A * z + (z + D * z) := le_add_of_nonneg_right (add_nonneg hz0 (mul_nonneg hD hz0))
      _ = z * (1 + A + D) := by ring
      _ ≤ 1 := hsmallprod.le
  have hxbound : |x| ≤ D * z + A * z := by
    calc
      _ = |(x - u) + u| := by congr 1; ring
      _ ≤ |x - u| + |u| := abs_add _ _
      _ ≤ _ := add_le_add herrlin hu
  have hx1 : |x| ≤ 1 := by
    apply hxbound.trans
    calc
      D * z + A * z ≤ z + (D * z + A * z) := le_add_of_nonneg_left hz0
      _ = z * (1 + A + D) := by ring
      _ ≤ 1 := hsmallprod.le
  have hE1 : |Real.exp x - Real.exp u| ≤ Real.exp 1 * D * z ^ (K + 1) :=
    (binomial_exp_sub_exp_le x u hx1 hu1).trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left herrz (Real.exp_pos 1).le)
  have hfac : (0 : ℝ) < ((K + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (K + 1)
  have hup : |u| ^ (K + 1) ≤ (A * z) ^ (K + 1) :=
    pow_le_pow_left₀ (abs_nonneg u) hu _
  have hE2 : |Real.exp u - P| ≤
      (Real.exp 1 * A ^ (K + 1) / ((K + 1).factorial : ℝ)) * z ^ (K + 1) := by
    calc
      _ ≤ Real.exp 1 * |u| ^ (K + 1) / ((K + 1).factorial : ℝ) :=
        binomial_exp_taylor_bound K u hu1
      _ ≤ Real.exp 1 * (A * z) ^ (K + 1) / ((K + 1).factorial : ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hup (Real.exp_pos 1).le) hfac.le
      _ = _ := by rw [mul_pow]; ring
  have hE3 := binomialExpDropped_le K N hN1 s t B hB hs ht hz
  have hfinite : P =
      (∑ n ∈ Icc 0 K, eval₂Hom (Rat.castHom ℝ)
        (fun i : Fin 2 => if i = 0 then s else t) (binomialExpCoeff n) / (N : ℝ) ^ n) +
          binomialExpDropped K s t (1 / (N : ℝ)) := by
    simpa only [P, u, div_pow, one_pow, mul_one_div] using
      binomialExp_finite_collection K s t (1 / (N : ℝ))
  have hmass : 0 < Real.sqrt (Real.pi * (N : ℝ)) * binomialMass m j :=
    mul_pos (Real.sqrt_pos.mpr (mul_pos Real.pi_pos hNr)) (binomialMass_pos_of_le m j hjm.le)
  have hexp : Real.exp x = Real.sqrt (Real.pi * (N : ℝ)) * binomialMass m j :=
    Real.exp_log hmass
  change |Real.sqrt (Real.pi * (N : ℝ)) * binomialMass m j -
    (∑ n ∈ Icc 0 K, eval₂Hom (Rat.castHom ℝ)
      (fun i : Fin 2 => if i = 0 then s else t) (binomialExpCoeff n) / (N : ℝ) ^ n)| ≤ _
  calc
    _ = |(Real.exp x - Real.exp u) + (Real.exp u - P) +
        binomialExpDropped K s t (1 / (N : ℝ))| := by
      rw [hexp, hfinite]
      congr 1
      ring
    _ ≤ |Real.exp x - Real.exp u| + |Real.exp u - P| +
        |binomialExpDropped K s t (1 / (N : ℝ))| :=
      (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)
    _ ≤ (Real.exp 1 * D * z ^ (K + 1)) +
        ((Real.exp 1 * A ^ (K + 1) / ((K + 1).factorial : ℝ)) * z ^ (K + 1)) +
          ((binomialExpDroppedMajorant K : ℝ) * z ^ (K + 1)) :=
      add_le_add (add_le_add hE1 hE2) hE3
    _ = binomialExpWindowConstant K * B ^ (2 * K + 2) / (N : ℝ) ^ (K + 1) := by
      dsimp only [binomialExpWindowConstant, A, D, z]
      rw [show 2 * K + 2 = 2 * (K + 1) by omega]
      simp only [div_pow, pow_mul]
      ring

end Hardinian
