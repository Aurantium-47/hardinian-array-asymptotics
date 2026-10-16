import Hardinian.BinomialExponentialWindow

namespace Hardinian

open Finset MvPolynomial

noncomputable def orderedBinomialKernelCoeff (n a b : ℕ) : ℚ :=
  ∑ v ∈ range (a - b),
    eval₂Hom (RingHom.id ℚ)
      (fun i : Fin 2 => if i = 0 then (a : ℚ) + (b : ℚ)
        else (v : ℚ) - ((a - b : ℕ) : ℚ) / 2)
      (binomialExpCoeff n)

theorem orderedBinomialKernelCoeff_cast (n a b : ℕ) :
    (orderedBinomialKernelCoeff n a b : ℝ) =
      ∑ v ∈ range (a - b),
        eval₂Hom (Rat.castHom ℝ)
          (fun i : Fin 2 => if i = 0 then (a : ℝ) + (b : ℝ)
            else (v : ℝ) - ((a - b : ℕ) : ℝ) / 2)
          (binomialExpCoeff n) := by
  classical
  change (Rat.castHom ℝ) (orderedBinomialKernelCoeff n a b) = _
  unfold orderedBinomialKernelCoeff
  rw [map_sum]
  apply sum_congr rfl
  intro v hv
  rw [MvPolynomial.map_eval₂Hom, RingHom.comp_id]
  have hval :
      (fun i : Fin 2 => (Rat.castHom ℝ)
        (if i = 0 then (a : ℚ) + (b : ℚ) else (v : ℚ) - ((a - b : ℕ) : ℚ) / 2)) =
      (fun i : Fin 2 => if i = 0 then (a : ℝ) + (b : ℝ)
        else (v : ℝ) - ((a - b : ℕ) : ℝ) / 2) := by
    funext i
    split_ifs <;> norm_num
  rw [hval]

theorem orderedBinomialKernelCoeff_zero (a b : ℕ) :
    orderedBinomialKernelCoeff 0 a b = ((a - b : ℕ) : ℚ) := by
  classical
  simp [orderedBinomialKernelCoeff, binomialExpCoeff_zero, sum_const, nsmul_eq_mul]

theorem orderedBinomialKernelCoeff_zero_ordered (a b : ℕ) (hba : b ≤ a) :
    orderedBinomialKernelCoeff 0 a b = (a : ℚ) - (b : ℚ) := by
  rw [orderedBinomialKernelCoeff_zero, Nat.cast_sub hba]

theorem orderedBinomialKernelCoeff_diagonal (n a : ℕ) :
    orderedBinomialKernelCoeff n a a = 0 := by
  simp [orderedBinomialKernelCoeff]

theorem orderedKernel_diagonal (u : ℕ) : binomialKernel u u = 0 := by
  simp [binomialKernel, Ico_self]

theorem orderedKernel_reverse_empty (u v : ℕ) (hvu : v ≤ u) : binomialKernel u v = 0 := by
  simp [binomialKernel, Ico_eq_empty_of_le hvu]

theorem orderedKernel_width (N a b : ℕ) (ha : a ≤ N) (hba : b ≤ a) :
    (N - b) - (N - a) = a - b ∧ (N - a) + (a - b) = N - b := by
  omega

theorem orderedKernel_shift_mem (N a b v : ℕ) (ha : a ≤ N) (hba : b ≤ a)
    (hv : v ∈ range (a - b)) : N - a + v ∈ Ico (N - a) (N - b) := by
  simp only [mem_range] at hv
  simp only [mem_Ico]
  omega

theorem orderedKernel_shift_inverse (N a b j : ℕ) (ha : a ≤ N) (hba : b ≤ a)
    (hj : j ∈ Ico (N - a) (N - b)) :
    j - (N - a) ∈ range (a - b) ∧ N - a + (j - (N - a)) = j := by
  simp only [mem_Ico] at hj
  simp only [mem_range]
  omega

theorem orderedKernel_unshift_shift (N a v : ℕ) :
    (N - a + v) - (N - a) = v := by omega

theorem orderedKernel_shift_center (N a b v : ℕ) (ha : a ≤ N) (hba : b ≤ a) :
    ((N - a + v : ℕ) : ℝ) - (((N - a) + (N - b) : ℕ) : ℝ) / 2 =
      (v : ℝ) - ((a - b : ℕ) : ℝ) / 2 := by
  have hb : b ≤ N := hba.trans ha
  simp only [Nat.cast_add, Nat.cast_sub ha, Nat.cast_sub hb, Nat.cast_sub hba]
  ring

theorem orderedBinomialKernelCoeff_interval_sum (N a b n : ℕ)
    (ha : a ≤ N) (hba : b ≤ a) :
    (∑ j ∈ Ico (N - a) (N - b),
      eval₂Hom (Rat.castHom ℝ)
        (fun i : Fin 2 => if i = 0 then (a : ℝ) + (b : ℝ)
          else (j : ℝ) - (((N - a) + (N - b) : ℕ) : ℝ) / 2)
        (binomialExpCoeff n)) = (orderedBinomialKernelCoeff n a b : ℝ) := by
  classical
  rw [orderedBinomialKernelCoeff_cast]
  refine sum_bij' (fun j hj => j - (N - a)) (fun v hv => N - a + v) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    exact (orderedKernel_shift_inverse N a b j ha hba hj).1
  · intro v hv
    exact orderedKernel_shift_mem N a b v ha hba hv
  · intro j hj
    exact (orderedKernel_shift_inverse N a b j ha hba hj).2
  · intro v hv
    exact orderedKernel_unshift_shift N a v
  · intro j hj
    have hc := orderedKernel_shift_center N a b (j - (N - a)) ha hba
    rw [(orderedKernel_shift_inverse N a b j ha hba hj).2] at hc
    rw [hc]

theorem orderedBinomialKernelCoeff_finite_sum (N a b K : ℕ)
    (ha : a ≤ N) (hba : b ≤ a) :
    (∑ j ∈ Ico (N - a) (N - b),
      ∑ n ∈ Icc 0 K, eval₂Hom (Rat.castHom ℝ)
        (fun i : Fin 2 => if i = 0 then (a : ℝ) + (b : ℝ)
          else (j : ℝ) - (((N - a) + (N - b) : ℕ) : ℝ) / 2)
        (binomialExpCoeff n) / (N : ℝ) ^ n) =
      ∑ n ∈ Icc 0 K, (orderedBinomialKernelCoeff n a b : ℝ) / (N : ℝ) ^ n := by
  classical
  rw [sum_comm]
  apply sum_congr rfl
  intro n hn
  rw [← sum_div, orderedBinomialKernelCoeff_interval_sum N a b n ha hba]

theorem orderedKernel_discrepancy_sum (N a b K : ℕ) (ha : a ≤ N) (hba : b ≤ a) :
    Real.sqrt (Real.pi * (N : ℝ)) * binomialKernel (N - a) (N - b) -
      (∑ n ∈ Icc 0 K, (orderedBinomialKernelCoeff n a b : ℝ) / (N : ℝ) ^ n) =
    ∑ j ∈ Ico (N - a) (N - b),
      (Real.sqrt (Real.pi * (N : ℝ)) * binomialMass ((N - a) + (N - b)) j -
        ∑ n ∈ Icc 0 K, eval₂Hom (Rat.castHom ℝ)
          (fun i : Fin 2 => if i = 0 then (a : ℝ) + (b : ℝ)
            else (j : ℝ) - (((N - a) + (N - b) : ℕ) : ℝ) / 2)
          (binomialExpCoeff n) / (N : ℝ) ^ n) := by
  rw [sum_sub_distrib, orderedBinomialKernelCoeff_finite_sum N a b K ha hba]
  rw [binomialKernel, mul_sum]

theorem uniform_orderedBinomialKernel_expansion (C : ℝ) (hC : 0 < C) (K : ℕ) :
    ∃ N0 : ℕ, 4 ≤ N0 ∧ ∀ N ≥ N0, ∀ L a b : ℕ,
      b < a → a ≤ L → (L : ℝ) ≤ C * Real.log (N : ℝ) →
      let err := |Real.sqrt (Real.pi * (N : ℝ)) * binomialKernel (N - a) (N - b) -
        (∑ n ∈ Icc 0 K, (orderedBinomialKernelCoeff n a b : ℝ) / (N : ℝ) ^ n)|
      err ≤ ((a - b : ℕ) : ℝ) * binomialExpWindowConstant K *
        (1 + (L : ℝ)) ^ (2 * K + 2) / (N : ℝ) ^ (K + 1) ∧
      err ≤ binomialExpWindowConstant K *
        (1 + (L : ℝ)) ^ (2 * K + 3) / (N : ℝ) ^ (K + 1) := by
  classical
  obtain ⟨NM, hNM4, hmass⟩ := uniform_normalizedBinomialMass_exp_window C hC K
  obtain ⟨NG, hNG2, hgeo⟩ := logWindow_eventually_below_half C
  refine ⟨max NM NG, le_trans hNM4 (le_max_left _ _), ?_⟩
  intro N hN L a b hba haL hL
  have hNM : NM ≤ N := le_trans (le_max_left _ _) hN
  have hNG : NG ≤ N := le_trans (le_max_right _ _) hN
  have hN4 : 4 ≤ N := hNM4.trans hNM
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hhalf : 2 * (L : ℝ) < (N : ℝ) := by linarith only [hgeo N hNG, hL]
  have hLN : L ≤ N := by
    have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    exact_mod_cast (show (L : ℝ) ≤ (N : ℝ) by linarith only [hhalf, hL0])
  have ha : a ≤ N := haL.trans hLN
  have hwidth := (orderedKernel_width N a b ha hba.le).1
  let B : ℝ := 1 + (L : ℝ)
  let ε : ℝ := binomialExpWindowConstant K * B ^ (2 * K + 2) / (N : ℝ) ^ (K + 1)
  let err := |Real.sqrt (Real.pi * (N : ℝ)) * binomialKernel (N - a) (N - b) -
    (∑ n ∈ Icc 0 K, (orderedBinomialKernelCoeff n a b : ℝ) / (N : ℝ) ^ n)|
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hε : 0 ≤ ε := div_nonneg
    (mul_nonneg (binomialExpWindowConstant_nonneg K) (pow_nonneg hB _)) (pow_nonneg hNr.le _)
  have hsharp : err ≤ ((a - b : ℕ) : ℝ) * ε := by
    dsimp only [err]
    rw [orderedKernel_discrepancy_sum N a b K ha hba.le]
    calc
      _ ≤ ∑ j ∈ Ico (N - a) (N - b),
          |Real.sqrt (Real.pi * (N : ℝ)) * binomialMass ((N - a) + (N - b)) j -
            ∑ n ∈ Icc 0 K, eval₂Hom (Rat.castHom ℝ)
              (fun i : Fin 2 => if i = 0 then (a : ℝ) + (b : ℝ)
                else (j : ℝ) - (((N - a) + (N - b) : ℕ) : ℝ) / 2)
              (binomialExpCoeff n) / (N : ℝ) ^ n| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Ico (N - a) (N - b), ε := by
        apply sum_le_sum
        intro j hj
        exact hmass N hNM L a b j hba haL hL hj
      _ = _ := by simp only [sum_const, Nat.card_Ico, hwidth, nsmul_eq_mul]
  change err ≤ ((a - b : ℕ) : ℝ) * binomialExpWindowConstant K *
      B ^ (2 * K + 2) / (N : ℝ) ^ (K + 1) ∧
    err ≤ binomialExpWindowConstant K * B ^ (2 * K + 3) / (N : ℝ) ^ (K + 1)
  constructor
  · simpa only [ε, mul_div_assoc, mul_assoc] using hsharp
  · have hdL : ((a - b : ℕ) : ℝ) ≤ (L : ℝ) := by
      exact_mod_cast ((Nat.sub_le a b).trans haL)
    have hdB : ((a - b : ℕ) : ℝ) ≤ B := by dsimp only [B]; linarith only [hdL]
    calc
      err ≤ ((a - b : ℕ) : ℝ) * ε := hsharp
      _ ≤ B * ε := mul_le_mul_of_nonneg_right hdB hε
      _ = _ := by
        dsimp only [ε]
        rw [show 2 * K + 3 = (2 * K + 2) + 1 by omega, pow_succ]
        ring

end Hardinian
