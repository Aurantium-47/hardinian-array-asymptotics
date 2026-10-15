import Hardinian.StirlingIncrementPowers
import Hardinian.InversePowerDifferences
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.BigOperators

namespace Hardinian

open scoped BigOperators

def stirlingCorrectionCoeff : ℕ → ℚ :=
  WellFounded.fix Nat.lt_wfRel.wf fun n rec =>
    (stirlingIncrementCoeff n -
      ∑ i : Fin n, rec i i.2 * (-1 : ℚ) ^ (n - (i : ℕ)) *
        (Nat.choose (n + 1) (i : ℕ) : ℚ)) / ((n : ℚ) + 1)

theorem stirlingCorrectionCoeff_fin_eq (n : ℕ) :
    stirlingCorrectionCoeff n =
      (stirlingIncrementCoeff n -
        ∑ i : Fin n, stirlingCorrectionCoeff i * (-1 : ℚ) ^ (n - (i : ℕ)) *
          (Nat.choose (n + 1) (i : ℕ) : ℚ)) / ((n : ℚ) + 1) :=
  WellFounded.fix_eq _ _ _

theorem stirlingCorrectionCoeff_eq (n : ℕ) :
    stirlingCorrectionCoeff n =
      (stirlingIncrementCoeff n -
        ∑ i ∈ Finset.range n, stirlingCorrectionCoeff i * (-1 : ℚ) ^ (n - i) *
          (Nat.choose (n + 1) i : ℚ)) / ((n : ℚ) + 1) := by
  rw [stirlingCorrectionCoeff_fin_eq, ← Fin.sum_univ_eq_sum_range]

theorem stirlingCorrectionCoeff_zero : stirlingCorrectionCoeff 0 = 1 / 12 := by
  rw [stirlingCorrectionCoeff_eq]
  norm_num [stirlingIncrementCoeff]

theorem stirlingCorrectionCoeff_one : stirlingCorrectionCoeff 1 = 0 := by
  rw [stirlingCorrectionCoeff_eq]
  norm_num [stirlingIncrementCoeff, Finset.sum_range_succ, stirlingCorrectionCoeff_zero]

theorem stirlingCorrectionCoeff_two : stirlingCorrectionCoeff 2 = -1 / 360 := by
  rw [stirlingCorrectionCoeff_eq]
  norm_num [stirlingIncrementCoeff, Finset.sum_range_succ,
    stirlingCorrectionCoeff_zero, stirlingCorrectionCoeff_one]

theorem stirlingCorrectionCoeff_matching (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1),
      stirlingCorrectionCoeff i * (-1 : ℚ) ^ (n - i) * (Nat.choose (n + 1) i : ℚ)) =
      stirlingIncrementCoeff n := by
  have hd : (n : ℚ) + 1 ≠ 0 := by positivity
  rw [Finset.sum_range_succ]
  simp only [Nat.sub_self, pow_zero, mul_one, Nat.choose_succ_self_right,
    Nat.cast_add, Nat.cast_one]
  rw [stirlingCorrectionCoeff_eq n, div_mul_cancel₀ _ hd]
  ring

theorem inversePowerDifferenceCoeff_reindexed (n i : ℕ) (hi : i ≤ n) :
    inversePowerDifferenceCoeff i (n - i) =
      (-1 : ℚ) ^ (n - i) * (Nat.choose (n + 1) i : ℚ) := by
  unfold inversePowerDifferenceCoeff
  rw [show i + (n - i) + 1 = n + 1 by omega]
  congr 1
  exact_mod_cast (Nat.choose_symm_of_eq_add (a := n - i + 1) (b := i) (by omega))

theorem stirlingCorrectionCoeff_matching_beta (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1),
      stirlingCorrectionCoeff i * inversePowerDifferenceCoeff i (n - i)) =
      stirlingIncrementCoeff n := by
  calc
    _ = ∑ i ∈ Finset.range (n + 1),
        stirlingCorrectionCoeff i * (-1 : ℚ) ^ (n - i) * (Nat.choose (n + 1) i : ℚ) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [inversePowerDifferenceCoeff_reindexed n i (by
        have := Finset.mem_range.mp hi
        omega)]
      ring
    _ = _ := stirlingCorrectionCoeff_matching n

theorem stirlingCorrectionCoeff_matching_real (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1),
      (stirlingCorrectionCoeff i : ℝ) * (inversePowerDifferenceCoeff i (n - i) : ℝ)) =
      (stirlingIncrementCoeff n : ℝ) := by
  exact_mod_cast stirlingCorrectionCoeff_matching_beta n

noncomputable def stirlingCorrectionPrefix (N J : ℕ) : ℝ :=
  ∑ i ∈ Finset.range J, (stirlingCorrectionCoeff i : ℝ) / (N : ℝ) ^ (i + 1)

def stirlingResidualConstant (J : ℕ) : ℚ :=
  (J : ℚ) + 3 + ∑ i ∈ Finset.range J,
    |stirlingCorrectionCoeff i| * (2 : ℚ) ^ i * (Nat.choose (J + 1) i : ℚ)

theorem stirlingResidualConstant_nonneg (J : ℕ) : 0 ≤ stirlingResidualConstant J := by
  unfold stirlingResidualConstant
  positivity

theorem stirlingResidualConstant_cast (J : ℕ) :
    (stirlingResidualConstant J : ℝ) = (J : ℝ) + 3 +
      ∑ i ∈ Finset.range J, |(stirlingCorrectionCoeff i : ℝ)| *
        (2 : ℝ) ^ i * (Nat.choose (J + 1) i : ℝ) := by
  norm_num [stirlingResidualConstant]

/-- The finite triangular reindexing, with all subtraction bounds derived from membership. -/
theorem stirling_triangle_sum (J : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ i ∈ Finset.range J, ∑ j ∈ Finset.range (J - i), f i j) =
      ∑ n ∈ Finset.range J, ∑ i ∈ Finset.range (n + 1), f i (n - i) := by
  classical
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij (fun a ha => (⟨a.1 + a.2, a.1⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_sigma, Finset.mem_range] at ha ⊢
    omega
  · rintro ⟨i, j⟩ ha ⟨i', j'⟩ hb h
    have hs := congrArg Sigma.fst h
    have hi := congrArg (fun z : (Σ _ : ℕ, ℕ) => z.2) h
    dsimp at hs hi
    have hj : j = j' := by omega
    subst i'
    subst j'
    rfl
  · rintro ⟨n, i⟩ hb
    simp only [Finset.mem_sigma, Finset.mem_range] at hb
    refine ⟨⟨i, n - i⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_range]
      omega
    · change (⟨i + (n - i), i⟩ : Σ _ : ℕ, ℕ) = ⟨n, i⟩
      rw [show i + (n - i) = n by omega]
  · intro a ha
    dsimp
    rw [Nat.add_sub_cancel_left]

theorem stirlingCorrection_matching_polynomial (N J : ℕ) :
    (∑ i ∈ Finset.range J, (stirlingCorrectionCoeff i : ℝ) *
      (∑ j ∈ Finset.range (J - i),
        (inversePowerDifferenceCoeff i j : ℝ) / (N : ℝ) ^ (i + j + 2))) =
      ∑ n ∈ Finset.range J, (stirlingIncrementCoeff n : ℝ) / (N : ℝ) ^ (n + 2) := by
  calc
    _ = ∑ i ∈ Finset.range J, ∑ j ∈ Finset.range (J - i),
        ((stirlingCorrectionCoeff i : ℝ) * (inversePowerDifferenceCoeff i j : ℝ)) /
          (N : ℝ) ^ (i + j + 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [div_eq_mul_inv]
      ring
    _ = ∑ n ∈ Finset.range J, ∑ i ∈ Finset.range (n + 1),
        ((stirlingCorrectionCoeff i : ℝ) * (inversePowerDifferenceCoeff i (n - i) : ℝ)) /
          (N : ℝ) ^ (i + (n - i) + 2) := stirling_triangle_sum J _
    _ = ∑ n ∈ Finset.range J,
        (∑ i ∈ Finset.range (n + 1),
          (stirlingCorrectionCoeff i : ℝ) * (inversePowerDifferenceCoeff i (n - i) : ℝ)) /
            (N : ℝ) ^ (n + 2) := by
      apply Finset.sum_congr rfl
      intro n hn
      calc
        _ = ∑ i ∈ Finset.range (n + 1),
            ((stirlingCorrectionCoeff i : ℝ) * (inversePowerDifferenceCoeff i (n - i) : ℝ)) /
              (N : ℝ) ^ (n + 2) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [show i + (n - i) + 2 = n + 2 by
            have := Finset.mem_range.mp hi
            omega]
        _ = _ := by simp only [div_eq_mul_inv, Finset.sum_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [stirlingCorrectionCoeff_matching_real]

theorem stirlingCorrectionDifference_sum (N J : ℕ) :
    stirlingCorrectionPrefix N J - stirlingCorrectionPrefix (N + 1) J =
      ∑ i ∈ Finset.range J, (stirlingCorrectionCoeff i : ℝ) *
        (1 / (N : ℝ) ^ (i + 1) - 1 / ((N : ℝ) + 1) ^ (i + 1)) := by
  unfold stirlingCorrectionPrefix
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  push_cast
  simp only [div_eq_mul_inv]
  ring

theorem stirlingCorrection_slice_error (N J i : ℕ) (hN : 1 ≤ N) (hi : i < J) :
    |(stirlingCorrectionCoeff i : ℝ) *
      ((1 / (N : ℝ) ^ (i + 1) - 1 / ((N : ℝ) + 1) ^ (i + 1)) -
        ∑ j ∈ Finset.range (J - i),
          (inversePowerDifferenceCoeff i j : ℝ) / (N : ℝ) ^ (i + j + 2))| ≤
      (|(stirlingCorrectionCoeff i : ℝ)| * (2 : ℝ) ^ i *
        (Nat.choose (J + 1) i : ℝ)) / (N : ℝ) ^ (J + 2) := by
  have hb := inversePowerDifference_error N i (J - i) hN
  rw [show J - i + i + 1 = J + 1 by omega,
    show i + (J - i) + 2 = J + 2 by omega] at hb
  rw [abs_mul]
  calc
    _ ≤ |(stirlingCorrectionCoeff i : ℝ)| *
        (((2 : ℝ) ^ i * (Nat.choose (J + 1) i : ℝ)) / (N : ℝ) ^ (J + 2)) :=
      mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ = _ := by simp only [div_eq_mul_inv]; ring

theorem stirlingCorrection_delta_error (N J : ℕ) (hN : 1 ≤ N) :
    |(stirlingCorrectionPrefix N J - stirlingCorrectionPrefix (N + 1) J) -
        ∑ n ∈ Finset.range J, (stirlingIncrementCoeff n : ℝ) / (N : ℝ) ^ (n + 2)| ≤
      (∑ i ∈ Finset.range J, |(stirlingCorrectionCoeff i : ℝ)| *
        (2 : ℝ) ^ i * (Nat.choose (J + 1) i : ℝ)) / (N : ℝ) ^ (J + 2) := by
  rw [stirlingCorrectionDifference_sum, ← stirlingCorrection_matching_polynomial N J,
    ← Finset.sum_sub_distrib]
  have heq : (∑ i ∈ Finset.range J,
      ((stirlingCorrectionCoeff i : ℝ) *
        (1 / (N : ℝ) ^ (i + 1) - 1 / ((N : ℝ) + 1) ^ (i + 1)) -
       (stirlingCorrectionCoeff i : ℝ) *
        (∑ j ∈ Finset.range (J - i),
          (inversePowerDifferenceCoeff i j : ℝ) / (N : ℝ) ^ (i + j + 2)))) =
      ∑ i ∈ Finset.range J, (stirlingCorrectionCoeff i : ℝ) *
        ((1 / (N : ℝ) ^ (i + 1) - 1 / ((N : ℝ) + 1) ^ (i + 1)) -
          ∑ j ∈ Finset.range (J - i),
            (inversePowerDifferenceCoeff i j : ℝ) / (N : ℝ) ^ (i + j + 2)) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq]
  calc
    _ ≤ ∑ i ∈ Finset.range J, |(stirlingCorrectionCoeff i : ℝ) *
        ((1 / (N : ℝ) ^ (i + 1) - 1 / ((N : ℝ) + 1) ^ (i + 1)) -
          ∑ j ∈ Finset.range (J - i),
            (inversePowerDifferenceCoeff i j : ℝ) / (N : ℝ) ^ (i + j + 2))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range J,
        (|(stirlingCorrectionCoeff i : ℝ)| * (2 : ℝ) ^ i *
          (Nat.choose (J + 1) i : ℝ)) / (N : ℝ) ^ (J + 2) :=
      Finset.sum_le_sum (fun i hi => stirlingCorrection_slice_error N J i hN (Finset.mem_range.mp hi))
    _ = _ := by simp only [div_eq_mul_inv, Finset.sum_mul]

theorem stirlingCorrection_increment_error (N J : ℕ) (hN : 1 ≤ N) :
    |(Real.log (Stirling.stirlingSeq N) - Real.log (Stirling.stirlingSeq (N + 1))) -
        (stirlingCorrectionPrefix N J - stirlingCorrectionPrefix (N + 1) J)| ≤
      (stirlingResidualConstant J : ℝ) / (N : ℝ) ^ (J + 2) := by
  let A : ℝ := ∑ n ∈ Finset.range J, (stirlingIncrementCoeff n : ℝ) / (N : ℝ) ^ (n + 2)
  let D : ℝ := Real.log (Stirling.stirlingSeq N) - Real.log (Stirling.stirlingSeq (N + 1))
  let F : ℝ := stirlingCorrectionPrefix N J - stirlingCorrectionPrefix (N + 1) J
  have hA : |D - A| ≤ ((J : ℝ) + 3) / (N : ℝ) ^ (J + 2) :=
    stirlingIncrement_inversePower_error N J hN
  have hF : |F - A| ≤
      (∑ i ∈ Finset.range J, |(stirlingCorrectionCoeff i : ℝ)| *
        (2 : ℝ) ^ i * (Nat.choose (J + 1) i : ℝ)) / (N : ℝ) ^ (J + 2) :=
    stirlingCorrection_delta_error N J hN
  change |D - F| ≤ _
  calc
    _ = |(D - A) - (F - A)| := by congr 1; ring
    _ ≤ |D - A| + |F - A| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add (D - A) (-(F - A))
    _ ≤ ((J : ℝ) + 3) / (N : ℝ) ^ (J + 2) +
        (∑ i ∈ Finset.range J, |(stirlingCorrectionCoeff i : ℝ)| *
          (2 : ℝ) ^ i * (Nat.choose (J + 1) i : ℝ)) / (N : ℝ) ^ (J + 2) := add_le_add hA hF
    _ = _ := by rw [stirlingResidualConstant_cast]; ring

end Hardinian
