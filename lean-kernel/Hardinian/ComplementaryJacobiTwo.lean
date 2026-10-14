import Hardinian.ComplementaryMinorTwo
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

namespace Hardinian.FiniteAlgebra

open scoped BigOperators

noncomputable def minor₂ {m : ℕ}
    (V : Matrix (Fin m) (Fin m) ℤ) (I J : TwoSet m) : ℤ :=
  Matrix.det (V.submatrix (select₂ I) (select₂ J))

noncomputable def coefficientTwo {k : ℕ}
    (V : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) (I J : TwoSet (k + 2)) :
    Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ :=
  ((1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ).updateCol
    (select₂ J 0) (fun x => V x (select₂ I 0))).updateCol
      (select₂ J 1) (fun x => V x (select₂ I 1))

noncomputable def selector₂ {m : ℕ} (J : TwoSet m) : Matrix (Fin 2) (Fin m) ℤ :=
  fun a x => if x = select₂ J a then 1 else 0

noncomputable def updateDirections₂ {k : ℕ}
    (V : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) (I J : TwoSet (k + 2)) :
    Matrix (Fin (k + 2)) (Fin 2) ℤ :=
  fun x b => V x (select₂ I b) - selector₂ J b x

theorem coefficientTwo_selected_column {k : ℕ}
    (V : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) (I J : TwoSet (k + 2))
    (x : Fin (k + 2)) (b : Fin 2) :
    coefficientTwo V I J x (select₂ J b) = V x (select₂ I b) := by
  fin_cases b
  · simp only [coefficientTwo, Matrix.updateCol_ne (ne_of_lt (select₂_lt J)),
      Matrix.updateCol_self]
  · simp only [coefficientTwo, Matrix.updateCol_self]

theorem coefficientTwo_other_column {k : ℕ}
    (V : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) (I J : TwoSet (k + 2))
    (y : Fin (k + 2)) (hy : y ∉ J.val) (x : Fin (k + 2)) :
    coefficientTwo V I J x y = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) x y := by
  have h0 : y ≠ select₂ J 0 := fun h => hy ((mem_twoSet_iff J y).2 (Or.inl h))
  have h1 : y ≠ select₂ J 1 := fun h => hy ((mem_twoSet_iff J y).2 (Or.inr h))
  simp only [coefficientTwo, Matrix.updateCol_ne h1, Matrix.updateCol_ne h0]

theorem selector₂_selected {m : ℕ} (J : TwoSet m) (a b : Fin 2) :
    selector₂ J a (select₂ J b) = if b = a then 1 else 0 := by
  classical
  by_cases h : b = a
  · subst b
    simp [selector₂]
  · have h' : select₂ J b ≠ select₂ J a := fun he => h ((select₂ J).injective he)
    simp only [selector₂, if_neg h', if_neg h]

theorem selector₂_mul {m : ℕ} (J : TwoSet m) (U : Matrix (Fin m) (Fin 2) ℤ)
    (a b : Fin 2) :
    (selector₂ J * U) a b = U (select₂ J a) b := by
  classical
  rw [Matrix.mul_apply]
  simp [selector₂, ite_mul]

theorem coefficientTwo_eq_one_add_update {k : ℕ}
    (V : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) (I J : TwoSet (k + 2)) :
    coefficientTwo V I J =
      (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) +
        updateDirections₂ V I J * selector₂ J := by
  classical
  ext x y
  change coefficientTwo V I J x y =
    (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) x y +
      ∑ a : Fin 2, updateDirections₂ V I J x a * selector₂ J a y
  rw [Fin.sum_univ_two]
  by_cases h0 : y = select₂ J 0
  · subst y
    rw [coefficientTwo_selected_column V I J x 0]
    simp only [updateDirections₂, selector₂, Matrix.one_apply, if_pos rfl,
      if_neg (ne_of_lt (select₂_lt J)), mul_one, mul_zero, add_zero]
    ring
  · by_cases h1 : y = select₂ J 1
    · subst y
      rw [coefficientTwo_selected_column V I J x 1]
      simp only [updateDirections₂, selector₂, Matrix.one_apply, if_pos rfl,
        if_neg (ne_of_gt (select₂_lt J)), mul_one, mul_zero, zero_add]
      ring
    · have hy : y ∉ J.val := by
        rw [mem_twoSet_iff]
        exact fun h => h.elim h0 h1
      rw [coefficientTwo_other_column V I J y hy x]
      simp only [selector₂, if_neg h0, if_neg h1, mul_zero, add_zero]

theorem one_add_selector_mul_update {k : ℕ}
    (V : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) (I J : TwoSet (k + 2)) :
    (1 : Matrix (Fin 2) (Fin 2) ℤ) + selector₂ J * updateDirections₂ V I J =
      V.submatrix (select₂ J) (select₂ I) := by
  ext a b
  change (1 : Matrix (Fin 2) (Fin 2) ℤ) a b +
    (selector₂ J * updateDirections₂ V I J) a b = V (select₂ J a) (select₂ I b)
  rw [selector₂_mul]
  simp only [updateDirections₂, selector₂_selected, Matrix.one_apply]
  ring

theorem det_coefficientTwo {k : ℕ}
    (V : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) (I J : TwoSet (k + 2)) :
    Matrix.det (coefficientTwo V I J) = minor₂ V J I := by
  unfold minor₂
  rw [coefficientTwo_eq_one_add_update, Matrix.det_one_add_mul_comm,
    one_add_selector_mul_update]

theorem mul_coefficientTwo {k : ℕ}
    (A V : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ)
    (hAV : A * V = 1) (I J : TwoSet (k + 2)) :
    A * coefficientTwo V I J = replaceTwo A I J := by
  classical
  ext x y
  by_cases h0 : y = select₂ J 0
  · subst y
    calc
      (A * coefficientTwo V I J) x (select₂ J 0) = (A * V) x (select₂ I 0) := by
        simp only [Matrix.mul_apply, coefficientTwo_selected_column]
      _ = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) x (select₂ I 0) :=
        congrArg (fun M : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ => M x (select₂ I 0)) hAV
      _ = replaceTwo A I J x (select₂ J 0) := by
        simp only [replaceTwo_first_column, Matrix.one_apply]
  · by_cases h1 : y = select₂ J 1
    · subst y
      calc
        (A * coefficientTwo V I J) x (select₂ J 1) = (A * V) x (select₂ I 1) := by
          simp only [Matrix.mul_apply, coefficientTwo_selected_column]
        _ = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) x (select₂ I 1) :=
          congrArg (fun M : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ => M x (select₂ I 1)) hAV
        _ = replaceTwo A I J x (select₂ J 1) := by
          simp only [replaceTwo, Matrix.updateCol_self, Matrix.one_apply, Pi.single_apply, eq_comm]
    · have hy : y ∉ J.val := by
        rw [mem_twoSet_iff]
        exact fun h => h.elim h0 h1
      calc
        (A * coefficientTwo V I J) x y =
            (A * (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ)) x y := by
          simp only [Matrix.mul_apply, coefficientTwo_other_column V I J y hy]
        _ = A x y := by rw [Matrix.mul_one]
        _ = replaceTwo A I J x y := by
          simp only [replaceTwo, Matrix.updateCol_ne h1, Matrix.updateCol_ne h0]

/-- The ascending two-index complementary-minor identity from a whole-matrix right inverse. -/
theorem complementary_two_of_right_inverse
    (k : ℕ) (A V : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ)
    (hAV : A * V = 1) (I J : TwoSet (k + 2)) :
    complement₂ A I J =
      (-1 : ℤ) ^ (indexSum₂ I + indexSum₂ J) * Matrix.det A * minor₂ V J I := by
  let sign : ℤ := (-1) ^ (indexSum₂ I + indexSum₂ J)
  have hs : sign * sign = 1 :=
    pow_mul_pow_eq_one (a := (-1 : ℤ)) (b := (-1 : ℤ))
      (indexSum₂ I + indexSum₂ J) (by norm_num)
  have hd : Matrix.det A * minor₂ V J I = sign * complement₂ A I J := by
    calc
      Matrix.det A * minor₂ V J I = Matrix.det A * Matrix.det (coefficientTwo V I J) := by
        rw [det_coefficientTwo]
      _ = Matrix.det (A * coefficientTwo V I J) := (Matrix.det_mul A _).symm
      _ = Matrix.det (replaceTwo A I J) := congrArg Matrix.det (mul_coefficientTwo A V hAV I J)
      _ = sign * complement₂ A I J := det_replaceTwo_columns A I J
  calc
    complement₂ A I J = (sign * sign) * complement₂ A I J := by rw [hs, one_mul]
    _ = sign * (sign * complement₂ A I J) := mul_assoc _ _ _
    _ = sign * (Matrix.det A * minor₂ V J I) := congrArg (fun z : ℤ => sign * z) hd.symm
    _ = _ := (mul_assoc sign (Matrix.det A) (minor₂ V J I)).symm

theorem complementary_two_of_right_inverse_zero
    (A V : Matrix (Fin 2) (Fin 2) ℤ) (hAV : A * V = 1) (I J : TwoSet 2) :
    (1 : ℤ) = (-1 : ℤ) ^ (indexSum₂ I + indexSum₂ J) * Matrix.det A * minor₂ V J I := by
  simpa only [complement₂_zero] using complementary_two_of_right_inverse 0 A V hAV I J

end Hardinian.FiniteAlgebra
