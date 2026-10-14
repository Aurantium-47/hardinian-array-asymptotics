import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace Hardinian.FiniteAlgebra

abbrev TwoSet (m : ℕ) := {s : Finset (Fin m) // s.card = 2}

noncomputable def select₂ {m : ℕ} (I : TwoSet m) : Fin 2 ↪o Fin m :=
  I.val.orderEmbOfFin I.property

theorem select₂_lt {m : ℕ} (I : TwoSet m) : select₂ I 0 < select₂ I 1 :=
  (select₂ I).strictMono (by decide)

theorem mem_twoSet_iff {m : ℕ} (I : TwoSet m) (x : Fin m) :
    x ∈ I.val ↔ x = select₂ I 0 ∨ x = select₂ I 1 := by
  classical
  constructor
  · intro hx
    let e := I.val.orderIsoOfFin I.property
    obtain ⟨a, ha⟩ := e.surjective ⟨x, hx⟩
    have hv : select₂ I a = x := congrArg Subtype.val ha
    fin_cases a
    · exact Or.inl hv.symm
    · exact Or.inr hv.symm
  · rintro (rfl | rfl)
    · exact Finset.orderEmbOfFin_mem I.val I.property 0
    · exact Finset.orderEmbOfFin_mem I.val I.property 1

theorem two_complement_card {k : ℕ} (I : TwoSet (k + 2)) :
    (I.valᶜ).card = k := by
  simp only [Finset.card_compl, Fintype.card_fin, I.property, Nat.add_sub_cancel]

noncomputable def omit₂ {k : ℕ} (I : TwoSet (k + 2)) : Fin k ↪o Fin (k + 2) :=
  (I.valᶜ).orderEmbOfFin (two_complement_card I)

noncomputable def indexSum₂ {m : ℕ} (I : TwoSet m) : ℕ :=
  (select₂ I 0).val + (select₂ I 1).val

theorem high_ne_zero {k : ℕ} (I : TwoSet (k + 2)) : select₂ I 1 ≠ 0 :=
  ne_of_gt (lt_of_le_of_lt (Fin.zero_le (select₂ I 0)) (select₂_lt I))

noncomputable def highPred {k : ℕ} (I : TwoSet (k + 2)) : Fin (k + 1) :=
  (select₂ I 1).pred (high_ne_zero I)

theorem lift_highPred {k : ℕ} (I : TwoSet (k + 2)) :
    (select₂ I 0).succAbove (highPred I) = select₂ I 1 :=
  Fin.succAbove_pred_of_lt _ _ (select₂_lt I)

theorem highPred_val {k : ℕ} (I : TwoSet (k + 2)) :
    (highPred I).val + 1 = (select₂ I 1).val := by
  simpa only [highPred, Fin.val_succ] using
    congrArg Fin.val (Fin.succ_pred (select₂ I 1) (high_ne_zero I))

noncomputable def deleteTwice {k : ℕ} (I : TwoSet (k + 2)) (x : Fin k) : Fin (k + 2) :=
  (select₂ I 0).succAbove ((highPred I).succAbove x)

theorem deleteTwice_ne_low {k : ℕ} (I : TwoSet (k + 2)) (x : Fin k) :
    deleteTwice I x ≠ select₂ I 0 :=
  Fin.succAbove_ne _ _

theorem deleteTwice_ne_high {k : ℕ} (I : TwoSet (k + 2)) (x : Fin k) :
    deleteTwice I x ≠ select₂ I 1 := by
  intro h
  have hi := (Fin.strictMono_succAbove (select₂ I 0)).injective
  have he : (highPred I).succAbove x = highPred I :=
    hi (h.trans (lift_highPred I).symm)
  exact Fin.succAbove_ne (highPred I) x he

theorem deleteTwice_eq_omit {k : ℕ} (I : TwoSet (k + 2)) :
    deleteTwice I = (omit₂ I : Fin k → Fin (k + 2)) := by
  change deleteTwice I =
    ((I.valᶜ).orderEmbOfFin (two_complement_card I) : Fin k → Fin (k + 2))
  apply Finset.orderEmbOfFin_unique (two_complement_card I)
  · intro x
    rw [Finset.mem_compl, mem_twoSet_iff]
    rintro (h | h)
    · exact deleteTwice_ne_low I x h
    · exact deleteTwice_ne_high I x h
  · exact (Fin.strictMono_succAbove (select₂ I 0)).comp
      (Fin.strictMono_succAbove (highPred I))

noncomputable def complement₂ {k : ℕ}
    (A : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) (I J : TwoSet (k + 2)) : ℤ :=
  Matrix.det (A.submatrix (omit₂ I) (omit₂ J))

noncomputable def replaceTwo {k : ℕ}
    (A : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) (I J : TwoSet (k + 2)) :
    Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ :=
  (A.updateCol (select₂ J 0) (Pi.single (select₂ I 0) 1)).updateCol
    (select₂ J 1) (Pi.single (select₂ I 1) 1)

theorem det_of_single_column {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) (i j : Fin (n + 1))
    (hc : ∀ x, A x j = if x = i then 1 else 0) :
    Matrix.det A = (-1 : ℤ) ^ (i.val + j.val) *
      Matrix.det (A.submatrix i.succAbove j.succAbove) := by
  classical
  rw [Matrix.det_succ_column A j]
  simp [hc, mul_ite, ite_mul]

theorem replaceTwo_first_column {k : ℕ}
    (A : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) (I J : TwoSet (k + 2))
    (x : Fin (k + 2)) :
    replaceTwo A I J x (select₂ J 0) = if x = select₂ I 0 then 1 else 0 := by
  simp only [replaceTwo, Matrix.updateCol_ne (ne_of_lt (select₂_lt J)),
    Matrix.updateCol_self, Pi.single_apply, eq_comm]

theorem high_single_after_delete {k : ℕ} (I : TwoSet (k + 2)) (x : Fin (k + 1)) :
    (Pi.single (select₂ I 1) 1 : Fin (k + 2) → ℤ) ((select₂ I 0).succAbove x) =
      if x = highPred I then 1 else 0 := by
  classical
  by_cases h : x = highPred I
  · subst x
    simp [lift_highPred]
  · have h' : (select₂ I 0).succAbove x ≠ select₂ I 1 := by
      intro he
      exact h ((Fin.strictMono_succAbove (select₂ I 0)).injective
        (he.trans (lift_highPred I).symm))
    simp [Pi.single_apply, h, h', Ne.symm h']

theorem replaceTwo_second_column {k : ℕ}
    (A : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) (I J : TwoSet (k + 2))
    (x : Fin (k + 1)) :
    ((replaceTwo A I J).submatrix (select₂ I 0).succAbove (select₂ J 0).succAbove)
      x (highPred J) = if x = highPred I then 1 else 0 := by
  change replaceTwo A I J ((select₂ I 0).succAbove x)
    ((select₂ J 0).succAbove (highPred J)) = _
  rw [lift_highPred J, replaceTwo, Matrix.updateCol_self]
  exact high_single_after_delete I x

theorem replaceTwo_remaining_matrix {k : ℕ}
    (A : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) (I J : TwoSet (k + 2)) :
    ((replaceTwo A I J).submatrix (select₂ I 0).succAbove (select₂ J 0).succAbove).submatrix
      (highPred I).succAbove (highPred J).succAbove =
      A.submatrix (omit₂ I) (omit₂ J) := by
  ext x y
  change replaceTwo A I J (deleteTwice I x) (deleteTwice J y) =
    A (omit₂ I x) (omit₂ J y)
  rw [replaceTwo, Matrix.updateCol_ne (deleteTwice_ne_high J y),
    Matrix.updateCol_ne (deleteTwice_ne_low J y)]
  simp only [deleteTwice_eq_omit]

theorem deletion_sign {k : ℕ} (I J : TwoSet (k + 2)) :
    (-1 : ℤ) ^ ((select₂ I 0).val + (select₂ J 0).val) *
      (-1 : ℤ) ^ ((highPred I).val + (highPred J).val) =
      (-1 : ℤ) ^ (indexSum₂ I + indexSum₂ J) := by
  have hi := highPred_val I
  have hj := highPred_val J
  have he : indexSum₂ I + indexSum₂ J =
      ((select₂ I 0).val + (select₂ J 0).val) +
        ((highPred I).val + (highPred J).val) + 2 := by
    unfold indexSum₂
    omega
  rw [← pow_add]
  conv_rhs => rw [he, pow_add]
  norm_num

/-- Two specified standard columns give the signed, ascending complementary minor.
The dimension parameter may be zero, so the final complementary determinant may be empty. -/
theorem det_replaceTwo_columns {k : ℕ}
    (A : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) (I J : TwoSet (k + 2)) :
    Matrix.det (replaceTwo A I J) =
      (-1 : ℤ) ^ (indexSum₂ I + indexSum₂ J) * complement₂ A I J := by
  unfold complement₂
  rw [det_of_single_column (replaceTwo A I J) (select₂ I 0) (select₂ J 0)
    (replaceTwo_first_column A I J)]
  rw [det_of_single_column _ (highPred I) (highPred J) (replaceTwo_second_column A I J)]
  rw [← mul_assoc, deletion_sign, replaceTwo_remaining_matrix]

theorem complement₂_zero (A : Matrix (Fin 2) (Fin 2) ℤ) (I J : TwoSet 2) :
    complement₂ (k := 0) A I J = 1 :=
  Matrix.det_fin_zero

end Hardinian.FiniteAlgebra
