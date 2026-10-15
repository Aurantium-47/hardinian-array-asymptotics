import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace Hardinian.FiniteAlgebra

/-- Pair the two off-diagonal orientations, retaining each strictly increasing pair once. -/
theorem sum_pairs_ordered (m : ℕ) (F : Fin m → Fin m → ℤ)
    (hdiag : ∀ i, F i i = 0) :
    (∑ i : Fin m, ∑ j : Fin m, F i j) =
      ∑ i : Fin m,
        ∑ j ∈ (Finset.univ : Finset (Fin m)).filter (fun j => i < j),
          (F i j + F j i) := by
  have hsplit (i j : Fin m) :
      F i j = (if i < j then F i j else 0) + (if j < i then F i j else 0) := by
    rcases lt_trichotomy i j with hij | heq | hji
    · have hn : ¬ j < i := not_lt.mpr (le_of_lt hij)
      simp [hij, hn]
    · subst j
      simp [hdiag]
    · have hn : ¬ i < j := not_lt.mpr (le_of_lt hji)
      simp [hji, hn]
  have hswap :
      (∑ i : Fin m, ∑ j : Fin m, if j < i then F i j else 0) =
        ∑ i : Fin m, ∑ j : Fin m, if i < j then F j i else 0 :=
    Finset.sum_comm
  simp only [Finset.sum_filter]
  calc
    (∑ i : Fin m, ∑ j : Fin m, F i j) =
        ∑ i : Fin m, ∑ j : Fin m,
          ((if i < j then F i j else 0) + (if j < i then F i j else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_congr rfl (fun j hj => hsplit i j)
    _ = (∑ i : Fin m, ∑ j : Fin m, if i < j then F i j else 0) +
        (∑ i : Fin m, ∑ j : Fin m, if j < i then F i j else 0) := by
      simp only [Finset.sum_add_distrib]
    _ = (∑ i : Fin m, ∑ j : Fin m, if i < j then F i j else 0) +
        (∑ i : Fin m, ∑ j : Fin m, if i < j then F j i else 0) := by
      rw [hswap]
    _ = ∑ i : Fin m, ∑ j : Fin m, if i < j then F i j + F j i else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases h : i < j <;> simp [h]

/-- Expand the determinant of the actual rectangular product as a finite double sum. -/
theorem det_rectangular_product_expansion (m : ℕ)
    (A : Matrix (Fin 2) (Fin m) ℤ)
    (B : Matrix (Fin m) (Fin 2) ℤ) :
    Matrix.det (A * B) =
      ∑ i : Fin m, ∑ j : Fin m,
        A 0 i * A 1 j * (B i 0 * B j 1 - B i 1 * B j 0) := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.mul_apply]
  rw [Fintype.sum_mul_sum, Fintype.sum_mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Rectangular second-order Cauchy-Binet with each pair in ascending order and no factorial. -/
theorem rectangular_binet_two_ordered (m : ℕ)
    (A : Matrix (Fin 2) (Fin m) ℤ)
    (B : Matrix (Fin m) (Fin 2) ℤ) :
    Matrix.det (A * B) =
      ∑ i : Fin m,
        ∑ j ∈ (Finset.univ : Finset (Fin m)).filter (fun j => i < j),
          Matrix.det (A.submatrix (id : Fin 2 → Fin 2)
            (![i, j] : Fin 2 → Fin m)) *
          Matrix.det (B.submatrix (![i, j] : Fin 2 → Fin m)
            (id : Fin 2 → Fin 2)) := by
  rw [det_rectangular_product_expansion]
  rw [sum_pairs_ordered m
    (fun i j => A 0 i * A 1 j * (B i 0 * B j 1 - B i 1 * B j 0))
    (by intro i; ring)]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Matrix.det_fin_two, Matrix.submatrix_apply, id_eq,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- The middle dimensions zero and one give determinant zero, without constructing invalid indices. -/
theorem det_rectangular_product_eq_zero_of_lt_two
    (m : ℕ) (hm : m < 2)
    (A : Matrix (Fin 2) (Fin m) ℤ)
    (B : Matrix (Fin m) (Fin 2) ℤ) :
    Matrix.det (A * B) = 0 := by
  rw [rectangular_binet_two_ordered]
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  have hij := (Finset.mem_filter.mp hj).2
  change i.val < j.val at hij
  have hi' := i.isLt
  have hj' := j.isLt
  omega

end Hardinian.FiniteAlgebra

