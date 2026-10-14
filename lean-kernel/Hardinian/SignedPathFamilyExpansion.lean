import Hardinian.GridPathCount
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace Hardinian

open scoped BigOperators

def PathTuple {k N : ℕ} (u v : Fin k → Fin (N + 1)) (σ : Equiv.Perm (Fin k)) :=
  ∀ i : Fin k, GridPath (u i).val (v (σ i)).val

theorem pathTuple_finite {k N : ℕ} (u v : Fin k → Fin (N + 1))
    (σ : Equiv.Perm (Fin k)) : Finite (PathTuple u v σ) := by
  letI (i : Fin k) : Finite (GridPath (u i).val (v (σ i)).val) :=
    gridPath_finite (u i).val (v (σ i)).val
  unfold PathTuple
  infer_instance

noncomputable instance pathTupleFintype {k N : ℕ} (u v : Fin k → Fin (N + 1))
    (σ : Equiv.Perm (Fin k)) : Fintype (PathTuple u v σ) := by
  letI := pathTuple_finite u v σ
  exact Fintype.ofFinite (PathTuple u v σ)

theorem pathTuple_card {k N : ℕ} (u v : Fin k → Fin (N + 1))
    (σ : Equiv.Perm (Fin k)) :
    Nat.card (PathTuple u v σ) = ∏ i : Fin k, Nat.choose ((u i).val + (v (σ i)).val) (u i).val := by
  unfold PathTuple
  rw [Nat.card_pi]
  apply Finset.prod_congr rfl
  intro i hi
  exact gridPath_card (u i).val (v (σ i)).val

theorem pathTuple_fintype_card {k N : ℕ} (u v : Fin k → Fin (N + 1))
    (σ : Equiv.Perm (Fin k)) :
    Fintype.card (PathTuple u v σ) = ∏ i : Fin k, Nat.choose ((u i).val + (v (σ i)).val) (u i).val := by
  rw [← Nat.card_eq_fintype_card]
  exact pathTuple_card u v σ

def SignedFamily {k N : ℕ} (u v : Fin k → Fin (N + 1)) :=
  (σ : Equiv.Perm (Fin k)) × PathTuple u v σ

noncomputable instance signedFamilyFintype {k N : ℕ} (u v : Fin k → Fin (N + 1)) :
    Fintype (SignedFamily u v) := by
  unfold SignedFamily
  infer_instance

theorem signedFamily_finite {k N : ℕ} (u v : Fin k → Fin (N + 1)) :
    Finite (SignedFamily u v) := by
  infer_instance

theorem signedFamily_card {k N : ℕ} (u v : Fin k → Fin (N + 1)) :
    Nat.card (SignedFamily u v) =
      ∑ σ : Equiv.Perm (Fin k), ∏ i : Fin k, Nat.choose ((u i).val + (v (σ i)).val) (u i).val := by
  unfold SignedFamily
  rw [Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro σ hσ
  exact pathTuple_card u v σ

def signedFamilyWeight {k N : ℕ} {u v : Fin k → Fin (N + 1)} (F : SignedFamily u v) : ℤ :=
  (Equiv.Perm.sign F.1 : ℤ)

noncomputable def signedFamilySum {k N : ℕ} (u v : Fin k → Fin (N + 1)) : ℤ :=
  ∑ F : SignedFamily u v, signedFamilyWeight F

def gridPathMatrix {k N : ℕ} (u v : Fin k → Fin (N + 1)) : Matrix (Fin k) (Fin k) ℤ :=
  fun i j => (Nat.choose ((u i).val + (v j).val) (u i).val : ℤ)

theorem signedFamilySum_eq_perm_sum {k N : ℕ} (u v : Fin k → Fin (N + 1)) :
    signedFamilySum u v = ∑ σ : Equiv.Perm (Fin k),
      (Equiv.Perm.sign σ : ℤ) * ∏ i : Fin k, (Nat.choose ((u i).val + (v (σ i)).val) (u i).val : ℤ) := by
  classical
  calc
    signedFamilySum u v = ∑ σ : Equiv.Perm (Fin k),
        ∑ _P : PathTuple u v σ, (Equiv.Perm.sign σ : ℤ) := by
      exact Fintype.sum_sigma (fun F : SignedFamily u v => signedFamilyWeight F)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, pathTuple_fintype_card, Nat.cast_prod]
      exact mul_comm _ _

theorem gridPathMatrix_det_columns {k N : ℕ} (u v : Fin k → Fin (N + 1)) :
    (gridPathMatrix u v).det = ∑ σ : Equiv.Perm (Fin k),
      (Equiv.Perm.sign σ : ℤ) * ∏ i : Fin k, gridPathMatrix u v i (σ i) := by
  calc
    (gridPathMatrix u v).det = (gridPathMatrix u v).transpose.det :=
      (Matrix.det_transpose (gridPathMatrix u v)).symm
    _ = _ := by
      simpa only [Matrix.transpose_apply, Int.cast_id] using
        Matrix.det_apply' (gridPathMatrix u v).transpose

theorem gridPathMatrix_det_eq_signedFamilySum {k N : ℕ} (u v : Fin k → Fin (N + 1)) :
    (gridPathMatrix u v).det = signedFamilySum u v := by
  exact (gridPathMatrix_det_columns u v).trans (signedFamilySum_eq_perm_sum u v).symm

theorem pathTuple_card_zero {N : ℕ} (u v : Fin 0 → Fin (N + 1))
    (σ : Equiv.Perm (Fin 0)) : Nat.card (PathTuple u v σ) = 1 := by
  simp [pathTuple_card]

theorem signedFamily_card_zero {N : ℕ} (u v : Fin 0 → Fin (N + 1)) :
    Nat.card (SignedFamily u v) = 1 := by
  simp [signedFamily_card]

theorem gridPathMatrix_det_zero {N : ℕ} (u v : Fin 0 → Fin (N + 1)) :
    (gridPathMatrix u v).det = 1 := Matrix.det_isEmpty

theorem signedFamilySum_zero {N : ℕ} (u v : Fin 0 → Fin (N + 1)) :
    signedFamilySum u v = 1 := by
  rw [← gridPathMatrix_det_eq_signedFamilySum]
  exact gridPathMatrix_det_zero u v

end Hardinian
