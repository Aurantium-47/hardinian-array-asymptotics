import Hardinian.ComplementaryMinorTwo
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

namespace Hardinian.FiniteAlgebra

def twoSetOfLT {m : ℕ} (u v : Fin m) (h : u < v) : TwoSet m :=
  ⟨{u, v}, by simp [ne_of_lt h]⟩

theorem select₂_twoSetOfLT {m : ℕ} (u v : Fin m) (h : u < v) :
    (select₂ (twoSetOfLT u v h) : Fin 2 → Fin m) = ![u, v] := by
  symm
  apply Finset.orderEmbOfFin_unique (twoSetOfLT u v h).property
  · intro x
    fin_cases x <;> simp [twoSetOfLT]
  · intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all

theorem twoSetOfLT_select₂ {m : ℕ} (I : TwoSet m) :
    twoSetOfLT (select₂ I 0) (select₂ I 1) (select₂_lt I) = I := by
  apply Subtype.ext
  ext x
  simp only [twoSetOfLT, Finset.mem_insert, Finset.mem_singleton, mem_twoSet_iff]

/-- A two-element finset has exactly one strictly increasing representative. -/
noncomputable def twoSetOrderEquiv (m : ℕ) :
    TwoSet m ≃ (Σ u : Fin m, {v : Fin m // u < v}) where
  toFun I := ⟨select₂ I 0, ⟨select₂ I 1, select₂_lt I⟩⟩
  invFun p := twoSetOfLT p.1 p.2.val p.2.property
  left_inv I := twoSetOfLT_select₂ I
  right_inv p := by
    rcases p with ⟨u, v, h⟩
    simp only [select₂_twoSetOfLT, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem sum_twoSet_eq_ordered (m : ℕ) (f : Fin m → Fin m → ℤ) :
    (∑ I : TwoSet m, f (select₂ I 0) (select₂ I 1)) =
      ∑ u : Fin m,
        ∑ v ∈ (Finset.univ : Finset (Fin m)).filter (fun v => u < v), f u v := by
  classical
  calc
    (∑ I : TwoSet m, f (select₂ I 0) (select₂ I 1)) =
        ∑ p : (Σ u : Fin m, {v : Fin m // u < v}), f p.1 p.2.val :=
      Fintype.sum_equiv (twoSetOrderEquiv m) _ _ (fun I => rfl)
    _ = ∑ u : Fin m, ∑ v : {v : Fin m // u < v}, f u v.val :=
      Fintype.sum_sigma _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u hu
      exact (Finset.sum_subtype (p := fun v : Fin m => u < v)
        ((Finset.univ : Finset (Fin m)).filter (fun v => u < v))
        (fun v => by simp) (f u)).symm

theorem sum_twoSet_eq_zero_of_lt_two (m : ℕ) (hm : m < 2)
    (f : Fin m → Fin m → ℤ) :
    (∑ I : TwoSet m, f (select₂ I 0) (select₂ I 1)) = 0 := by
  rw [sum_twoSet_eq_ordered]
  apply Finset.sum_eq_zero
  intro u hu
  apply Finset.sum_eq_zero
  intro v hv
  have huv := (Finset.mem_filter.mp hv).2
  change u.val < v.val at huv
  have hu' := u.isLt
  have hv' := v.isLt
  omega

end Hardinian.FiniteAlgebra
