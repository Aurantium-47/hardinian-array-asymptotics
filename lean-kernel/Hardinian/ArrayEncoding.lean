import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.NormNum

namespace Hardinian

theorem r2_side_reparameterization (n : ℕ) (hn : 3 ≤ n) : n = (n - 3) + 3 := by omega

theorem nat_unit_step_iff (x y : ℕ) :
    (x ≤ y ∧ y ≤ x + 1) ↔ (y = x ∨ y = x + 1) := by omega

def ArraySteps (k : ℕ) (A : Fin (k + 3) → Fin (k + 3) → ℕ) : Prop :=
  (∀ i : Fin (k + 3), ∀ j : Fin (k + 2),
    A i j.castSucc ≤ A i j.succ ∧ A i j.succ ≤ A i j.castSucc + 1) ∧
  (∀ i : Fin (k + 2), ∀ j : Fin (k + 3),
    A i.castSucc j ≤ A i.succ j ∧ A i.succ j ≤ A i.castSucc j + 1) ∧
  (∀ i j : Fin (k + 2), A i.castSucc j.castSucc ≤ A i.succ j.succ ∧
    A i.succ j.succ ≤ A i.castSucc j.castSucc + 1)

def ArrayMonotone (k : ℕ) (A : Fin (k + 3) → Fin (k + 3) → ℕ) : Prop :=
  ∀ i i' j j', i ≤ i' → j ≤ j' → A i j ≤ A i' j'

def IsR2Array (k : ℕ) (A : Fin (k + 3) → Fin (k + 3) → ℕ) : Prop :=
  A 0 0 = 0 ∧ A (Fin.last (k + 2)) (Fin.last (k + 2)) = k ∧ ArraySteps k A ∧
    ∀ i j, |(A i j : ℤ) - ((max i.val j.val : ℕ) : ℤ)| ≤ 2

def R2Array (k : ℕ) : Type :=
  {A : Fin (k + 3) → Fin (k + 3) → ℕ // IsR2Array k A}

def BoundaryArray (k : ℕ) (A : Fin (k + 3) → Fin (k + 3) → ℕ) : Prop :=
  A 0 0 = 0 ∧ ArrayMonotone k A ∧
    (∀ i, A (Fin.last (k + 2)) i = k ∧ A i (Fin.last (k + 2)) = k) ∧
    ∀ i j : Fin (k + 2), A i.succ j.succ ≤ A i.castSucc j.castSucc + 1

theorem fin_step_lipschitz (m : ℕ) (f : Fin (m + 1) → ℕ)
    (hf : ∀ i : Fin m, f i.succ ≤ f i.castSucc + 1)
    (i j : Fin (m + 1)) (hij : i ≤ j) :
    (f j : ℤ) - (f i : ℤ) ≤ (j.val : ℤ) - (i.val : ℤ) := by
  have hg : Monotone (fun t : Fin (m + 1) => (t.val : ℤ) - (f t : ℤ)) := by
    apply Fin.monotone_iff_le_succ.mpr
    intro t
    have h := hf t
    change (t.val : ℤ) - (f t.castSucc : ℤ) ≤ ((t.val + 1 : ℕ) : ℤ) - (f t.succ : ℤ)
    omega
  have h := hg hij
  dsimp only at h
  omega

theorem array_steps_monotone (k : ℕ) (A : Fin (k + 3) → Fin (k + 3) → ℕ)
    (h : ArraySteps k A) : ArrayMonotone k A := by
  have hr (i) : Monotone (A i) := Fin.monotone_iff_le_succ.mpr (fun j => (h.1 i j).1)
  have hv (j) : Monotone (fun i => A i j) :=
    Fin.monotone_iff_le_succ.mpr (fun i => (h.2.1 i j).1)
  intro i i' j j' hi hj
  exact (hv j hi).trans (hr i' hj)

theorem array_diagonal_value_bound (k : ℕ) (A : Fin (k + 3) → Fin (k + 3) → ℕ)
    (h0 : A 0 0 = 0) (h : ArraySteps k A) (i : Fin (k + 3)) : A i i ≤ i.val := by
  have hi := fin_step_lipschitz (k + 2) (fun t => A t t)
    (fun t => (h.2.2 t t).2) 0 i (Fin.zero_le i)
  simp only [h0, Fin.val_zero, Nat.cast_zero, sub_zero] at hi
  exact_mod_cast hi

theorem array_value_le_max (k : ℕ) (A : Fin (k + 3) → Fin (k + 3) → ℕ)
    (h0 : A 0 0 = 0) (h : ArraySteps k A) (i j : Fin (k + 3)) :
    A i j ≤ max i.val j.val := by
  have hm := array_steps_monotone k A h
  have hs := hm i (max i j) j (max i j) (le_max_left _ _) (le_max_right _ _)
  simpa only [Fin.coe_max] using hs.trans (array_diagonal_value_bound k A h0 h (max i j))

theorem r2Array_value_le_endpoint (k : ℕ) (A : Fin (k + 3) → Fin (k + 3) → ℕ)
    (h : IsR2Array k A) (i j : Fin (k + 3)) : A i j ≤ k := by
  have hm := array_steps_monotone k A h.2.2.1
  have hl := hm i (Fin.last (k + 2)) j (Fin.last (k + 2)) (Fin.le_last i) (Fin.le_last j)
  simpa only [h.2.1] using hl

theorem boundary_array_steps (k : ℕ) (A : Fin (k + 3) → Fin (k + 3) → ℕ)
    (hm : ArrayMonotone k A)
    (he : ∀ i, A (Fin.last (k + 2)) i = k ∧ A i (Fin.last (k + 2)) = k)
    (hd : ∀ i j : Fin (k + 2), A i.succ j.succ ≤ A i.castSucc j.castSucc + 1) :
    ArraySteps k A := by
  constructor
  · intro i j
    constructor
    · exact hm i i j.castSucc j.succ le_rfl (Fin.castSucc_le_succ j)
    · rcases Fin.eq_castSucc_or_eq_last i with ⟨p, rfl⟩ | rfl
      · exact (hm p.castSucc p.succ j.succ j.succ (Fin.castSucc_le_succ p) le_rfl).trans (hd p j)
      · rw [(he j.succ).1, (he j.castSucc).1]
        omega
  · constructor
    · intro i j
      constructor
      · exact hm i.castSucc i.succ j j (Fin.castSucc_le_succ i) le_rfl
      · rcases Fin.eq_castSucc_or_eq_last j with ⟨q, rfl⟩ | rfl
        · exact (hm i.succ i.succ q.castSucc q.succ le_rfl (Fin.castSucc_le_succ q)).trans (hd i q)
        · rw [(he i.succ).2, (he i.castSucc).2]
          omega
    · intro i j
      exact ⟨hm i.castSucc i.succ j.castSucc j.succ
        (Fin.castSucc_le_succ i) (Fin.castSucc_le_succ j), hd i j⟩

theorem isR2Array_iff_boundary (k : ℕ) (A : Fin (k + 3) → Fin (k + 3) → ℕ) :
    IsR2Array k A ↔ BoundaryArray k A := by
  constructor
  · rintro ⟨h0, hend, hs, hb⟩
    have hm := array_steps_monotone k A hs
    have hbl : k ≤ A (Fin.last (k + 2)) 0 := by
      have h := (abs_le.mp (hb (Fin.last (k + 2)) 0)).1
      simp only [Fin.val_last, Fin.val_zero, max_eq_left (Nat.zero_le (k + 2))] at h
      omega
    have htr : k ≤ A 0 (Fin.last (k + 2)) := by
      have h := (abs_le.mp (hb 0 (Fin.last (k + 2)))).1
      simp only [Fin.val_last, Fin.val_zero, max_eq_right (Nat.zero_le (k + 2))] at h
      omega
    have hup (i j) : A i j ≤ k := by
      have h := hm i (Fin.last (k + 2)) j (Fin.last (k + 2)) (Fin.le_last i) (Fin.le_last j)
      simpa only [hend] using h
    refine ⟨h0, hm, ?_, fun i j => (hs.2.2 i j).2⟩
    intro i
    exact ⟨le_antisymm (hup _ _) (hbl.trans (hm _ _ 0 i le_rfl (Fin.zero_le i))),
      le_antisymm (hup _ _) (htr.trans (hm 0 i _ _ (Fin.zero_le i) le_rfl))⟩
  · rintro ⟨h0, hm, he, hd⟩
    have hs := boundary_array_steps k A hm he hd
    refine ⟨h0, (he (Fin.last (k + 2))).1, hs, ?_⟩
    intro i j
    have hu := array_value_le_max k A h0 hs i j
    have hv := fin_step_lipschitz (k + 2) (fun t => A t j)
      (fun t => (hs.2.1 t j).2) i (Fin.last (k + 2)) (Fin.le_last i)
    have hr := fin_step_lipschitz (k + 2) (A i)
      (fun t => (hs.1 i t).2) j (Fin.last (k + 2)) (Fin.le_last j)
    simp only [(he j).1, (he i).2, Fin.val_last] at hv hr
    rcases le_total i.val j.val with hij | hji
    · simp only [max_eq_right hij] at hu ⊢
      exact abs_le.mpr ⟨by omega, by omega⟩
    · simp only [max_eq_left hji] at hu ⊢
      exact abs_le.mpr ⟨by omega, by omega⟩

def r2ArrayToFin (k : ℕ) (A : R2Array k) : Fin (k + 3) → Fin (k + 3) → Fin (k + 3) :=
  fun i j => ⟨A.1 i j, by have h := r2Array_value_le_endpoint k A.1 A.2 i j; omega⟩

theorem r2ArrayToFin_injective (k : ℕ) : Function.Injective (r2ArrayToFin k) := by
  intro A B h
  apply Subtype.ext
  funext i j
  exact congrArg Fin.val (congrFun (congrFun h i) j)

theorem r2Array_finite (k : ℕ) : Finite (R2Array k) :=
  Finite.of_injective (r2ArrayToFin k) (r2ArrayToFin_injective k)

end Hardinian
