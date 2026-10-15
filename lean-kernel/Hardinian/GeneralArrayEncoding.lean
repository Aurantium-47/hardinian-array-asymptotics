import Hardinian.ArrayEncoding

namespace Hardinian.AllParameters

/-- The level count k and the band parameter r are independent. -/
def ArraySteps (r k : ℕ) (A : Fin (k + r + 1) → Fin (k + r + 1) → ℕ) : Prop :=
  (∀ i : Fin (k + r + 1), ∀ j : Fin (k + r),
    A i j.castSucc ≤ A i j.succ ∧ A i j.succ ≤ A i j.castSucc + 1) ∧
  (∀ i : Fin (k + r), ∀ j : Fin (k + r + 1),
    A i.castSucc j ≤ A i.succ j ∧ A i.succ j ≤ A i.castSucc j + 1) ∧
  (∀ i j : Fin (k + r), A i.castSucc j.castSucc ≤ A i.succ j.succ ∧
    A i.succ j.succ ≤ A i.castSucc j.castSucc + 1)

def ArrayMonotone (r k : ℕ) (A : Fin (k + r + 1) → Fin (k + r + 1) → ℕ) : Prop :=
  ∀ i i' j j', i ≤ i' → j ≤ j' → A i j ≤ A i' j'

def IsSquareArray (r k : ℕ) (A : Fin (k + r + 1) → Fin (k + r + 1) → ℕ) : Prop :=
  A 0 0 = 0 ∧ A (Fin.last (k + r)) (Fin.last (k + r)) = k ∧ ArraySteps r k A ∧
    ∀ i j, |(A i j : ℤ) - ((max i.val j.val : ℕ) : ℤ)| ≤ (r : ℤ)

def SquareArray (r k : ℕ) : Type :=
  {A : Fin (k + r + 1) → Fin (k + r + 1) → ℕ // IsSquareArray r k A}

def BoundaryArray (r k : ℕ) (A : Fin (k + r + 1) → Fin (k + r + 1) → ℕ) : Prop :=
  A 0 0 = 0 ∧ ArrayMonotone r k A ∧
    (∀ i, A (Fin.last (k + r)) i = k ∧ A i (Fin.last (k + r)) = k) ∧
    ∀ i j : Fin (k + r), A i.succ j.succ ≤ A i.castSucc j.castSucc + 1

theorem array_steps_monotone (r k : ℕ)
    (A : Fin (k + r + 1) → Fin (k + r + 1) → ℕ)
    (h : ArraySteps r k A) : ArrayMonotone r k A := by
  have hr (i) : Monotone (A i) := Fin.monotone_iff_le_succ.mpr (fun j => (h.1 i j).1)
  have hv (j) : Monotone (fun i => A i j) :=
    Fin.monotone_iff_le_succ.mpr (fun i => (h.2.1 i j).1)
  intro i i' j j' hi hj
  exact (hv j hi).trans (hr i' hj)

theorem array_diagonal_value_bound (r k : ℕ)
    (A : Fin (k + r + 1) → Fin (k + r + 1) → ℕ)
    (h0 : A 0 0 = 0) (h : ArraySteps r k A) (i : Fin (k + r + 1)) :
    A i i ≤ i.val := by
  have hi := Hardinian.fin_step_lipschitz (k + r) (fun t => A t t)
    (fun t => (h.2.2 t t).2) 0 i (Fin.zero_le i)
  simp only [h0, Fin.val_zero, Nat.cast_zero, sub_zero] at hi
  exact_mod_cast hi

theorem array_value_le_max (r k : ℕ)
    (A : Fin (k + r + 1) → Fin (k + r + 1) → ℕ)
    (h0 : A 0 0 = 0) (h : ArraySteps r k A) (i j : Fin (k + r + 1)) :
    A i j ≤ max i.val j.val := by
  have hm := array_steps_monotone r k A h
  have hs := hm i (max i j) j (max i j) (le_max_left _ _) (le_max_right _ _)
  simpa only [Fin.coe_max] using
    hs.trans (array_diagonal_value_bound r k A h0 h (max i j))

theorem squareArray_value_le_endpoint (r k : ℕ)
    (A : Fin (k + r + 1) → Fin (k + r + 1) → ℕ)
    (h : IsSquareArray r k A) (i j : Fin (k + r + 1)) : A i j ≤ k := by
  have hm := array_steps_monotone r k A h.2.2.1
  have hl := hm i (Fin.last (k + r)) j (Fin.last (k + r)) (Fin.le_last i) (Fin.le_last j)
  simpa only [h.2.1] using hl

theorem boundary_array_steps (r k : ℕ)
    (A : Fin (k + r + 1) → Fin (k + r + 1) → ℕ)
    (hm : ArrayMonotone r k A)
    (he : ∀ i, A (Fin.last (k + r)) i = k ∧ A i (Fin.last (k + r)) = k)
    (hd : ∀ i j : Fin (k + r), A i.succ j.succ ≤ A i.castSucc j.castSucc + 1) :
    ArraySteps r k A := by
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

theorem isSquareArray_iff_boundary (r k : ℕ)
    (A : Fin (k + r + 1) → Fin (k + r + 1) → ℕ) :
    IsSquareArray r k A ↔ BoundaryArray r k A := by
  constructor
  · rintro ⟨h0, hend, hs, hb⟩
    have hm := array_steps_monotone r k A hs
    have hbl : k ≤ A (Fin.last (k + r)) 0 := by
      have h := (abs_le.mp (hb (Fin.last (k + r)) 0)).1
      simp only [Fin.val_last, Fin.val_zero, max_eq_left (Nat.zero_le (k + r))] at h
      omega
    have htr : k ≤ A 0 (Fin.last (k + r)) := by
      have h := (abs_le.mp (hb 0 (Fin.last (k + r)))).1
      simp only [Fin.val_last, Fin.val_zero, max_eq_right (Nat.zero_le (k + r))] at h
      omega
    have hup (i j) : A i j ≤ k := by
      have h := hm i (Fin.last (k + r)) j (Fin.last (k + r)) (Fin.le_last i) (Fin.le_last j)
      simpa only [hend] using h
    refine ⟨h0, hm, ?_, fun i j => (hs.2.2 i j).2⟩
    intro i
    exact ⟨le_antisymm (hup _ _) (hbl.trans (hm _ _ 0 i le_rfl (Fin.zero_le i))),
      le_antisymm (hup _ _) (htr.trans (hm 0 i _ _ (Fin.zero_le i) le_rfl))⟩
  · rintro ⟨h0, hm, he, hd⟩
    have hs := boundary_array_steps r k A hm he hd
    refine ⟨h0, (he (Fin.last (k + r))).1, hs, ?_⟩
    intro i j
    have hu := array_value_le_max r k A h0 hs i j
    have hv := Hardinian.fin_step_lipschitz (k + r) (fun t => A t j)
      (fun t => (hs.2.1 t j).2) i (Fin.last (k + r)) (Fin.le_last i)
    have hr := Hardinian.fin_step_lipschitz (k + r) (A i)
      (fun t => (hs.1 i t).2) j (Fin.last (k + r)) (Fin.le_last j)
    simp only [(he j).1, (he i).2, Fin.val_last] at hv hr
    rcases le_total i.val j.val with hij | hji
    · simp only [max_eq_right hij] at hu ⊢
      exact abs_le.mpr ⟨by omega, by omega⟩
    · simp only [max_eq_left hji] at hu ⊢
      exact abs_le.mpr ⟨by omega, by omega⟩

def squareArrayToFin (r k : ℕ) (A : SquareArray r k) :
    Fin (k + r + 1) → Fin (k + r + 1) → Fin (k + 1) :=
  fun i j => ⟨A.1 i j, by have h := squareArray_value_le_endpoint r k A.1 A.2 i j; omega⟩

theorem squareArrayToFin_injective (r k : ℕ) :
    Function.Injective (squareArrayToFin r k) := by
  intro A B h
  apply Subtype.ext
  funext i j
  exact congrArg Fin.val (congrFun (congrFun h i) j)

theorem squareArray_finite (r k : ℕ) : Finite (SquareArray r k) :=
  Finite.of_injective (squareArrayToFin r k) (squareArrayToFin_injective r k)

theorem squareArray_zero_band_value (k : ℕ) (A : SquareArray 0 k)
    (i j : Fin (k + 0 + 1)) : A.1 i j = max i.val j.val := by
  have h := abs_le.mp (A.2.2.2.2 i j)
  norm_num at h
  omega

theorem squareArray_zero_levels_value (r : ℕ) (A : SquareArray r 0)
    (i j : Fin (0 + r + 1)) : A.1 i j = 0 :=
  Nat.eq_zero_of_le_zero (squareArray_value_le_endpoint r 0 A.1 A.2 i j)

def zeroLevelArray (r : ℕ) : SquareArray r 0 :=
  ⟨fun _ _ => 0, (isSquareArray_iff_boundary r 0 _).mpr
    ⟨rfl, fun _ _ _ _ _ _ => le_rfl, fun _ => ⟨rfl, rfl⟩, fun _ _ => Nat.zero_le 1⟩⟩

theorem squareArray_zero_levels_eq (r : ℕ) (A : SquareArray r 0) :
    A = zeroLevelArray r := by
  apply Subtype.ext
  funext i j
  exact squareArray_zero_levels_value r A i j

theorem squareArray_zero_levels_card (r : ℕ) : Nat.card (SquareArray r 0) = 1 :=
  Nat.card_eq_one_iff_exists.mpr ⟨zeroLevelArray r, squareArray_zero_levels_eq r⟩

theorem squareArray_zero_dimension_card : Nat.card (SquareArray 0 0) = 1 :=
  squareArray_zero_levels_card 0

end Hardinian.AllParameters
