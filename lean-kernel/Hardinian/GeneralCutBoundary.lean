import Hardinian.CutPathCore
import Mathlib.Data.Nat.Find
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.SetTheory.Cardinal.Finite

namespace Hardinian.AllParameters

def IsLowerCut (m : ℕ) (C : Finset (Fin (m + 1) × Fin (m + 1))) : Prop :=
  ((0, 0) : Fin (m + 1) × Fin (m + 1)) ∈ C ∧
    (∀ p q : Fin (m + 1) × Fin (m + 1), q.1 ≤ p.1 → q.2 ≤ p.2 → p ∈ C → q ∈ C) ∧
    ∀ i, (Fin.last m, i) ∉ C ∧ (i, Fin.last m) ∉ C

def LowerCut (m : ℕ) := {C : Finset (Fin (m + 1) × Fin (m + 1)) // IsLowerCut m C}

def lowerCutNat {m : ℕ} (C : LowerCut m) (i j : ℕ) : Prop :=
  ∃ a b : Fin (m + 1), a.val = i ∧ b.val = j ∧ (a, b) ∈ C.1

theorem lowerCutNat_iff {m : ℕ} (C : LowerCut m) (i j : Fin (m + 1)) :
    lowerCutNat C i.val j.val ↔ (i, j) ∈ C.1 := by
  constructor
  · rintro ⟨a, b, ha, hb, hm⟩
    have he : a = i := Fin.ext ha
    have hf : b = j := Fin.ext hb
    simpa only [he, hf] using hm
  · intro h
    exact ⟨i, j, rfl, rfl, h⟩

theorem lowerCutNat_origin {m : ℕ} (C : LowerCut m) : lowerCutNat C 0 0 :=
  ⟨0, 0, rfl, rfl, C.2.1⟩

theorem lowerCutNat_lower {m : ℕ} (C : LowerCut m) (i j i' j' : ℕ)
    (hi : i' ≤ i) (hj : j' ≤ j) (h : lowerCutNat C i j) : lowerCutNat C i' j' := by
  rcases h with ⟨a, b, rfl, rfl, hm⟩
  let a' : Fin (m + 1) := ⟨i', lt_of_le_of_lt hi a.isLt⟩
  let b' : Fin (m + 1) := ⟨j', lt_of_le_of_lt hj b.isLt⟩
  exact ⟨a', b', rfl, rfl, C.2.2.1 (a, b) (a', b') hi hj hm⟩

theorem lowerCutNat_bounds {m : ℕ} (C : LowerCut m) (i j : ℕ)
    (h : lowerCutNat C i j) : i < m ∧ j < m := by
  rcases h with ⟨a, b, rfl, rfl, hm⟩
  have hna : a.val ≠ m := by
    intro ha
    have he : a = Fin.last m := Fin.ext ha
    exact (C.2.2.2 b).1 (by simpa only [he] using hm)
  have hnb : b.val ≠ m := by
    intro hb
    have he : b = Fin.last m := Fin.ext hb
    exact (C.2.2.2 a).2 (by simpa only [he] using hm)
  have ha := a.isLt
  have hb := b.isLt
  omega

noncomputable def lowerCutU {m : ℕ} (C : LowerCut m) : Fin m := by
  classical
  let u := Nat.findGreatest (fun i => lowerCutNat C i 0) m
  have hu : lowerCutNat C u 0 :=
    Nat.findGreatest_spec (P := fun i => lowerCutNat C i 0)
      (Nat.zero_le m) (lowerCutNat_origin C)
  exact ⟨u, (lowerCutNat_bounds C u 0 hu).1⟩

noncomputable def lowerCutV {m : ℕ} (C : LowerCut m) : Fin m := by
  classical
  let v := Nat.findGreatest (fun j => lowerCutNat C 0 j) m
  have hv : lowerCutNat C 0 v :=
    Nat.findGreatest_spec (P := fun j => lowerCutNat C 0 j)
      (Nat.zero_le m) (lowerCutNat_origin C)
  exact ⟨v, (lowerCutNat_bounds C 0 v hv).2⟩

theorem lowerCutU_mem {m : ℕ} (C : LowerCut m) : lowerCutNat C (lowerCutU C).val 0 := by
  classical
  change lowerCutNat C (Nat.findGreatest (fun i => lowerCutNat C i 0) m) 0
  exact Nat.findGreatest_spec (P := fun i => lowerCutNat C i 0)
    (Nat.zero_le m) (lowerCutNat_origin C)

theorem lowerCutV_mem {m : ℕ} (C : LowerCut m) : lowerCutNat C 0 (lowerCutV C).val := by
  classical
  change lowerCutNat C 0 (Nat.findGreatest (fun j => lowerCutNat C 0 j) m)
  exact Nat.findGreatest_spec (P := fun j => lowerCutNat C 0 j)
    (Nat.zero_le m) (lowerCutNat_origin C)

theorem lowerCutNat_endpoint_bounds {m : ℕ} (C : LowerCut m) (i j : ℕ)
    (h : lowerCutNat C i j) : i ≤ (lowerCutU C).val ∧ j ≤ (lowerCutV C).val := by
  classical
  have hb := lowerCutNat_bounds C i j h
  constructor
  · exact Nat.le_findGreatest hb.1.le (lowerCutNat_lower C i j i 0 le_rfl (Nat.zero_le _) h)
  · exact Nat.le_findGreatest hb.2.le (lowerCutNat_lower C i j 0 j (Nat.zero_le _) le_rfl h)

noncomputable def lowerCutShape {m : ℕ} (C : LowerCut m) :
    CutShape (lowerCutU C).val (lowerCutV C).val :=
  ⟨lowerCutNat C, lowerCutU_mem C, lowerCutV_mem C,
    lowerCutNat_lower C, lowerCutNat_endpoint_bounds C⟩

def BoundedGridPath (m : ℕ) := Σ u : Fin m, Σ v : Fin m, GridPath u.val v.val

noncomputable def gridPathCut (m : ℕ) (P : BoundedGridPath m) : LowerCut m := by
  classical
  refine ⟨Finset.univ.filter (fun p => pathCut P.2.2 p.1.val p.2.val), ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨0, Nat.zero_le _, Nat.zero_le _⟩
  · intro p q hi hj hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact (pathCut_isShape P.2.2).2.2.1 _ _ _ _ hi hj hp
  · intro i
    constructor
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro h
      have hb := (pathCut_isShape P.2.2).2.2.2 _ _ h
      have hu := P.1.isLt
      simp only [Fin.val_last] at hb
      omega
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro h
      have hb := (pathCut_isShape P.2.2).2.2.2 _ _ h
      have hv := P.2.1.isLt
      simp only [Fin.val_last] at hb
      omega

theorem mem_gridPathCut (m : ℕ) (P : BoundedGridPath m) (i j : Fin (m + 1)) :
    (i, j) ∈ (gridPathCut m P).1 ↔ pathCut P.2.2 i.val j.val := by
  classical
  simp only [gridPathCut, Finset.mem_filter, Finset.mem_univ, true_and]

theorem lowerCutNat_gridPathCut (m : ℕ) (P : BoundedGridPath m) (i j : ℕ) :
    lowerCutNat (gridPathCut m P) i j ↔ pathCut P.2.2 i j := by
  constructor
  · rintro ⟨a, b, rfl, rfl, h⟩
    exact (mem_gridPathCut m P a b).mp h
  · intro h
    have hb := (pathCut_isShape P.2.2).2.2.2 i j h
    have hu := P.1.isLt
    have hv := P.2.1.isLt
    let a : Fin (m + 1) := ⟨i, by omega⟩
    let b : Fin (m + 1) := ⟨j, by omega⟩
    exact ⟨a, b, rfl, rfl, (mem_gridPathCut m P a b).mpr h⟩

noncomputable def lowerCutPath {m : ℕ} (C : LowerCut m) : BoundedGridPath m :=
  ⟨lowerCutU C, lowerCutV C, boundaryPath (lowerCutShape C)⟩

theorem gridPathCut_lowerCutPath {m : ℕ} (C : LowerCut m) :
    gridPathCut m (lowerCutPath C) = C := by
  apply Subtype.ext
  apply Finset.ext
  rintro ⟨i, j⟩
  rw [mem_gridPathCut]
  have he : pathCut (boundaryPath (lowerCutShape C)) i.val j.val = lowerCutNat C i.val j.val :=
    congrFun (congrFun (congrArg Subtype.val (pathCut_boundaryPath (lowerCutShape C))) i.val) j.val
  change pathCut (boundaryPath (lowerCutShape C)) i.val j.val ↔ (i, j) ∈ C.1
  rw [he]
  exact lowerCutNat_iff C i j

theorem gridPathCut_injective (m : ℕ) : Function.Injective (gridPathCut m) := by
  rintro ⟨u, v, P⟩ ⟨u', v', Q⟩ h
  have hall (i j : ℕ) : pathCut P i j ↔ pathCut Q i j := by
    rw [← lowerCutNat_gridPathCut m ⟨u, v, P⟩ i j,
      ← lowerCutNat_gridPathCut m ⟨u', v', Q⟩ i j, h]
  have hu : u = u' := by
    apply Fin.ext
    apply le_antisymm
    · exact ((pathCut_isShape Q).2.2.2 _ _ ((hall _ _).mp (pathCut_isShape P).1)).1
    · exact ((pathCut_isShape P).2.2.2 _ _ ((hall _ _).mpr (pathCut_isShape Q).1)).1
  cases hu
  have hv : v = v' := by
    apply Fin.ext
    apply le_antisymm
    · exact ((pathCut_isShape Q).2.2.2 _ _ ((hall _ _).mp (pathCut_isShape P).2.1)).2
    · exact ((pathCut_isShape P).2.2.2 _ _ ((hall _ _).mpr (pathCut_isShape Q).2.1)).2
  cases hv
  have hp : P = Q := by
    apply pathCut_injective
    apply Subtype.ext
    funext i j
    exact propext (hall i j)
  cases hp
  rfl

theorem lowerCutPath_gridPathCut (m : ℕ) (P : BoundedGridPath m) :
    lowerCutPath (gridPathCut m P) = P :=
  gridPathCut_injective m (gridPathCut_lowerCutPath (gridPathCut m P))

noncomputable def lowerCutGridPathEquiv (m : ℕ) : LowerCut m ≃ BoundedGridPath m where
  toFun := lowerCutPath
  invFun := gridPathCut m
  left_inv := gridPathCut_lowerCutPath
  right_inv := lowerCutPath_gridPathCut m

theorem lowerCut_finite (m : ℕ) : Finite (LowerCut m) := by
  unfold LowerCut
  infer_instance

theorem lowerCut_card_eq_gridPaths (m : ℕ) : Nat.card (LowerCut m) = Nat.card (BoundedGridPath m) :=
  Nat.card_congr (lowerCutGridPathEquiv m)

theorem boundedGridPath_finite (m : ℕ) : Finite (BoundedGridPath m) := by
  letI := lowerCut_finite m
  exact Finite.of_equiv (LowerCut m) (lowerCutGridPathEquiv m)

theorem lowerCut_zero_empty : IsEmpty (LowerCut 0) :=
  ⟨fun C => Nat.not_lt_zero 0 (lowerCutNat_bounds C 0 0 (lowerCutNat_origin C)).1⟩

theorem boundedGridPath_zero_empty : IsEmpty (BoundedGridPath 0) :=
  ⟨fun P => Fin.elim0 P.1⟩

theorem lowerCut_zero_card : Nat.card (LowerCut 0) = 0 := by
  letI := lowerCut_zero_empty
  exact Nat.card_of_isEmpty

theorem boundedGridPath_zero_card : Nat.card (BoundedGridPath 0) = 0 := by
  letI := boundedGridPath_zero_empty
  exact Nat.card_of_isEmpty

/-- The positive premise only chooses a particular endpoint0; the main Equiv has none. -/
def zeroBoundedGridPath (m : ℕ) (hm : 0 < m) : BoundedGridPath m :=
  ⟨⟨0, hm⟩, ⟨0, hm⟩, zeroGridPath⟩

theorem zeroPathCut_singleton (m : ℕ) (hm : 0 < m) :
    (gridPathCut m (zeroBoundedGridPath m hm)).1 = {(0, 0)} := by
  apply Finset.ext
  rintro ⟨i, j⟩
  rw [mem_gridPathCut, Finset.mem_singleton]
  constructor
  · rintro ⟨t, hi, hj⟩
    change i.val ≤ 0 at hi
    change j.val ≤ 0 at hj
    have hi0 : i = 0 := Fin.ext (by change i.val = 0; omega)
    have hj0 : j = 0 := Fin.ext (by change j.val = 0; omega)
    exact Prod.ext hi0 hj0
  · intro h
    have hi : i = 0 := congrArg Prod.fst h
    have hj : j = 0 := congrArg Prod.snd h
    subst i
    subst j
    exact ⟨0, le_rfl, le_rfl⟩

theorem boundedGridPath_one_unique (P : BoundedGridPath 1) :
    P = zeroBoundedGridPath 1 Nat.zero_lt_one := by
  rcases P with ⟨u, v, P⟩
  have hu : u = 0 := Subsingleton.elim _ _
  cases hu
  have hv : v = 0 := Subsingleton.elim _ _
  cases hv
  have hp : P = zeroGridPath := gridPath_zero_unique P
  cases hp
  rfl

theorem boundedGridPath_one_card : Nat.card (BoundedGridPath 1) = 1 :=
  Nat.card_eq_one_iff_exists.mpr
    ⟨zeroBoundedGridPath 1 Nat.zero_lt_one, boundedGridPath_one_unique⟩

theorem lowerCut_one_card : Nat.card (LowerCut 1) = 1 :=
  (lowerCut_card_eq_gridPaths 1).trans boundedGridPath_one_card

theorem lowerCut_one_singleton (C : LowerCut 1) : C.1 = {(0, 0)} := by
  calc
    C.1 = (gridPathCut 1 (lowerCutPath C)).1 :=
      congrArg Subtype.val (gridPathCut_lowerCutPath C).symm
    _ = (gridPathCut 1 (zeroBoundedGridPath 1 Nat.zero_lt_one)).1 :=
      congrArg (fun P => (gridPathCut 1 P).1) (boundedGridPath_one_unique (lowerCutPath C))
    _ = _ := zeroPathCut_singleton 1 Nat.zero_lt_one

end Hardinian.AllParameters
