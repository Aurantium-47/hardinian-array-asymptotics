import Hardinian.CutPathCore
import Mathlib.Data.Nat.Find
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.SetTheory.Cardinal.Finite

namespace Hardinian

def IsLowerCut (k : ℕ) (C : Finset (Fin (k + 3) × Fin (k + 3))) : Prop :=
  ((0, 0) : Fin (k + 3) × Fin (k + 3)) ∈ C ∧
    (∀ p q : Fin (k + 3) × Fin (k + 3), q.1 ≤ p.1 → q.2 ≤ p.2 → p ∈ C → q ∈ C) ∧
    ∀ i, (Fin.last (k + 2), i) ∉ C ∧ (i, Fin.last (k + 2)) ∉ C

def LowerCut (k : ℕ) := {C : Finset (Fin (k + 3) × Fin (k + 3)) // IsLowerCut k C}

def lowerCutNat {k : ℕ} (C : LowerCut k) (i j : ℕ) : Prop :=
  ∃ a b : Fin (k + 3), a.val = i ∧ b.val = j ∧ (a, b) ∈ C.1

theorem lowerCutNat_iff {k : ℕ} (C : LowerCut k) (i j : Fin (k + 3)) :
    lowerCutNat C i.val j.val ↔ (i, j) ∈ C.1 := by
  constructor
  · rintro ⟨a, b, ha, hb, hm⟩
    have he : a = i := Fin.ext ha
    have hf : b = j := Fin.ext hb
    simpa only [he, hf] using hm
  · intro h
    exact ⟨i, j, rfl, rfl, h⟩

theorem lowerCutNat_origin {k : ℕ} (C : LowerCut k) : lowerCutNat C 0 0 :=
  ⟨0, 0, rfl, rfl, C.2.1⟩

theorem lowerCutNat_lower {k : ℕ} (C : LowerCut k) (i j i' j' : ℕ)
    (hi : i' ≤ i) (hj : j' ≤ j) (h : lowerCutNat C i j) : lowerCutNat C i' j' := by
  rcases h with ⟨a, b, rfl, rfl, hm⟩
  let a' : Fin (k + 3) := ⟨i', lt_of_le_of_lt hi a.isLt⟩
  let b' : Fin (k + 3) := ⟨j', lt_of_le_of_lt hj b.isLt⟩
  exact ⟨a', b', rfl, rfl, C.2.2.1 (a, b) (a', b') hi hj hm⟩

theorem lowerCutNat_bounds {k : ℕ} (C : LowerCut k) (i j : ℕ)
    (h : lowerCutNat C i j) : i ≤ k + 1 ∧ j ≤ k + 1 := by
  rcases h with ⟨a, b, rfl, rfl, hm⟩
  constructor
  · by_contra hn
    have he : a = Fin.last (k + 2) := Fin.ext (by have ha := a.isLt; omega)
    exact (C.2.2.2 b).1 (by simpa only [he] using hm)
  · by_contra hn
    have he : b = Fin.last (k + 2) := Fin.ext (by have hb := b.isLt; omega)
    exact (C.2.2.2 a).2 (by simpa only [he] using hm)

noncomputable def lowerCutU {k : ℕ} (C : LowerCut k) : Fin (k + 2) := by
  classical
  exact ⟨Nat.findGreatest (fun i => lowerCutNat C i 0) (k + 1),
    Nat.lt_succ_of_le (Nat.findGreatest_le _)⟩

noncomputable def lowerCutV {k : ℕ} (C : LowerCut k) : Fin (k + 2) := by
  classical
  exact ⟨Nat.findGreatest (fun j => lowerCutNat C 0 j) (k + 1),
    Nat.lt_succ_of_le (Nat.findGreatest_le _)⟩

theorem lowerCutU_mem {k : ℕ} (C : LowerCut k) : lowerCutNat C (lowerCutU C).val 0 := by
  classical
  exact Nat.findGreatest_spec (Nat.zero_le (k + 1)) (lowerCutNat_origin C)

theorem lowerCutV_mem {k : ℕ} (C : LowerCut k) : lowerCutNat C 0 (lowerCutV C).val := by
  classical
  exact Nat.findGreatest_spec (Nat.zero_le (k + 1)) (lowerCutNat_origin C)

theorem lowerCutNat_endpoint_bounds {k : ℕ} (C : LowerCut k) (i j : ℕ)
    (h : lowerCutNat C i j) : i ≤ (lowerCutU C).val ∧ j ≤ (lowerCutV C).val := by
  classical
  have hb := lowerCutNat_bounds C i j h
  constructor
  · exact Nat.le_findGreatest hb.1 (lowerCutNat_lower C i j i 0 le_rfl (Nat.zero_le _) h)
  · exact Nat.le_findGreatest hb.2 (lowerCutNat_lower C i j 0 j (Nat.zero_le _) le_rfl h)

noncomputable def lowerCutShape {k : ℕ} (C : LowerCut k) :
    CutShape (lowerCutU C).val (lowerCutV C).val :=
  ⟨lowerCutNat C, lowerCutU_mem C, lowerCutV_mem C,
    lowerCutNat_lower C, lowerCutNat_endpoint_bounds C⟩

def BoundedGridPath (k : ℕ) := Σ u : Fin (k + 2), Σ v : Fin (k + 2), GridPath u.val v.val

noncomputable def gridPathCut (k : ℕ) (P : BoundedGridPath k) : LowerCut k := by
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

theorem mem_gridPathCut (k : ℕ) (P : BoundedGridPath k) (i j : Fin (k + 3)) :
    (i, j) ∈ (gridPathCut k P).1 ↔ pathCut P.2.2 i.val j.val := by
  classical
  simp only [gridPathCut, Finset.mem_filter, Finset.mem_univ, true_and]

theorem lowerCutNat_gridPathCut (k : ℕ) (P : BoundedGridPath k) (i j : ℕ) :
    lowerCutNat (gridPathCut k P) i j ↔ pathCut P.2.2 i j := by
  constructor
  · rintro ⟨a, b, rfl, rfl, h⟩
    exact (mem_gridPathCut k P a b).mp h
  · intro h
    have hb := (pathCut_isShape P.2.2).2.2.2 i j h
    have hu := P.1.isLt
    have hv := P.2.1.isLt
    let a : Fin (k + 3) := ⟨i, by omega⟩
    let b : Fin (k + 3) := ⟨j, by omega⟩
    exact ⟨a, b, rfl, rfl, (mem_gridPathCut k P a b).mpr h⟩

noncomputable def lowerCutPath {k : ℕ} (C : LowerCut k) : BoundedGridPath k :=
  ⟨lowerCutU C, lowerCutV C, boundaryPath (lowerCutShape C)⟩

theorem gridPathCut_lowerCutPath {k : ℕ} (C : LowerCut k) :
    gridPathCut k (lowerCutPath C) = C := by
  apply Subtype.ext
  apply Finset.ext
  rintro ⟨i, j⟩
  rw [mem_gridPathCut]
  have he : pathCut (boundaryPath (lowerCutShape C)) i.val j.val = lowerCutNat C i.val j.val :=
    congrFun (congrFun (congrArg Subtype.val (pathCut_boundaryPath (lowerCutShape C))) i.val) j.val
  change pathCut (boundaryPath (lowerCutShape C)) i.val j.val ↔ (i, j) ∈ C.1
  rw [he]
  exact lowerCutNat_iff C i j

theorem gridPathCut_injective (k : ℕ) : Function.Injective (gridPathCut k) := by
  rintro ⟨u, v, P⟩ ⟨u', v', Q⟩ h
  have hall (i j : ℕ) : pathCut P i j ↔ pathCut Q i j := by
    rw [← lowerCutNat_gridPathCut k ⟨u, v, P⟩ i j,
      ← lowerCutNat_gridPathCut k ⟨u', v', Q⟩ i j, h]
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

theorem lowerCutPath_gridPathCut (k : ℕ) (P : BoundedGridPath k) :
    lowerCutPath (gridPathCut k P) = P :=
  gridPathCut_injective k (gridPathCut_lowerCutPath (gridPathCut k P))

noncomputable def lowerCutGridPathEquiv (k : ℕ) : LowerCut k ≃ BoundedGridPath k where
  toFun := lowerCutPath
  invFun := gridPathCut k
  left_inv := gridPathCut_lowerCutPath
  right_inv := lowerCutPath_gridPathCut k

theorem lowerCut_finite (k : ℕ) : Finite (LowerCut k) := by
  unfold LowerCut
  infer_instance

theorem lowerCut_card_eq_gridPaths (k : ℕ) : Nat.card (LowerCut k) = Nat.card (BoundedGridPath k) :=
  Nat.card_congr (lowerCutGridPathEquiv k)

theorem zeroPathCut_singleton (k : ℕ) :
    (gridPathCut k ⟨0, 0, zeroGridPath⟩).1 = {(0, 0)} := by
  apply Finset.ext
  rintro ⟨i, j⟩
  rw [mem_gridPathCut, Finset.mem_singleton]
  constructor
  · rintro ⟨t, hi, hj⟩
    change i.val ≤ 0 at hi
    change j.val ≤ 0 at hj
    exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
  · intro h
    have hi := congrArg (fun p : Fin (k + 3) × Fin (k + 3) => p.1.val) h
    have hj := congrArg (fun p : Fin (k + 3) × Fin (k + 3) => p.2.val) h
    exact ⟨0, by change i.val ≤ 0; omega, by change j.val ≤ 0; omega⟩

end Hardinian
