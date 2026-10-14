import Hardinian.GridPathSeparation
import Hardinian.CutBoundary
import Hardinian.SeparatedCuts

namespace Hardinian

def OrderedPathFamily (k : ℕ) :=
  {P : Fin k → BoundedGridPath k //
    StrictMono (fun t => (P t).1) ∧
      ∀ s t : Fin k, s ≠ t → VertexDisjoint (P s).2.2 (P t).2.2}

theorem family_sinks_strictMono (k : ℕ) (F : OrderedPathFamily k) :
    StrictMono (fun t => (F.1 t).2.1) := by
  intro s t hst
  exact ordered_paths_sink_lt (F.1 s).2.2 (F.1 t).2.2
    (F.2.1 hst) (F.2.2 s t (ne_of_lt hst))

theorem family_diagonal (k : ℕ) (F : OrderedPathFamily k) (s t : Fin k) (hst : s < t) :
    DiagContained (pathCut (F.1 s).2.2) (pathCut (F.1 t).2.2) :=
  ordered_paths_diagonal (F.1 s).2.2 (F.1 t).2.2
    (F.2.1 hst) (F.2.2 s t (ne_of_lt hst))

def separatedLowerCut {k : ℕ} (C : SeparatedCuts k) (t : Fin k) : LowerCut k :=
  ⟨C.1 t, (C.2.2.2.1 t).1, C.2.1 t, (C.2.2.2.1 t).2⟩

theorem lowerCutPath_cut {k : ℕ} (C : LowerCut k) (i j : ℕ) :
    pathCut (lowerCutPath C).2.2 i j ↔ lowerCutNat C i j := by
  rw [← lowerCutNat_gridPathCut, gridPathCut_lowerCutPath]

theorem separatedLowerCut_diagonal {k : ℕ} (C : SeparatedCuts k)
    (s t : Fin k) (hst : s < t) :
    DiagContained (lowerCutNat (separatedLowerCut C s))
      (lowerCutNat (separatedLowerCut C t)) := by
  intro i j h
  have hb := lowerCutNat_bounds (separatedLowerCut C s) i j h
  let a : Fin (k + 2) := ⟨i, by omega⟩
  let b : Fin (k + 2) := ⟨j, by omega⟩
  let r : Fin k := ⟨s.val + 1, by have ht := t.isLt; change s.val < t.val at hst; omega⟩
  have hm : (a.castSucc, b.castSucc) ∈ C.1 s :=
    (lowerCutNat_iff (separatedLowerCut C s) a.castSucc b.castSucc).mp h
  have hn := C.2.2.2.2 s r rfl a b hm
  have hrt : r ≤ t := by change s.val + 1 ≤ t.val; change s.val < t.val at hst; omega
  exact (lowerCutNat_iff (separatedLowerCut C t) a.succ b.succ).mpr (C.2.2.1 hrt hn)

theorem separatedLowerCut_sources {k : ℕ} (C : SeparatedCuts k) :
    StrictMono (fun t => lowerCutU (separatedLowerCut C t)) := by
  intro s t hst
  have hd := separatedLowerCut_diagonal C s t hst
    (lowerCutU (separatedLowerCut C s)).val 0 (lowerCutU_mem (separatedLowerCut C s))
  have hb := (lowerCutNat_endpoint_bounds (separatedLowerCut C t) _ _ hd).1
  change (lowerCutU (separatedLowerCut C s)).val < (lowerCutU (separatedLowerCut C t)).val
  omega

theorem separatedLowerCut_paths_disjoint {k : ℕ} (C : SeparatedCuts k)
    (s t : Fin k) (hst : s < t) :
    VertexDisjoint (lowerCutPath (separatedLowerCut C s)).2.2
      (lowerCutPath (separatedLowerCut C t)).2.2 := by
  apply diagonal_paths_vertexDisjoint
  intro i j h
  exact (lowerCutPath_cut (separatedLowerCut C t) _ _).mpr
    (separatedLowerCut_diagonal C s t hst i j
      ((lowerCutPath_cut (separatedLowerCut C s) i j).mp h))

noncomputable def cutsToPathFamily {k : ℕ} (C : SeparatedCuts k) : OrderedPathFamily k := by
  refine ⟨fun t => lowerCutPath (separatedLowerCut C t), separatedLowerCut_sources C, ?_⟩
  intro s t hst
  rcases lt_or_gt_of_ne hst with hlt | hgt
  · exact separatedLowerCut_paths_disjoint C s t hlt
  · exact vertexDisjoint_symm _ _ (separatedLowerCut_paths_disjoint C t s hgt)

noncomputable def familyToSeparatedCuts {k : ℕ} (F : OrderedPathFamily k) : SeparatedCuts k := by
  refine ⟨fun t => (gridPathCut k (F.1 t)).1, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t
    exact (gridPathCut k (F.1 t)).2.2.1
  · intro s t hst p hp
    rcases lt_or_eq_of_le hst with hlt | he
    · have hd := family_diagonal k F s t hlt p.1.val p.2.val
        ((mem_gridPathCut k (F.1 s) p.1 p.2).mp hp)
      apply (mem_gridPathCut k (F.1 t) p.1 p.2).mpr
      exact (pathCut_isShape (F.1 t).2.2).2.2.1 _ _ _ _ (by omega) (by omega) hd
    · simpa only [he] using hp
  · intro t
    exact ⟨(gridPathCut k (F.1 t)).2.1, (gridPathCut k (F.1 t)).2.2.2⟩
  · intro s t hst i j hp
    have hlt : s < t := by change s.val < t.val; omega
    exact (mem_gridPathCut k (F.1 t) i.succ j.succ).mpr
      (family_diagonal k F s t hlt i.val j.val
        ((mem_gridPathCut k (F.1 s) i.castSucc j.castSucc).mp hp))

theorem familyToSeparatedCuts_cutsToPathFamily {k : ℕ} (C : SeparatedCuts k) :
    familyToSeparatedCuts (cutsToPathFamily C) = C := by
  apply Subtype.ext
  funext t
  exact congrArg Subtype.val (gridPathCut_lowerCutPath (separatedLowerCut C t))

theorem cutsToPathFamily_familyToSeparatedCuts {k : ℕ} (F : OrderedPathFamily k) :
    cutsToPathFamily (familyToSeparatedCuts F) = F := by
  apply Subtype.ext
  funext t
  exact lowerCutPath_gridPathCut k (F.1 t)

noncomputable def separatedCutsPathFamilyEquiv (k : ℕ) :
    SeparatedCuts k ≃ OrderedPathFamily k where
  toFun := cutsToPathFamily
  invFun := familyToSeparatedCuts
  left_inv := familyToSeparatedCuts_cutsToPathFamily
  right_inv := cutsToPathFamily_familyToSeparatedCuts

noncomputable def arrayPathFamilyEquiv (k : ℕ) : R2Array k ≃ OrderedPathFamily k :=
  (arrayCutsEquiv k).trans (separatedCutsPathFamilyEquiv k)

theorem pathFamily_finite (k : ℕ) : Finite (OrderedPathFamily k) := by
  letI := separatedCuts_finite k
  exact Finite.of_equiv (SeparatedCuts k) (separatedCutsPathFamilyEquiv k)

theorem separatedCuts_card_eq_pathFamily (k : ℕ) :
    Nat.card (SeparatedCuts k) = Nat.card (OrderedPathFamily k) :=
  Nat.card_congr (separatedCutsPathFamilyEquiv k)

theorem array_card_eq_pathFamily (k : ℕ) :
    Nat.card (R2Array k) = Nat.card (OrderedPathFamily k) :=
  Nat.card_congr (arrayPathFamilyEquiv k)

theorem pathFamily_zero_card : Nat.card (OrderedPathFamily 0) = 1 := by
  rw [← separatedCuts_card_eq_pathFamily, separatedCuts_zero_card]

end Hardinian
