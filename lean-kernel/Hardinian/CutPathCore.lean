import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.NormNum

namespace Hardinian

def GridStep (p q : ℕ × ℕ) : Prop :=
  (q.1 = p.1 ∧ q.2 = p.2 + 1) ∨ (q.1 + 1 = p.1 ∧ q.2 = p.2)

def IsGridPath (u v : ℕ) (p : Fin (u + v + 1) → ℕ × ℕ) : Prop :=
  p 0 = (u, 0) ∧ p (Fin.last (u + v)) = (0, v) ∧
    ∀ t : Fin (u + v), GridStep (p t.castSucc) (p t.succ)

def GridPath (u v : ℕ) := {p : Fin (u + v + 1) → ℕ × ℕ // IsGridPath u v p}

theorem gridPath_row_antitone {u v : ℕ} (P : GridPath u v) :
    Antitone (fun t => (P.1 t).1) := by
  apply Fin.antitone_iff_succ_le.mpr
  intro t
  rcases P.2.2.2 t with h | h <;> omega

theorem gridPath_col_monotone {u v : ℕ} (P : GridPath u v) :
    Monotone (fun t => (P.1 t).2) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro t
  rcases P.2.2.2 t with h | h <;> omega

theorem gridPath_bounds {u v : ℕ} (P : GridPath u v) (t : Fin (u + v + 1)) :
    (P.1 t).1 ≤ u ∧ (P.1 t).2 ≤ v := by
  have hr := gridPath_row_antitone P (Fin.zero_le t)
  have hc := gridPath_col_monotone P (Fin.le_last t)
  simpa only [P.2.1, P.2.2.1] using And.intro hr hc

theorem gridPath_rank {u v : ℕ} (P : GridPath u v) (t : Fin (u + v + 1)) :
    (P.1 t).2 + u = (P.1 t).1 + t.val := by
  induction t using Fin.induction with
  | zero => simp only [P.2.1, Fin.val_zero, Nat.zero_add, Nat.add_zero]
  | succ t ih =>
    have hs := P.2.2.2 t
    change (P.1 t.castSucc).2 + u = (P.1 t.castSucc).1 + t.val at ih
    change (P.1 t.succ).2 + u = (P.1 t.succ).1 + (t.val + 1)
    rcases hs with hs | hs <;> omega

theorem gridPath_injective {u v : ℕ} (P : GridPath u v) : Function.Injective P.1 := by
  intro s t h
  have hs := gridPath_rank P s
  have ht := gridPath_rank P t
  rw [h] at hs
  apply Fin.ext
  omega

def IsCutShape (u v : ℕ) (C : ℕ → ℕ → Prop) : Prop :=
  C u 0 ∧ C 0 v ∧
    (∀ i j i' j', i' ≤ i → j' ≤ j → C i j → C i' j') ∧
    ∀ i j, C i j → i ≤ u ∧ j ≤ v

def CutShape (u v : ℕ) := {C : ℕ → ℕ → Prop // IsCutShape u v C}

def ShapeBoundary {u v : ℕ} (C : CutShape u v) (p : ℕ × ℕ) : Prop :=
  C.1 p.1 p.2 ∧ ¬ C.1 (p.1 + 1) (p.2 + 1)

theorem shape_source_boundary {u v : ℕ} (C : CutShape u v) :
    ShapeBoundary C (u, 0) := by
  refine ⟨C.2.1, ?_⟩
  intro h
  have hb := C.2.2.2.2 _ _ h
  omega

theorem shape_sink_boundary {u v : ℕ} (C : CutShape u v) :
    ShapeBoundary C (0, v) := by
  refine ⟨C.2.2.1, ?_⟩
  intro h
  have hb := C.2.2.2.2 _ _ h
  omega

theorem shape_boundary_unique {u v r : ℕ} (C : CutShape u v) (p q : ℕ × ℕ)
    (hp : ShapeBoundary C p) (hq : ShapeBoundary C q)
    (hrp : p.2 + u = p.1 + r) (hrq : q.2 + u = q.1 + r) : p = q := by
  have hi : p.1 = q.1 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hp.2 (C.2.2.2.1 q.1 q.2 (p.1 + 1) (p.2 + 1) (by omega) (by omega) hq.1)
    · exact hq.2 (C.2.2.2.1 p.1 p.2 (q.1 + 1) (q.2 + 1) (by omega) (by omega) hp.1)
  have hj : p.2 = q.2 := by omega
  exact Prod.ext hi hj

theorem shape_boundary_next {u v r : ℕ} (C : CutShape u v) (p : ℕ × ℕ)
    (hp : ShapeBoundary C p) (hr : p.2 + u = p.1 + r) (hlt : r < u + v) :
    ∃ q, ShapeBoundary C q ∧ q.2 + u = q.1 + (r + 1) ∧ GridStep p q := by
  classical
  by_cases he : C.1 p.1 (p.2 + 1)
  · refine ⟨(p.1, p.2 + 1), ⟨he, ?_⟩, by omega, Or.inl ⟨rfl, rfl⟩⟩
    intro h
    exact hp.2 (C.2.2.2.1 _ _ _ _ le_rfl (by omega) h)
  · have hi : 0 < p.1 := by
      have hb := C.2.2.2.2 _ _ hp.1
      by_contra hz
      have hv : p.2 + 1 ≤ v := by omega
      exact he (C.2.2.2.1 0 v p.1 (p.2 + 1) (by omega) hv C.2.2.1)
    refine ⟨(p.1 - 1, p.2), ⟨?_, ?_⟩, by omega, Or.inr ⟨by omega, rfl⟩⟩
    · exact C.2.2.2.1 _ _ _ _ (by omega) le_rfl hp.1
    · intro h
      apply he
      convert h using 1 <;> omega

theorem shape_boundary_exists {u v : ℕ} (C : CutShape u v) (r : ℕ) (hr : r ≤ u + v) :
    ∃ p, ShapeBoundary C p ∧ p.2 + u = p.1 + r := by
  revert hr
  induction r with
  | zero => intro hr; exact ⟨(u, 0), shape_source_boundary C, by omega⟩
  | succ r ih =>
    intro hr
    obtain ⟨p, hp, he⟩ := ih (by omega)
    obtain ⟨q, hq, hqe, _⟩ := shape_boundary_next C p hp he (by omega)
    exact ⟨q, hq, hqe⟩

noncomputable def boundaryPoint {u v : ℕ} (C : CutShape u v) (t : Fin (u + v + 1)) : ℕ × ℕ :=
  Classical.choose (shape_boundary_exists C t.val (by omega))

theorem boundaryPoint_spec {u v : ℕ} (C : CutShape u v) (t : Fin (u + v + 1)) :
    ShapeBoundary C (boundaryPoint C t) ∧
      (boundaryPoint C t).2 + u = (boundaryPoint C t).1 + t.val :=
  Classical.choose_spec (shape_boundary_exists C t.val (by omega))

theorem boundaryPoint_isPath {u v : ℕ} (C : CutShape u v) :
    IsGridPath u v (boundaryPoint C) := by
  refine ⟨?_, ?_, ?_⟩
  · exact shape_boundary_unique C _ _ (boundaryPoint_spec C 0).1
      (shape_source_boundary C) (boundaryPoint_spec C 0).2 (by simp)
  · exact shape_boundary_unique C _ _ (boundaryPoint_spec C (Fin.last (u + v))).1
      (shape_sink_boundary C) (boundaryPoint_spec C (Fin.last (u + v))).2 (by simp [Nat.add_comm])
  · intro t
    obtain ⟨q, hq, hr, hs⟩ := shape_boundary_next C (boundaryPoint C t.castSucc)
      (boundaryPoint_spec C t.castSucc).1 (boundaryPoint_spec C t.castSucc).2 t.isLt
    have he : q = boundaryPoint C t.succ := shape_boundary_unique C _ _ hq
      (boundaryPoint_spec C t.succ).1 hr (boundaryPoint_spec C t.succ).2
    simpa only [he] using hs

noncomputable def boundaryPath {u v : ℕ} (C : CutShape u v) : GridPath u v :=
  ⟨boundaryPoint C, boundaryPoint_isPath C⟩

def pathCut {u v : ℕ} (P : GridPath u v) (i j : ℕ) : Prop :=
  ∃ t, i ≤ (P.1 t).1 ∧ j ≤ (P.1 t).2

theorem pathCut_isShape {u v : ℕ} (P : GridPath u v) : IsCutShape u v (pathCut P) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨0, by simp only [P.2.1, le_refl, and_self]⟩
  · exact ⟨Fin.last (u + v), by simp only [P.2.2.1, le_refl, and_self]⟩
  · intro i j i' j' hi hj h
    obtain ⟨t, ht, hs⟩ := h
    exact ⟨t, hi.trans ht, hj.trans hs⟩
  · intro i j h
    obtain ⟨t, hi, hj⟩ := h
    exact ⟨hi.trans (gridPath_bounds P t).1, hj.trans (gridPath_bounds P t).2⟩

def pathCutShape {u v : ℕ} (P : GridPath u v) : CutShape u v :=
  ⟨pathCut P, pathCut_isShape P⟩

theorem gridPath_vertex_boundary {u v : ℕ} (P : GridPath u v) (t : Fin (u + v + 1)) :
    ShapeBoundary (pathCutShape P) (P.1 t) := by
  refine ⟨⟨t, le_rfl, le_rfl⟩, ?_⟩
  rintro ⟨s, hs, ht⟩
  rcases le_total t s with hts | hst
  · have h := gridPath_row_antitone P hts
    dsimp only at h
    omega
  · have h := gridPath_col_monotone P hst
    dsimp only at h
    omega

theorem pathCut_boundaryPath {u v : ℕ} (C : CutShape u v) : pathCutShape (boundaryPath C) = C := by
  apply Subtype.ext
  funext i j
  apply propext
  constructor
  · rintro ⟨t, hi, hj⟩
    exact C.2.2.2.1 _ _ i j hi hj (boundaryPoint_spec C t).1.1
  · intro h
    have hb := C.2.2.2.2 i j h
    let t : Fin (u + v + 1) := ⟨j + u - i, by omega⟩
    have hr := (boundaryPoint_spec C t).2
    change (boundaryPoint C t).2 + u = (boundaryPoint C t).1 + (j + u - i) at hr
    have hi : i ≤ (boundaryPoint C t).1 := by
      by_contra hn
      exact (boundaryPoint_spec C t).1.2
        (C.2.2.2.1 i j _ _ (by omega) (by omega) h)
    refine ⟨t, hi, ?_⟩
    change j ≤ (boundaryPoint C t).2
    omega

theorem boundaryPath_pathCut {u v : ℕ} (P : GridPath u v) : boundaryPath (pathCutShape P) = P := by
  apply Subtype.ext
  funext t
  exact shape_boundary_unique (pathCutShape P) _ _ (boundaryPoint_spec (pathCutShape P) t).1
    (gridPath_vertex_boundary P t) (boundaryPoint_spec (pathCutShape P) t).2 (gridPath_rank P t)

noncomputable def cutShapePathEquiv (u v : ℕ) : CutShape u v ≃ GridPath u v where
  toFun := boundaryPath
  invFun := pathCutShape
  left_inv := pathCut_boundaryPath
  right_inv := boundaryPath_pathCut

theorem pathCut_injective {u v : ℕ} : Function.Injective (@pathCutShape u v) := by
  intro P Q h
  rw [← boundaryPath_pathCut P, ← boundaryPath_pathCut Q, h]

theorem gridPath_zero_vertices (P : GridPath 0 0) (t : Fin (0 + 0 + 1)) : P.1 t = (0, 0) := by
  have h := gridPath_bounds P t
  exact Prod.ext (by omega) (by omega)

def zeroGridPath : GridPath 0 0 :=
  ⟨fun _ => (0, 0), rfl, rfl, fun t => Fin.elim0 t⟩

theorem gridPath_zero_unique (P : GridPath 0 0) : P = zeroGridPath := by
  apply Subtype.ext
  funext t
  exact gridPath_zero_vertices P t

theorem gridWalk_length_forced {L u v : ℕ} (p : Fin (L + 1) → ℕ × ℕ)
    (h0 : p 0 = (u, 0)) (hl : p (Fin.last L) = (0, v))
    (hs : ∀ t : Fin L, GridStep (p t.castSucc) (p t.succ)) : L = u + v := by
  have hr (t : Fin (L + 1)) : (p t).2 + u = (p t).1 + t.val := by
    induction t using Fin.induction with
    | zero => simp only [h0, Fin.val_zero, Nat.zero_add, Nat.add_zero]
    | succ t ih =>
      have h := hs t
      change (p t.castSucc).2 + u = (p t.castSucc).1 + t.val at ih
      change (p t.succ).2 + u = (p t.succ).1 + (t.val + 1)
      rcases h with h | h <;> omega
  have h := hr (Fin.last L)
  simp only [hl, Fin.val_last, Nat.zero_add] at h
  omega

end Hardinian
