import Hardinian.CutPathCore

namespace Hardinian

theorem splice_rank {u v u' v' : ℕ} (P : GridPath u v) (Q : GridPath u' v')
    (a : Fin (u + v + 1)) (b : Fin (u' + v' + 1)) (h : P.1 a = Q.1 b) :
    a.val + u' = b.val + u := by
  have hp := gridPath_rank P a
  have hq := gridPath_rank Q b
  rw [h] at hp
  omega

theorem splice_lengths {u v u' v' : ℕ} (P : GridPath u v) (Q : GridPath u' v')
    (a : Fin (u + v + 1)) (b : Fin (u' + v' + 1)) (h : P.1 a = Q.1 b) :
    a.val + (u' + v' - b.val) = u + v' ∧
      b.val + (u + v - a.val) = u' + v := by
  have hr := splice_rank P Q a b h
  have ha := a.isLt
  have hb := b.isLt
  constructor <;> omega

theorem splice_cut_bound {u v u' v' : ℕ} (P : GridPath u v) (Q : GridPath u' v')
    (a : Fin (u + v + 1)) (b : Fin (u' + v' + 1)) (h : P.1 a = Q.1 b) :
    a.val < u + v' + 1 := by
  have hl := (splice_lengths P Q a b h).1
  omega

theorem splice_tail_bound {u v u' v' : ℕ} (P : GridPath u v) (Q : GridPath u' v')
    (a : Fin (u + v + 1)) (b : Fin (u' + v' + 1)) (h : P.1 a = Q.1 b)
    (t : Fin (u + v' + 1)) (ht : ¬ t.val ≤ a.val) :
    b.val + (t.val - a.val) < u' + v' + 1 := by
  have hr := splice_rank P Q a b h
  have hb := b.isLt
  have htt := t.isLt
  omega

def spliceVertex {u v u' v' : ℕ} (P : GridPath u v) (Q : GridPath u' v')
    (a : Fin (u + v + 1)) (b : Fin (u' + v' + 1)) (h : P.1 a = Q.1 b)
    (t : Fin (u + v' + 1)) : ℕ × ℕ :=
  if ht : t.val ≤ a.val then P.1 ⟨t.val, by have ha := a.isLt; omega⟩
  else Q.1 ⟨b.val + (t.val - a.val), splice_tail_bound P Q a b h t ht⟩

theorem spliceVertex_prefix {u v u' v' : ℕ} (P : GridPath u v) (Q : GridPath u' v')
    (a : Fin (u + v + 1)) (b : Fin (u' + v' + 1)) (h : P.1 a = Q.1 b)
    (t : Fin (u + v' + 1)) (ht : t.val ≤ a.val) :
    spliceVertex P Q a b h t = P.1 ⟨t.val, by omega⟩ := by
  simp only [spliceVertex, dif_pos ht]

theorem spliceVertex_tail {u v u' v' : ℕ} (P : GridPath u v) (Q : GridPath u' v')
    (a : Fin (u + v + 1)) (b : Fin (u' + v' + 1)) (h : P.1 a = Q.1 b)
    (t : Fin (u + v' + 1)) (ht : ¬ t.val ≤ a.val) :
    spliceVertex P Q a b h t =
      Q.1 ⟨b.val + (t.val - a.val), splice_tail_bound P Q a b h t ht⟩ := by
  simp only [spliceVertex, dif_neg ht]

theorem spliceVertex_isPath {u v u' v' : ℕ} (P : GridPath u v) (Q : GridPath u' v')
    (a : Fin (u + v + 1)) (b : Fin (u' + v' + 1)) (h : P.1 a = Q.1 b) :
    IsGridPath u v' (spliceVertex P Q a b h) := by
  have hr := splice_rank P Q a b h
  have ha := a.isLt
  have hb := b.isLt
  refine ⟨?_, ?_, ?_⟩
  · rw [spliceVertex_prefix P Q a b h 0 (by simp)]
    exact P.2.1
  · by_cases ht : u + v' ≤ a.val
    · rw [spliceVertex_prefix P Q a b h (Fin.last (u + v')) ht]
      change P.1 ⟨u + v', _⟩ = (0, v')
      have ea : (⟨u + v', by omega⟩ : Fin (u + v + 1)) = a :=
        Fin.ext (by change u + v' = a.val; omega)
      have eb : b = Fin.last (u' + v') :=
        Fin.ext (by change b.val = u' + v'; omega)
      rw [ea, h, eb]
      exact Q.2.2.1
    · rw [spliceVertex_tail P Q a b h (Fin.last (u + v')) ht]
      change Q.1 ⟨b.val + (u + v' - a.val), _⟩ = (0, v')
      have eb : (⟨b.val + (u + v' - a.val), by omega⟩ : Fin (u' + v' + 1)) =
          Fin.last (u' + v') := Fin.ext (by change b.val + (u + v' - a.val) = u' + v'; omega)
      rw [eb]
      exact Q.2.2.1
  · intro t
    have htt := t.isLt
    by_cases hn : t.val + 1 ≤ a.val
    · have hc : t.val ≤ a.val := by omega
      rw [spliceVertex_prefix P Q a b h t.castSucc hc,
        spliceVertex_prefix P Q a b h t.succ hn]
      exact P.2.2.2 ⟨t.val, by omega⟩
    · by_cases hc : t.val ≤ a.val
      · rw [spliceVertex_prefix P Q a b h t.castSucc hc,
          spliceVertex_tail P Q a b h t.succ hn]
        change GridStep (P.1 ⟨t.val, _⟩) (Q.1 ⟨b.val + (t.val + 1 - a.val), _⟩)
        have ea : (⟨t.val, by omega⟩ : Fin (u + v + 1)) = a :=
          Fin.ext (by change t.val = a.val; omega)
        have en : (⟨b.val + (t.val + 1 - a.val), by omega⟩ : Fin (u' + v' + 1)) =
            (⟨b.val, by omega⟩ : Fin (u' + v')).succ :=
          Fin.ext (by change b.val + (t.val + 1 - a.val) = b.val + 1; omega)
        rw [ea, h, en]
        exact Q.2.2.2 ⟨b.val, by omega⟩
      · rw [spliceVertex_tail P Q a b h t.castSucc hc,
          spliceVertex_tail P Q a b h t.succ hn]
        change GridStep (Q.1 ⟨b.val + (t.val - a.val), _⟩)
          (Q.1 ⟨b.val + (t.val + 1 - a.val), _⟩)
        have en : (⟨b.val + (t.val + 1 - a.val), by omega⟩ : Fin (u' + v' + 1)) =
            (⟨b.val + (t.val - a.val), by omega⟩ : Fin (u' + v')).succ :=
          Fin.ext (by change b.val + (t.val + 1 - a.val) = b.val + (t.val - a.val) + 1; omega)
        rw [en]
        exact Q.2.2.2 ⟨b.val + (t.val - a.val), by omega⟩

def gridPathSplice {u v u' v' : ℕ} (P : GridPath u v) (Q : GridPath u' v')
    (a : Fin (u + v + 1)) (b : Fin (u' + v' + 1)) (h : P.1 a = Q.1 b) :
    GridPath u v' := ⟨spliceVertex P Q a b h, spliceVertex_isPath P Q a b h⟩

def spliceCut {u v u' v' : ℕ} (P : GridPath u v) (Q : GridPath u' v')
    (a : Fin (u + v + 1)) (b : Fin (u' + v' + 1)) (h : P.1 a = Q.1 b) :
    Fin (u + v' + 1) := ⟨a.val, splice_cut_bound P Q a b h⟩

theorem gridPathSplice_cut {u v u' v' : ℕ} (P : GridPath u v) (Q : GridPath u' v')
    (a : Fin (u + v + 1)) (b : Fin (u' + v' + 1)) (h : P.1 a = Q.1 b) :
    (gridPathSplice P Q a b h).1 (spliceCut P Q a b h) = P.1 a := by
  exact spliceVertex_prefix P Q a b h (spliceCut P Q a b h) le_rfl

theorem gridPathSplice_meet {u v u' v' : ℕ} (P : GridPath u v) (Q : GridPath u' v')
    (a : Fin (u + v + 1)) (b : Fin (u' + v' + 1)) (h : P.1 a = Q.1 b) :
    (gridPathSplice P Q a b h).1 (spliceCut P Q a b h) =
      (gridPathSplice Q P b a h.symm).1 (spliceCut Q P b a h.symm) := by
  rw [gridPathSplice_cut, gridPathSplice_cut]
  exact h

theorem gridPathSplice_recover {u v u' v' : ℕ} (P : GridPath u v) (Q : GridPath u' v')
    (a : Fin (u + v + 1)) (b : Fin (u' + v' + 1)) (h : P.1 a = Q.1 b) :
    gridPathSplice (gridPathSplice P Q a b h) (gridPathSplice Q P b a h.symm)
      (spliceCut P Q a b h) (spliceCut Q P b a h.symm)
      (gridPathSplice_meet P Q a b h) = P := by
  apply Subtype.ext
  funext t
  change spliceVertex (gridPathSplice P Q a b h) (gridPathSplice Q P b a h.symm)
    (spliceCut P Q a b h) (spliceCut Q P b a h.symm)
    (gridPathSplice_meet P Q a b h) t = P.1 t
  by_cases ht : t.val ≤ a.val
  · rw [spliceVertex_prefix (gridPathSplice P Q a b h) (gridPathSplice Q P b a h.symm)
      (spliceCut P Q a b h) (spliceCut Q P b a h.symm) (gridPathSplice_meet P Q a b h) t ht]
    exact spliceVertex_prefix P Q a b h _ ht
  · rw [spliceVertex_tail (gridPathSplice P Q a b h) (gridPathSplice Q P b a h.symm)
      (spliceCut P Q a b h) (spliceCut Q P b a h.symm) (gridPathSplice_meet P Q a b h) t ht]
    change spliceVertex Q P b a h.symm
      ⟨b.val + (t.val - a.val), _⟩ = P.1 t
    rw [spliceVertex_tail Q P b a h.symm _ (by dsimp only; omega)]
    apply congrArg P.1
    apply Fin.ext
    dsimp only
    omega

def tailSwap {u v u' v' : ℕ} (P : GridPath u v) (Q : GridPath u' v')
    (a : Fin (u + v + 1)) (b : Fin (u' + v' + 1)) (h : P.1 a = Q.1 b) :
    GridPath u v' × GridPath u' v :=
  (gridPathSplice P Q a b h, gridPathSplice Q P b a h.symm)

theorem tailSwap_involutive {u v u' v' : ℕ} (P : GridPath u v) (Q : GridPath u' v')
    (a : Fin (u + v + 1)) (b : Fin (u' + v' + 1)) (h : P.1 a = Q.1 b) :
    tailSwap (tailSwap P Q a b h).1 (tailSwap P Q a b h).2
      (spliceCut P Q a b h) (spliceCut Q P b a h.symm)
      (gridPathSplice_meet P Q a b h) = (P, Q) := by
  apply Prod.ext
  · exact gridPathSplice_recover P Q a b h
  · exact gridPathSplice_recover Q P b a h.symm

def gridGrade (p : ℕ × ℕ) : ℤ := (p.2 : ℤ) - (p.1 : ℤ)

theorem gridPath_grade {u v : ℕ} (P : GridPath u v) (t : Fin (u + v + 1)) :
    gridGrade (P.1 t) = (t.val : ℤ) - (u : ℤ) := by
  have hr := gridPath_rank P t
  unfold gridGrade
  omega

theorem gridPath_grade_le_iff {u v : ℕ} (P : GridPath u v)
    (s t : Fin (u + v + 1)) : gridGrade (P.1 s) ≤ gridGrade (P.1 t) ↔ s.val ≤ t.val := by
  rw [gridPath_grade, gridPath_grade]
  omega

theorem gridPathSplice_prefix_visits {u v u' v' : ℕ} (P : GridPath u v) (Q : GridPath u' v')
    (a : Fin (u + v + 1)) (b : Fin (u' + v' + 1)) (h : P.1 a = Q.1 b)
    (p : ℕ × ℕ) (hp : gridGrade p ≤ gridGrade (P.1 a)) :
    (∃ t, (gridPathSplice P Q a b h).1 t = p) ↔ ∃ t, P.1 t = p := by
  constructor
  · rintro ⟨t, ht⟩
    have hg := gridPath_grade (gridPathSplice P Q a b h) t
    have ha := gridPath_grade P a
    rw [ht] at hg
    have hb : t.val ≤ a.val := by omega
    refine ⟨⟨t.val, by have hlt := a.isLt; omega⟩, ?_⟩
    exact (spliceVertex_prefix P Q a b h t hb).symm.trans ht
  · rintro ⟨t, ht⟩
    have hg := gridPath_grade P t
    have ha := gridPath_grade P a
    rw [ht] at hg
    have hb : t.val ≤ a.val := by omega
    refine ⟨⟨t.val, by have hlt := splice_cut_bound P Q a b h; omega⟩, ?_⟩
    exact (spliceVertex_prefix P Q a b h _ hb).trans ht

theorem tailSwap_labelled_prefix {u v u' v' : ℕ} (P : GridPath u v) (Q : GridPath u' v')
    (a : Fin (u + v + 1)) (b : Fin (u' + v' + 1)) (h : P.1 a = Q.1 b)
    (p : ℕ × ℕ) (hp : gridGrade p ≤ gridGrade (P.1 a)) :
    ((∃ t, (tailSwap P Q a b h).1.1 t = p) ↔ ∃ t, P.1 t = p) ∧
      ((∃ t, (tailSwap P Q a b h).2.1 t = p) ↔ ∃ t, Q.1 t = p) := by
  exact ⟨gridPathSplice_prefix_visits P Q a b h p hp,
    gridPathSplice_prefix_visits Q P b a h.symm p (by simpa only [← h] using hp)⟩

theorem gridPathSplice_source {u v u' v' : ℕ} (P : GridPath u v) (Q : GridPath u' v')
    (a : Fin (u + v + 1)) (b : Fin (u' + v' + 1)) (h : P.1 a = Q.1 b) :
    (gridPathSplice P Q a b h).1 0 = (u, 0) := (gridPathSplice P Q a b h).2.1

theorem gridPathSplice_sink {u v u' v' : ℕ} (P : GridPath u v) (Q : GridPath u' v')
    (a : Fin (u + v + 1)) (b : Fin (u' + v' + 1)) (h : P.1 a = Q.1 b) :
    (gridPathSplice P Q a b h).1 (Fin.last (u + v')) = (0, v') :=
  (gridPathSplice P Q a b h).2.2.1

theorem gridPathSplice_step {u v u' v' : ℕ} (P : GridPath u v) (Q : GridPath u' v')
    (a : Fin (u + v + 1)) (b : Fin (u' + v' + 1)) (h : P.1 a = Q.1 b)
    (t : Fin (u + v')) :
    GridStep ((gridPathSplice P Q a b h).1 t.castSucc)
      ((gridPathSplice P Q a b h).1 t.succ) := (gridPathSplice P Q a b h).2.2.2 t

theorem tailSwap_zero : tailSwap zeroGridPath zeroGridPath 0 0 rfl =
    (zeroGridPath, zeroGridPath) := by
  apply Prod.ext <;> apply gridPath_zero_unique

end Hardinian
