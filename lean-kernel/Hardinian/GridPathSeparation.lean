import Hardinian.CutPathCore

namespace Hardinian

def VertexDisjoint {u v u' v' : ℕ} (P : GridPath u v) (Q : GridPath u' v') : Prop :=
  ∀ s : Fin (u + v + 1), ∀ t : Fin (u' + v' + 1), P.1 s ≠ Q.1 t

def DiagContained (C D : ℕ → ℕ → Prop) : Prop :=
  ∀ i j : ℕ, C i j → D (i + 1) (j + 1)

def gridPathAt {u v : ℕ} (P : GridPath u v) (m : ℕ) (hm : m ≤ u + v) : ℕ × ℕ :=
  P.1 ⟨m, by omega⟩

theorem vertexDisjoint_symm {u v u' v' : ℕ} (P : GridPath u v) (Q : GridPath u' v')
    (h : VertexDisjoint P Q) : VertexDisjoint Q P := by
  intro t s he
  exact h s t he.symm

theorem gridPathAt_rank {u v : ℕ} (P : GridPath u v) (m : ℕ) (hm : m ≤ u + v) :
    (gridPathAt P m hm).2 + u = (gridPathAt P m hm).1 + m := by
  exact gridPath_rank P ⟨m, by omega⟩

theorem gridPathAt_last {u v : ℕ} (P : GridPath u v) (m : ℕ) (hm : m ≤ u + v)
    (he : m = u + v) : gridPathAt P m hm = (0, v) := by
  subst m
  exact P.2.2.1

theorem gridPathAt_col_step {u v : ℕ} (P : GridPath u v) (m n : ℕ)
    (hm : m ≤ u + v) (hn : n ≤ u + v) (he : n = m + 1) :
    (gridPathAt P m hm).2 ≤ (gridPathAt P n hn).2 ∧
      (gridPathAt P n hn).2 ≤ (gridPathAt P m hm).2 + 1 := by
  subst n
  have hs := P.2.2.2 ⟨m, by omega⟩
  change GridStep (gridPathAt P m hm) (gridPathAt P (m + 1) hn) at hs
  rcases hs with hs | hs <;> omega

theorem ordered_paths_aligned_col_lt {u v u' v' : ℕ}
    (P : GridPath u v) (Q : GridPath u' v') (hu : u < u')
    (hd : VertexDisjoint P Q) (m : ℕ)
    (hp : m ≤ u + v) (hq : m + (u' - u) ≤ u' + v') :
    (gridPathAt P m hp).2 < (gridPathAt Q (m + (u' - u)) hq).2 := by
  have hsource : u + (u' - u) = u' := by omega
  revert hp hq
  induction m with
  | zero =>
    intro hp hq
    have hrp := gridPathAt_rank P 0 hp
    have hrq := gridPathAt_rank Q (0 + (u' - u)) hq
    have hpc : (gridPathAt P 0 hp).2 = 0 := congrArg Prod.snd P.2.1
    have hne : gridPathAt P 0 hp ≠ gridPathAt Q (0 + (u' - u)) hq := hd _ _
    by_contra hn
    apply hne
    exact Prod.ext (by omega) (by omega)
  | succ m ih =>
    intro hp hq
    have hp0 : m ≤ u + v := by omega
    have hq0 : m + (u' - u) ≤ u' + v' := by omega
    have hprev := ih hp0 hq0
    have hps := gridPathAt_col_step P m (m + 1) hp0 hp rfl
    have hqs := gridPathAt_col_step Q (m + (u' - u)) ((m + 1) + (u' - u))
      hq0 hq (by omega)
    have hrp := gridPathAt_rank P (m + 1) hp
    have hrq := gridPathAt_rank Q ((m + 1) + (u' - u)) hq
    have hne : gridPathAt P (m + 1) hp ≠ gridPathAt Q ((m + 1) + (u' - u)) hq := hd _ _
    by_contra hn
    apply hne
    exact Prod.ext (by omega) (by omega)

theorem ordered_paths_sink_lt {u v u' v' : ℕ}
    (P : GridPath u v) (Q : GridPath u' v') (hu : u < u')
    (hd : VertexDisjoint P Q) : v < v' := by
  by_contra hn
  have hp : u + v' ≤ u + v := by omega
  have hq : (u + v') + (u' - u) ≤ u' + v' := by omega
  have hcol := ordered_paths_aligned_col_lt P Q hu hd (u + v') hp hq
  have hr := gridPathAt_rank P (u + v') hp
  have hend := gridPathAt_last Q ((u + v') + (u' - u)) hq (by omega)
  have hlast := congrArg Prod.snd hend
  omega

theorem diagonal_paths_vertexDisjoint {u v u' v' : ℕ}
    (P : GridPath u v) (Q : GridPath u' v')
    (hdiag : DiagContained (pathCut P) (pathCut Q)) : VertexDisjoint P Q := by
  intro s t he
  have h := hdiag (P.1 s).1 (P.1 s).2 ⟨s, le_rfl, le_rfl⟩
  apply (gridPath_vertex_boundary Q t).2
  simpa only [he] using h

theorem ordered_paths_diagonal {u v u' v' : ℕ}
    (P : GridPath u v) (Q : GridPath u' v') (hu : u < u')
    (hd : VertexDisjoint P Q) : DiagContained (pathCut P) (pathCut Q) := by
  have hv := ordered_paths_sink_lt P Q hu hd
  intro i j h
  obtain ⟨t, hi, hj⟩ := h
  have hp : t.val ≤ u + v := by omega
  have hq : t.val + (u' - u) ≤ u' + v' := by omega
  have hcol := ordered_paths_aligned_col_lt P Q hu hd t.val hp hq
  have hrp := gridPathAt_rank P t.val hp
  have hrq := gridPathAt_rank Q (t.val + (u' - u)) hq
  have hi' : i ≤ (gridPathAt P t.val hp).1 := hi
  have hj' : j ≤ (gridPathAt P t.val hp).2 := hj
  refine ⟨⟨t.val + (u' - u), by omega⟩, ?_, ?_⟩
  · change i + 1 ≤ (gridPathAt Q (t.val + (u' - u)) hq).1
    omega
  · change j + 1 ≤ (gridPathAt Q (t.val + (u' - u)) hq).2
    omega

theorem ordered_paths_disjoint_iff_diagonal {u v u' v' : ℕ}
    (P : GridPath u v) (Q : GridPath u' v') (hu : u < u') :
    VertexDisjoint P Q ↔ DiagContained (pathCut P) (pathCut Q) := by
  exact ⟨ordered_paths_diagonal P Q hu, diagonal_paths_vertexDisjoint P Q⟩

theorem zero_paths_not_vertexDisjoint (P Q : GridPath 0 0) : ¬ VertexDisjoint P Q := by
  intro hd
  exact hd 0 0 ((gridPath_zero_vertices P 0).trans (gridPath_zero_vertices Q 0).symm)

end Hardinian
