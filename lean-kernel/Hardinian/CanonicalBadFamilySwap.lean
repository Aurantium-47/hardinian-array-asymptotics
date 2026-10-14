import Hardinian.MarkedPathFamilySwap
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Image
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.Prod

namespace Hardinian

def IsBadFamily {k N : ℕ} {u v : Fin k → Fin (N + 1)} (F : SignedFamily u v) : Prop :=
  ∃ i j : Fin k, i ≠ j ∧ ∃ s t, (F.2 i).1 s = (F.2 j).1 t

abbrev BadFamily {k N : ℕ} (u v : Fin k → Fin (N + 1)) :=
  {F : SignedFamily u v // IsBadFamily F}

abbrev IntersectionAnchor (N k : ℕ) :=
  (Fin (N + 1) × Fin (N + 1)) × (Fin k × Fin k)

abbrev IntersectionKey := ℕ ×ₗ (ℕ ×ₗ (ℕ ×ₗ (ℕ ×ₗ ℕ)))

def anchorVertex {N k : ℕ} (a : IntersectionAnchor N k) : ℕ × ℕ :=
  (a.1.1.val, a.1.2.val)

def anchorGrade {N k : ℕ} (a : IntersectionAnchor N k) : ℕ :=
  a.1.2.val + N - a.1.1.val

def anchorKey {N k : ℕ} (a : IntersectionAnchor N k) : IntersectionKey :=
  toLex (anchorGrade a, toLex (a.1.1.val, toLex (a.1.2.val, toLex (a.2.1.val, a.2.2.val))))

theorem anchorKey_injective {N k : ℕ} : Function.Injective (@anchorKey N k) := by
  intro a b h
  simp only [anchorKey, toLex_inj, Prod.mk.injEq] at h
  exact Prod.ext (Prod.ext (Fin.ext h.2.1) (Fin.ext h.2.2.1))
    (Prod.ext (Fin.ext h.2.2.2.1) (Fin.ext h.2.2.2.2))

theorem anchorGrade_eq_gamma {N k : ℕ} (a : IntersectionAnchor N k) :
    (anchorGrade a : ℤ) = gridGrade (anchorVertex a) + (N : ℤ) := by
  have hr := a.1.1.isLt
  change ((a.1.2.val + N - a.1.1.val : ℕ) : ℤ) =
    (a.1.2.val : ℤ) - (a.1.1.val : ℤ) + (N : ℤ)
  omega

def IsIntersectionAnchor {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (F : SignedFamily u v) (a : IntersectionAnchor N k) : Prop :=
  a.2.1 < a.2.2 ∧ familyVisits F a.2.1 (anchorVertex a) ∧ familyVisits F a.2.2 (anchorVertex a)

noncomputable def intersectionAnchors {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (F : SignedFamily u v) : Finset (IntersectionAnchor N k) := by
  classical
  exact Finset.univ.filter (IsIntersectionAnchor F)

noncomputable def intersectionKeys {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (F : SignedFamily u v) : Finset IntersectionKey := by
  classical
  exact (intersectionAnchors F).image anchorKey

theorem mem_intersectionAnchors {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (F : SignedFamily u v) (a : IntersectionAnchor N k) :
    a ∈ intersectionAnchors F ↔ IsIntersectionAnchor F a := by
  classical
  simp only [intersectionAnchors, Finset.mem_filter, Finset.mem_univ, true_and]

theorem bad_of_intersectionAnchor {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (F : SignedFamily u v) (a : IntersectionAnchor N k) (ha : IsIntersectionAnchor F a) :
    IsBadFamily F := by
  obtain ⟨s, hs⟩ := ha.2.1
  obtain ⟨t, ht⟩ := ha.2.2
  exact ⟨a.2.1, a.2.2, ne_of_lt ha.1, s, t, hs.trans ht.symm⟩

theorem intersectionAnchors_nonempty {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (F : SignedFamily u v) (h : IsBadFamily F) : (intersectionAnchors F).Nonempty := by
  obtain ⟨i, j, hij, s, t, hst⟩ := h
  have hb := gridPath_bounds (F.2 i) s
  have hu := (u i).isLt
  have hv := (v (F.1 i)).isLt
  let p : Fin (N + 1) × Fin (N + 1) :=
    (⟨((F.2 i).1 s).1, by omega⟩, ⟨((F.2 i).1 s).2, by omega⟩)
  have hp : (p.1.val, p.2.val) = (F.2 i).1 s := Prod.ext rfl rfl
  rcases lt_or_gt_of_ne hij with hij | hji
  · refine ⟨(p, (i, j)), (mem_intersectionAnchors F _).2 ?_⟩
    exact ⟨hij, ⟨s, hp.symm⟩, ⟨t, hst.symm.trans hp.symm⟩⟩
  · refine ⟨(p, (j, i)), (mem_intersectionAnchors F _).2 ?_⟩
    exact ⟨hji, ⟨t, hst.symm.trans hp.symm⟩, ⟨s, hp.symm⟩⟩

theorem intersectionAnchors_nonempty_iff {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (F : SignedFamily u v) : (intersectionAnchors F).Nonempty ↔ IsBadFamily F := by
  constructor
  · rintro ⟨a, ha⟩
    exact bad_of_intersectionAnchor F a ((mem_intersectionAnchors F a).1 ha)
  · exact intersectionAnchors_nonempty F

theorem intersectionKeys_nonempty {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (F : SignedFamily u v) (h : IsBadFamily F) : (intersectionKeys F).Nonempty := by
  classical
  exact (intersectionAnchors_nonempty F h).image anchorKey

def rankVisitTime (u : ℕ) (p : ℕ × ℕ) : ℕ := p.2 + u - p.1

theorem gridPath_visit_time {u v : ℕ} (P : GridPath u v) (p : ℕ × ℕ)
    (t : Fin (u + v + 1)) (ht : P.1 t = p) : rankVisitTime u p = t.val := by
  have hr := gridPath_rank P t
  rw [ht] at hr
  unfold rankVisitTime
  omega

theorem gridPath_visit_time_lt {u v : ℕ} (P : GridPath u v) (p : ℕ × ℕ)
    (hp : ∃ t, P.1 t = p) : rankVisitTime u p < u + v + 1 := by
  obtain ⟨t, ht⟩ := hp
  rw [gridPath_visit_time P p t ht]
  exact t.isLt

theorem gridPath_visit_at_time {u v : ℕ} (P : GridPath u v) (p : ℕ × ℕ)
    (hp : ∃ t, P.1 t = p) :
    P.1 ⟨rankVisitTime u p, gridPath_visit_time_lt P p hp⟩ = p := by
  obtain ⟨t, ht⟩ := hp
  have he := gridPath_visit_time P p t ht
  have hb : rankVisitTime u p < u + v + 1 := by rw [he]; exact t.isLt
  have hf : (⟨rankVisitTime u p, hb⟩ : Fin (u + v + 1)) = t := Fin.ext he
  exact (congrArg P.1 hf).trans ht

noncomputable def firstIntersectionKey {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (B : BadFamily u v) : IntersectionKey :=
  (intersectionKeys B.1).min' (intersectionKeys_nonempty B.1 B.2)

theorem firstIntersectionKey_mem {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (B : BadFamily u v) : firstIntersectionKey B ∈ intersectionKeys B.1 :=
  Finset.min'_mem _ _

theorem firstIntersectionKey_exists_anchor {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (B : BadFamily u v) :
    ∃ a, a ∈ intersectionAnchors B.1 ∧ anchorKey a = firstIntersectionKey B := by
  classical
  have h := firstIntersectionKey_mem B
  change firstIntersectionKey B ∈ (intersectionAnchors B.1).image anchorKey at h
  exact Finset.mem_image.mp h

noncomputable def firstIntersectionAnchor {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (B : BadFamily u v) : IntersectionAnchor N k :=
  Classical.choose (firstIntersectionKey_exists_anchor B)

theorem firstIntersectionAnchor_mem {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (B : BadFamily u v) : firstIntersectionAnchor B ∈ intersectionAnchors B.1 :=
  (Classical.choose_spec (firstIntersectionKey_exists_anchor B)).1

theorem firstIntersectionAnchor_key {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (B : BadFamily u v) : anchorKey (firstIntersectionAnchor B) = firstIntersectionKey B :=
  (Classical.choose_spec (firstIntersectionKey_exists_anchor B)).2

noncomputable def canonicalMark {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (B : BadFamily u v) : MarkedFamily u v := by
  let a := firstIntersectionAnchor B
  have ha : IsIntersectionAnchor B.1 a := (mem_intersectionAnchors B.1 a).1 (firstIntersectionAnchor_mem B)
  refine ⟨B.1, a.2.1, a.2.2, ha.1,
    rankVisitTime (u a.2.1).val (anchorVertex a), rankVisitTime (u a.2.2).val (anchorVertex a),
    gridPath_visit_time_lt (B.1.2 a.2.1) (anchorVertex a) ha.2.1,
    gridPath_visit_time_lt (B.1.2 a.2.2) (anchorVertex a) ha.2.2, ?_⟩
  exact (gridPath_visit_at_time (B.1.2 a.2.1) (anchorVertex a) ha.2.1).trans
    (gridPath_visit_at_time (B.1.2 a.2.2) (anchorVertex a) ha.2.2).symm

theorem canonicalMark_family {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (B : BadFamily u v) : (canonicalMark B).family = B.1 := rfl

theorem canonicalMark_point {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (B : BadFamily u v) : markedPoint (canonicalMark B) = anchorVertex (firstIntersectionAnchor B) := by
  exact gridPath_visit_at_time (B.1.2 (firstIntersectionAnchor B).2.1)
    (anchorVertex (firstIntersectionAnchor B))
    (((mem_intersectionAnchors B.1 _).1 (firstIntersectionAnchor_mem B)).2.1)

theorem markedFamily_bad {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (M : MarkedFamily u v) : IsBadFamily M.family :=
  ⟨M.left, M.right, ne_of_lt M.ordered, markedLeftCut M, markedRightCut M, M.meet⟩

noncomputable def badSwap {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (B : BadFamily u v) : BadFamily u v :=
  ⟨(markedSwap (canonicalMark B)).family, markedFamily_bad (markedSwap (canonicalMark B))⟩

theorem firstIntersectionAnchor_mem_after {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (B : BadFamily u v) : firstIntersectionAnchor B ∈ intersectionAnchors (badSwap B).1 := by
  have ha := (mem_intersectionAnchors B.1 _).1 (firstIntersectionAnchor_mem B)
  apply (mem_intersectionAnchors (badSwap B).1 _).2
  refine ⟨ha.1, ?_, ?_⟩
  · exact (markedSwap_labelled_prefix (canonicalMark B) (firstIntersectionAnchor B).2.1
      (anchorVertex (firstIntersectionAnchor B)) (by
        simpa only [canonicalMark_point] using (le_refl (gridGrade (anchorVertex (firstIntersectionAnchor B)))))).2 ha.2.1
  · exact (markedSwap_labelled_prefix (canonicalMark B) (firstIntersectionAnchor B).2.2
      (anchorVertex (firstIntersectionAnchor B)) (by
        simpa only [canonicalMark_point] using (le_refl (gridGrade (anchorVertex (firstIntersectionAnchor B)))))).2 ha.2.2

theorem intersectionAnchor_after_swap_iff {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (B : BadFamily u v) (a : IntersectionAnchor N k)
    (hg : anchorGrade a ≤ anchorGrade (firstIntersectionAnchor B)) :
    a ∈ intersectionAnchors (badSwap B).1 ↔ a ∈ intersectionAnchors B.1 := by
  have hp : gridGrade (anchorVertex a) ≤ gridGrade (markedPoint (canonicalMark B)) := by
    rw [canonicalMark_point]
    have ha := anchorGrade_eq_gamma a
    have hb := anchorGrade_eq_gamma (firstIntersectionAnchor B)
    omega
  rw [mem_intersectionAnchors, mem_intersectionAnchors]
  constructor
  · rintro ⟨hij, hi, hj⟩
    exact ⟨hij, (markedSwap_labelled_prefix (canonicalMark B) a.2.1 (anchorVertex a) hp).1 hi,
      (markedSwap_labelled_prefix (canonicalMark B) a.2.2 (anchorVertex a) hp).1 hj⟩
  · rintro ⟨hij, hi, hj⟩
    exact ⟨hij, (markedSwap_labelled_prefix (canonicalMark B) a.2.1 (anchorVertex a) hp).2 hi,
      (markedSwap_labelled_prefix (canonicalMark B) a.2.2 (anchorVertex a) hp).2 hj⟩

theorem firstIntersectionKey_after_le {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (B : BadFamily u v) : firstIntersectionKey (badSwap B) ≤ firstIntersectionKey B := by
  classical
  have hm : firstIntersectionKey B ∈ intersectionKeys (badSwap B).1 := by
    rw [← firstIntersectionAnchor_key B]
    exact Finset.mem_image_of_mem anchorKey (firstIntersectionAnchor_mem_after B)
  exact Finset.min'_le _ _ hm

theorem firstIntersectionKey_after_swap {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (B : BadFamily u v) : firstIntersectionKey (badSwap B) = firstIntersectionKey B := by
  classical
  have hle := firstIntersectionKey_after_le B
  have hk : anchorKey (firstIntersectionAnchor (badSwap B)) ≤ anchorKey (firstIntersectionAnchor B) := by
    simpa only [firstIntersectionAnchor_key] using hle
  have hg := Prod.Lex.monotone_fst _ _ hk
  change anchorGrade (firstIntersectionAnchor (badSwap B)) ≤ anchorGrade (firstIntersectionAnchor B) at hg
  have hm : firstIntersectionAnchor (badSwap B) ∈ intersectionAnchors B.1 :=
    (intersectionAnchor_after_swap_iff B _ hg).1 (firstIntersectionAnchor_mem (badSwap B))
  have hkey : firstIntersectionKey (badSwap B) ∈ intersectionKeys B.1 := by
    rw [← firstIntersectionAnchor_key (badSwap B)]
    exact Finset.mem_image_of_mem anchorKey hm
  exact le_antisymm hle (Finset.min'_le _ _ hkey)

theorem firstIntersectionAnchor_after_swap {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (B : BadFamily u v) : firstIntersectionAnchor (badSwap B) = firstIntersectionAnchor B := by
  apply anchorKey_injective
  rw [firstIntersectionAnchor_key, firstIntersectionAnchor_key, firstIntersectionKey_after_swap]

theorem canonicalMark_after_swap {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (B : BadFamily u v) : canonicalMark (badSwap B) = markedSwap (canonicalMark B) := by
  apply markedFamily_ext
  · rfl
  · change (firstIntersectionAnchor (badSwap B)).2.1 = (firstIntersectionAnchor B).2.1
    exact congrArg (fun a : IntersectionAnchor N k => a.2.1) (firstIntersectionAnchor_after_swap B)
  · change (firstIntersectionAnchor (badSwap B)).2.2 = (firstIntersectionAnchor B).2.2
    exact congrArg (fun a : IntersectionAnchor N k => a.2.2) (firstIntersectionAnchor_after_swap B)
  · change rankVisitTime (u (firstIntersectionAnchor (badSwap B)).2.1).val
        (anchorVertex (firstIntersectionAnchor (badSwap B))) =
      rankVisitTime (u (firstIntersectionAnchor B).2.1).val (anchorVertex (firstIntersectionAnchor B))
    rw [firstIntersectionAnchor_after_swap]
  · change rankVisitTime (u (firstIntersectionAnchor (badSwap B)).2.2).val
        (anchorVertex (firstIntersectionAnchor (badSwap B))) =
      rankVisitTime (u (firstIntersectionAnchor B).2.2).val (anchorVertex (firstIntersectionAnchor B))
    rw [firstIntersectionAnchor_after_swap]

theorem badSwap_involutive {k N : ℕ} {u v : Fin k → Fin (N + 1)} :
    Function.Involutive (@badSwap k N u v) := by
  intro B
  apply Subtype.ext
  change (markedSwap (canonicalMark (badSwap B))).family = B.1
  rw [canonicalMark_after_swap]
  exact congrArg (fun M : MarkedFamily u v => M.family) (markedSwap_involutive (canonicalMark B))

theorem badSwap_sign {k N : ℕ} {u v : Fin k → Fin (N + 1)} (B : BadFamily u v) :
    signedFamilyWeight (badSwap B).1 = -signedFamilyWeight B.1 :=
  markedSwap_sign (canonicalMark B)

theorem badSwap_ne_self {k N : ℕ} {u v : Fin k → Fin (N + 1)} (B : BadFamily u v) :
    badSwap B ≠ B := by
  intro h
  have hm := congrArg (fun C : BadFamily u v => canonicalMark C) h
  change canonicalMark (badSwap B) = canonicalMark B at hm
  rw [canonicalMark_after_swap] at hm
  exact markedSwap_ne_self (canonicalMark B) hm

theorem badFamily_small_empty {k N : ℕ} (u v : Fin k → Fin (N + 1)) (hk : k ≤ 1) :
    IsEmpty (BadFamily u v) := by
  refine ⟨fun B => ?_⟩
  obtain ⟨i, j, hij, s, t, hst⟩ := B.2
  have hi := i.isLt
  have hj := j.isLt
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  omega

theorem badFamily_zero_empty {N : ℕ} (u v : Fin 0 → Fin (N + 1)) : IsEmpty (BadFamily u v) :=
  badFamily_small_empty u v (by omega)

theorem badFamily_one_empty {N : ℕ} (u v : Fin 1 → Fin (N + 1)) : IsEmpty (BadFamily u v) :=
  badFamily_small_empty u v (by omega)

end Hardinian
