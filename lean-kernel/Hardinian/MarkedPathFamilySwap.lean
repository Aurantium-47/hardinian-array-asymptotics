import Hardinian.GridPathSplice
import Hardinian.SignedPathFamilyExpansion

namespace Hardinian

def pathVertex {u v : ℕ} (P : GridPath u v) (t : ℕ) : Option (ℕ × ℕ) :=
  if h : t < u + v + 1 then some (P.1 ⟨t, h⟩) else none

theorem pathVertex_of_lt {u v : ℕ} (P : GridPath u v) (t : ℕ) (h : t < u + v + 1) :
    pathVertex P t = some (P.1 ⟨t, h⟩) := by
  simp only [pathVertex, dif_pos h]

theorem pathVertex_splice {u v u' v' : ℕ} (P : GridPath u v) (Q : GridPath u' v')
    (a : Fin (u + v + 1)) (b : Fin (u' + v' + 1)) (h : P.1 a = Q.1 b) (t : ℕ) :
    pathVertex (gridPathSplice P Q a b h) t =
      if t ≤ a.val then pathVertex P t else pathVertex Q (b.val + (t - a.val)) := by
  by_cases hp : t ≤ a.val
  · have ho : t < u + v + 1 := by have ha := a.isLt; omega
    have hn : t < u + v' + 1 := by have ha := splice_cut_bound P Q a b h; omega
    rw [if_pos hp, pathVertex_of_lt _ _ hn, pathVertex_of_lt _ _ ho]
    exact congrArg some (spliceVertex_prefix P Q a b h ⟨t, hn⟩ hp)
  · rw [if_neg hp]
    by_cases hn : t < u + v' + 1
    · have hq := splice_tail_bound P Q a b h ⟨t, hn⟩ hp
      rw [pathVertex_of_lt _ _ hn, pathVertex_of_lt _ _ hq]
      exact congrArg some (spliceVertex_tail P Q a b h ⟨t, hn⟩ hp)
    · have hq : ¬ b.val + (t - a.val) < u' + v' + 1 := by
        have hr := splice_rank P Q a b h
        omega
      simp only [pathVertex, dif_neg hn, dif_neg hq]

def familyVertex {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (F : SignedFamily u v) (i : Fin k) (t : ℕ) : Option (ℕ × ℕ) := pathVertex (F.2 i) t

def familyVisits {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (F : SignedFamily u v) (i : Fin k) (p : ℕ × ℕ) : Prop := ∃ t, (F.2 i).1 t = p

theorem familyVisits_iff_vertex {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (F : SignedFamily u v) (i : Fin k) (p : ℕ × ℕ) :
    familyVisits F i p ↔ ∃ t : ℕ, familyVertex F i t = some p := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t.val, ?_⟩
    exact (pathVertex_of_lt (F.2 i) t.val t.isLt).trans (congrArg some ht)
  · rintro ⟨t, ht⟩
    unfold familyVertex pathVertex at ht
    split_ifs at ht with h
    · exact ⟨⟨t, h⟩, Option.some.inj ht⟩
    · cases ht

theorem signedFamily_vertex_ext {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (F G : SignedFamily u v) (hσ : F.1 = G.1)
    (hv : ∀ i t, familyVertex F i t = familyVertex G i t) : F = G := by
  rcases F with ⟨σ, P⟩
  rcases G with ⟨τ, Q⟩
  dsimp only at hσ
  subst τ
  apply congrArg (fun R : PathTuple u v σ => (⟨σ, R⟩ : SignedFamily u v))
  funext i
  apply Subtype.ext
  funext t
  have h := hv i t.val
  simpa only [familyVertex, pathVertex, dif_pos t.isLt, Option.some.injEq] using h

structure MarkedFamily {k N : ℕ} (u v : Fin k → Fin (N + 1)) where
  family : SignedFamily u v
  left : Fin k
  right : Fin k
  ordered : left < right
  leftTime : ℕ
  rightTime : ℕ
  leftLegal : leftTime < (u left).val + (v (family.1 left)).val + 1
  rightLegal : rightTime < (u right).val + (v (family.1 right)).val + 1
  meet : (family.2 left).1 ⟨leftTime, leftLegal⟩ =
    (family.2 right).1 ⟨rightTime, rightLegal⟩

def markedLeftCut {k N : ℕ} {u v : Fin k → Fin (N + 1)} (M : MarkedFamily u v) :
    Fin ((u M.left).val + (v (M.family.1 M.left)).val + 1) := ⟨M.leftTime, M.leftLegal⟩

def markedRightCut {k N : ℕ} {u v : Fin k → Fin (N + 1)} (M : MarkedFamily u v) :
    Fin ((u M.right).val + (v (M.family.1 M.right)).val + 1) := ⟨M.rightTime, M.rightLegal⟩

def markedPoint {k N : ℕ} {u v : Fin k → Fin (N + 1)} (M : MarkedFamily u v) : ℕ × ℕ :=
  (M.family.2 M.left).1 (markedLeftCut M)

theorem markedFamily_ext {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (M L : MarkedFamily u v) (hf : M.family = L.family)
    (hi : M.left = L.left) (hj : M.right = L.right)
    (ha : M.leftTime = L.leftTime) (hb : M.rightTime = L.rightTime) : M = L := by
  cases M
  cases L
  cases hf
  cases hi
  cases hj
  cases ha
  cases hb
  rfl

def markedSwapTuple {k N : ℕ} {u v : Fin k → Fin (N + 1)} (M : MarkedFamily u v) :
    PathTuple u v (M.family.1 * Equiv.swap M.left M.right) := by
  intro i
  by_cases hi : i = M.left
  · subst i
    simpa only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] using
      gridPathSplice (M.family.2 M.left) (M.family.2 M.right)
        (markedLeftCut M) (markedRightCut M) M.meet
  · by_cases hj : i = M.right
    · subst i
      simpa only [Equiv.Perm.mul_apply, Equiv.swap_apply_right] using
        gridPathSplice (M.family.2 M.right) (M.family.2 M.left)
          (markedRightCut M) (markedLeftCut M) M.meet.symm
    · simpa only [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hi hj] using M.family.2 i

def markedSwapFamily {k N : ℕ} {u v : Fin k → Fin (N + 1)} (M : MarkedFamily u v) :
    SignedFamily u v := ⟨M.family.1 * Equiv.swap M.left M.right, markedSwapTuple M⟩

theorem markedSwapFamily_perm {k N : ℕ} {u v : Fin k → Fin (N + 1)} (M : MarkedFamily u v) :
    (markedSwapFamily M).1 = M.family.1 * Equiv.swap M.left M.right := rfl

theorem markedSwapFamily_vertex {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (M : MarkedFamily u v) (i : Fin k) (t : ℕ) :
    familyVertex (markedSwapFamily M) i t =
      if i = M.left then
        if t ≤ M.leftTime then familyVertex M.family M.left t
        else familyVertex M.family M.right (M.rightTime + (t - M.leftTime))
      else if i = M.right then
        if t ≤ M.rightTime then familyVertex M.family M.right t
        else familyVertex M.family M.left (M.leftTime + (t - M.rightTime))
      else familyVertex M.family i t := by
  by_cases hi : i = M.left
  · subst i
    simpa [markedSwapFamily, markedSwapTuple, familyVertex, Equiv.Perm.mul_apply,
      markedLeftCut, markedRightCut] using
      pathVertex_splice (M.family.2 M.left) (M.family.2 M.right)
        (markedLeftCut M) (markedRightCut M) M.meet t
  · by_cases hj : i = M.right
    · subst i
      simpa [markedSwapFamily, markedSwapTuple, familyVertex, Equiv.Perm.mul_apply,
        markedLeftCut, markedRightCut, hi] using
        pathVertex_splice (M.family.2 M.right) (M.family.2 M.left)
          (markedRightCut M) (markedLeftCut M) M.meet.symm t
    · simp [markedSwapFamily, markedSwapTuple, familyVertex, Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne hi hj, hi, hj]

theorem markedSwapFamily_cut_left {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (M : MarkedFamily u v) :
    familyVertex (markedSwapFamily M) M.left M.leftTime = some (markedPoint M) := by
  rw [markedSwapFamily_vertex]
  simp only [if_pos rfl, if_pos (le_refl M.leftTime)]
  exact pathVertex_of_lt (M.family.2 M.left) M.leftTime M.leftLegal

theorem markedSwapFamily_cut_right {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (M : MarkedFamily u v) :
    familyVertex (markedSwapFamily M) M.right M.rightTime = some (markedPoint M) := by
  rw [markedSwapFamily_vertex]
  simp only [if_neg (ne_of_lt M.ordered).symm, if_pos rfl, if_pos (le_refl M.rightTime)]
  exact (pathVertex_of_lt (M.family.2 M.right) M.rightTime M.rightLegal).trans
    (congrArg some M.meet.symm)

def markedSwap {k N : ℕ} {u v : Fin k → Fin (N + 1)} (M : MarkedFamily u v) :
    MarkedFamily u v := by
  have hl : M.leftTime < (u M.left).val + (v ((markedSwapFamily M).1 M.left)).val + 1 := by
    simpa only [markedSwapFamily, Equiv.Perm.mul_apply, Equiv.swap_apply_left] using
      splice_cut_bound (M.family.2 M.left) (M.family.2 M.right)
        (markedLeftCut M) (markedRightCut M) M.meet
  have hr : M.rightTime < (u M.right).val + (v ((markedSwapFamily M).1 M.right)).val + 1 := by
    simpa only [markedSwapFamily, Equiv.Perm.mul_apply, Equiv.swap_apply_right] using
      splice_cut_bound (M.family.2 M.right) (M.family.2 M.left)
        (markedRightCut M) (markedLeftCut M) M.meet.symm
  refine ⟨markedSwapFamily M, M.left, M.right, M.ordered, M.leftTime, M.rightTime, hl, hr, ?_⟩
  apply Option.some.inj
  have h := (markedSwapFamily_cut_left M).trans (markedSwapFamily_cut_right M).symm
  simpa only [familyVertex, pathVertex, dif_pos hl, dif_pos hr] using h

theorem markedSwap_family {k N : ℕ} {u v : Fin k → Fin (N + 1)} (M : MarkedFamily u v) :
    (markedSwap M).family = markedSwapFamily M := rfl

theorem markedSwap_left {k N : ℕ} {u v : Fin k → Fin (N + 1)} (M : MarkedFamily u v) :
    (markedSwap M).left = M.left := rfl

theorem markedSwap_right {k N : ℕ} {u v : Fin k → Fin (N + 1)} (M : MarkedFamily u v) :
    (markedSwap M).right = M.right := rfl

theorem markedSwap_leftTime {k N : ℕ} {u v : Fin k → Fin (N + 1)} (M : MarkedFamily u v) :
    (markedSwap M).leftTime = M.leftTime := rfl

theorem markedSwap_rightTime {k N : ℕ} {u v : Fin k → Fin (N + 1)} (M : MarkedFamily u v) :
    (markedSwap M).rightTime = M.rightTime := rfl

theorem markedSwap_vertex {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (M : MarkedFamily u v) (i : Fin k) (t : ℕ) :
    familyVertex (markedSwap M).family i t =
      if i = M.left then
        if t ≤ M.leftTime then familyVertex M.family M.left t
        else familyVertex M.family M.right (M.rightTime + (t - M.leftTime))
      else if i = M.right then
        if t ≤ M.rightTime then familyVertex M.family M.right t
        else familyVertex M.family M.left (M.leftTime + (t - M.rightTime))
      else familyVertex M.family i t := markedSwapFamily_vertex M i t

theorem markedSwap_point {k N : ℕ} {u v : Fin k → Fin (N + 1)} (M : MarkedFamily u v) :
    markedPoint (markedSwap M) = markedPoint M := by
  apply Option.some.inj
  have h := markedSwapFamily_cut_left M
  simpa only [familyVertex, pathVertex, dif_pos (markedSwap M).leftLegal] using h

theorem markedSwap_other_vertex {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (M : MarkedFamily u v) (i : Fin k) (hi : i ≠ M.left) (hj : i ≠ M.right) (t : ℕ) :
    familyVertex (markedSwap M).family i t = familyVertex M.family i t := by
  simp only [markedSwap_vertex, if_neg hi, if_neg hj]

theorem markedSwap_twice_vertex {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (M : MarkedFamily u v) (i : Fin k) (t : ℕ) :
    familyVertex (markedSwap (markedSwap M)).family i t = familyVertex M.family i t := by
  have hij : M.left ≠ M.right := ne_of_lt M.ordered
  simp only [markedSwap_vertex, markedSwap_left, markedSwap_right,
    markedSwap_leftTime, markedSwap_rightTime]
  by_cases hi : i = M.left
  · subst i
    by_cases ht : t ≤ M.leftTime
    · simp [ht, hij, hij.symm]
    · have hb : ¬ M.rightTime + (t - M.leftTime) ≤ M.rightTime := by omega
      have he : M.leftTime + (M.rightTime + (t - M.leftTime) - M.rightTime) = t := by omega
      simp [ht, hij, hij.symm, hb, he]
  · by_cases hj : i = M.right
    · subst i
      by_cases ht : t ≤ M.rightTime
      · simp [ht, hij, hij.symm]
      · have ha : ¬ M.leftTime + (t - M.rightTime) ≤ M.leftTime := by omega
        have he : M.rightTime + (M.leftTime + (t - M.rightTime) - M.leftTime) = t := by omega
        simp [ht, hij, hij.symm, ha, he]
    · simp [hi, hj]

theorem markedSwap_family_involutive {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (M : MarkedFamily u v) : (markedSwap (markedSwap M)).family = M.family := by
  apply signedFamily_vertex_ext
  · change (M.family.1 * Equiv.swap M.left M.right) * Equiv.swap M.left M.right = M.family.1
    exact Equiv.Perm.mul_swap_involutive M.left M.right M.family.1
  · exact markedSwap_twice_vertex M

theorem markedSwap_involutive {k N : ℕ} {u v : Fin k → Fin (N + 1)} :
    Function.Involutive (@markedSwap k N u v) := by
  intro M
  exact markedFamily_ext _ _ (markedSwap_family_involutive M) rfl rfl rfl rfl

def markedSwapEquiv {k N : ℕ} (u v : Fin k → Fin (N + 1)) : MarkedFamily u v ≃ MarkedFamily u v where
  toFun := markedSwap
  invFun := markedSwap
  left_inv := markedSwap_involutive
  right_inv := markedSwap_involutive

theorem markedSwap_sign {k N : ℕ} {u v : Fin k → Fin (N + 1)} (M : MarkedFamily u v) :
    signedFamilyWeight (markedSwap M).family = -signedFamilyWeight M.family := by
  change (Equiv.Perm.sign (M.family.1 * Equiv.swap M.left M.right) : ℤ) =
    -(Equiv.Perm.sign M.family.1 : ℤ)
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (ne_of_lt M.ordered)]
  simp

theorem markedSwap_ne_self {k N : ℕ} {u v : Fin k → Fin (N + 1)} (M : MarkedFamily u v) :
    markedSwap M ≠ M := by
  intro h
  have hp := congrArg (fun L : MarkedFamily u v => L.family.1) h
  change M.family.1 * Equiv.swap M.left M.right = M.family.1 at hp
  exact (ne_of_lt M.ordered) (Equiv.Perm.mul_swap_eq_iff.mp hp)

theorem markedSwap_prefix_forward {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (M : MarkedFamily u v) (i : Fin k) (p : ℕ × ℕ)
    (hp : gridGrade p ≤ gridGrade (markedPoint M)) :
    familyVisits (markedSwap M).family i p → familyVisits M.family i p := by
  rintro ⟨t, ht⟩
  have hv : familyVertex (markedSwap M).family i t.val = some p :=
    (pathVertex_of_lt ((markedSwap M).family.2 i) t.val t.isLt).trans (congrArg some ht)
  apply (familyVisits_iff_vertex M.family i p).2
  refine ⟨t.val, ?_⟩
  by_cases hi : i = M.left
  · subst i
    have hg := gridPath_grade ((markedSwap M).family.2 M.left) t
    have ha := gridPath_grade (M.family.2 M.left) (markedLeftCut M)
    rw [ht] at hg
    change gridGrade p ≤ gridGrade ((M.family.2 M.left).1 (markedLeftCut M)) at hp
    have hb : t.val ≤ M.leftTime := by dsimp only [markedLeftCut] at ha; omega
    rw [markedSwap_vertex] at hv
    simpa only [if_pos rfl, if_pos hb] using hv
  · by_cases hj : i = M.right
    · subst i
      have hg := gridPath_grade ((markedSwap M).family.2 M.right) t
      have ha := gridPath_grade (M.family.2 M.right) (markedRightCut M)
      rw [ht] at hg
      have hp' : gridGrade p ≤ gridGrade ((M.family.2 M.right).1 (markedRightCut M)) := by
        simpa only [markedPoint, markedLeftCut, markedRightCut, M.meet] using hp
      have hb : t.val ≤ M.rightTime := by dsimp only [markedRightCut] at ha; omega
      rw [markedSwap_vertex] at hv
      simpa only [if_neg hi, if_pos rfl, if_pos hb] using hv
    · rw [markedSwap_other_vertex M i hi hj] at hv
      exact hv

theorem markedSwap_labelled_prefix {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (M : MarkedFamily u v) (i : Fin k) (p : ℕ × ℕ)
    (hp : gridGrade p ≤ gridGrade (markedPoint M)) :
    familyVisits (markedSwap M).family i p ↔ familyVisits M.family i p := by
  constructor
  · exact markedSwap_prefix_forward M i p hp
  · intro h
    apply markedSwap_prefix_forward (markedSwap M) i p (by simpa only [markedSwap_point] using hp)
    simpa only [markedSwap_family_involutive] using h

theorem markedFamily_small_empty {k N : ℕ} (u v : Fin k → Fin (N + 1)) (hk : k ≤ 1) :
    IsEmpty (MarkedFamily u v) := by
  refine ⟨fun M => ?_⟩
  have hlt : M.left.val < M.right.val := M.ordered
  have hr := M.right.isLt
  omega

theorem markedFamily_zero_empty {N : ℕ} (u v : Fin 0 → Fin (N + 1)) :
    IsEmpty (MarkedFamily u v) := markedFamily_small_empty u v (by omega)

theorem markedFamily_one_empty {N : ℕ} (u v : Fin 1 → Fin (N + 1)) :
    IsEmpty (MarkedFamily u v) := markedFamily_small_empty u v (by omega)

end Hardinian
