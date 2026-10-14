import Hardinian.CutPathCore
import Mathlib.Data.Fintype.Powerset
import Mathlib.SetTheory.Cardinal.Finite

namespace Hardinian

def stepPrefixCount {L : ℕ} (S : Finset (Fin L)) (m : ℕ) : ℕ :=
  (S.filter (fun t => t.val < m)).card

theorem stepPrefixCount_zero {L : ℕ} (S : Finset (Fin L)) : stepPrefixCount S 0 = 0 := by
  simp [stepPrefixCount]

theorem stepPrefixCount_all {L : ℕ} (S : Finset (Fin L)) : stepPrefixCount S L = S.card := by
  unfold stepPrefixCount
  congr 1
  exact Finset.filter_eq_self.mpr (fun t _ => t.isLt)

theorem stepPrefixCount_le_card {L : ℕ} (S : Finset (Fin L)) (m : ℕ) :
    stepPrefixCount S m ≤ S.card := Finset.card_filter_le _ _

theorem stepPrefix_filter_succ_mem {L : ℕ} (S : Finset (Fin L)) (t : Fin L) (ht : t ∈ S) :
    S.filter (fun i => i.val < t.val + 1) = insert t (S.filter (fun i => i.val < t.val)) := by
  apply Finset.ext
  intro i
  simp only [Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨hi, hlt⟩
    by_cases he : i = t
    · exact Or.inl he
    · have hn : i.val ≠ t.val := fun h => he (Fin.ext h)
      exact Or.inr ⟨hi, by omega⟩
  · rintro (rfl | ⟨hi, hlt⟩)
    · exact ⟨ht, by omega⟩
    · exact ⟨hi, by omega⟩

theorem stepPrefix_filter_succ_not_mem {L : ℕ} (S : Finset (Fin L)) (t : Fin L) (ht : t ∉ S) :
    S.filter (fun i => i.val < t.val + 1) = S.filter (fun i => i.val < t.val) := by
  apply Finset.ext
  intro i
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hi, hlt⟩
    refine ⟨hi, ?_⟩
    by_contra hn
    have he : i = t := Fin.ext (by omega)
    exact ht (by simpa only [he] using hi)
  · rintro ⟨hi, hlt⟩
    exact ⟨hi, by omega⟩

theorem stepPrefixCount_succ {L : ℕ} (S : Finset (Fin L)) (t : Fin L) :
    stepPrefixCount S (t.val + 1) = stepPrefixCount S t.val + if t ∈ S then 1 else 0 := by
  by_cases ht : t ∈ S
  · rw [if_pos ht]
    unfold stepPrefixCount
    rw [stepPrefix_filter_succ_mem S t ht, Finset.card_insert_of_not_mem]
    simp only [Finset.mem_filter, lt_self_iff_false, and_false, not_false_eq_true]
  · rw [if_neg ht, Nat.add_zero]
    unfold stepPrefixCount
    rw [stepPrefix_filter_succ_not_mem S t ht]
    simp only [Nat.add_zero]

theorem stepPrefixCount_le_index {L : ℕ} (S : Finset (Fin L)) (m : ℕ) (hm : m ≤ L) :
    stepPrefixCount S m ≤ m := by
  revert hm
  induction m with
  | zero => intro hm; simp only [stepPrefixCount_zero, le_refl]
  | succ m ih =>
    intro hm
    let t : Fin L := ⟨m, by omega⟩
    have hp := stepPrefixCount_succ S t
    change stepPrefixCount S (m + 1) = stepPrefixCount S m + if t ∈ S then 1 else 0 at hp
    have hi := ih (by omega)
    split_ifs at hp <;> omega

def gridPathUpSteps {u v : ℕ} (P : GridPath u v) : Finset (Fin (u + v)) :=
  Finset.univ.filter (fun t => (P.1 t.succ).1 + 1 = (P.1 t.castSucc).1)

theorem gridPath_up_prefix {u v : ℕ} (P : GridPath u v) (t : Fin (u + v + 1)) :
    stepPrefixCount (gridPathUpSteps P) t.val + (P.1 t).1 = u := by
  induction t using Fin.induction with
  | zero => simp only [Fin.val_zero, stepPrefixCount_zero, P.2.1, Nat.zero_add]
  | succ t ih =>
    change stepPrefixCount (gridPathUpSteps P) t.val + (P.1 t.castSucc).1 = u at ih
    change stepPrefixCount (gridPathUpSteps P) (t.val + 1) + (P.1 t.succ).1 = u
    have hp := stepPrefixCount_succ (gridPathUpSteps P) t
    rcases P.2.2.2 t with he | hu
    · have hn : t ∉ gridPathUpSteps P := by
        simp only [gridPathUpSteps, Finset.mem_filter, Finset.mem_univ, true_and]
        intro h
        omega
      rw [if_neg hn] at hp
      omega
    · have hm : t ∈ gridPathUpSteps P := by
        simp only [gridPathUpSteps, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hu.1
      rw [if_pos hm] at hp
      omega

theorem gridPath_up_prefix_col {u v : ℕ} (P : GridPath u v) (t : Fin (u + v + 1)) :
    stepPrefixCount (gridPathUpSteps P) t.val + (P.1 t).2 = t.val := by
  have hu := gridPath_up_prefix P t
  have hr := gridPath_rank P t
  omega

theorem gridPathUpSteps_card {u v : ℕ} (P : GridPath u v) : (gridPathUpSteps P).card = u := by
  have h := gridPath_up_prefix P (Fin.last (u + v))
  simpa only [Fin.val_last, stepPrefixCount_all, P.2.2.1, Nat.add_zero] using h

def UpStepSet (u v : ℕ) := {S : Finset (Fin (u + v)) // S.card = u}

def gridPathUpStepSet {u v : ℕ} (P : GridPath u v) : UpStepSet u v :=
  ⟨gridPathUpSteps P, gridPathUpSteps_card P⟩

def stepSetVertices {u v : ℕ} (S : UpStepSet u v) (t : Fin (u + v + 1)) : ℕ × ℕ :=
  (u - stepPrefixCount S.1 t.val, t.val - stepPrefixCount S.1 t.val)

theorem stepSetVertices_isPath {u v : ℕ} (S : UpStepSet u v) :
    IsGridPath u v (stepSetVertices S) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [stepSetVertices, stepPrefixCount_zero]
  · simp [stepSetVertices, stepPrefixCount_all, S.2]
  · intro t
    have ha := stepPrefixCount_le_card S.1 t.val
    have hb := stepPrefixCount_le_card S.1 (t.val + 1)
    rw [S.2] at ha hb
    have hc := stepPrefixCount_le_index S.1 t.val (Nat.le_of_lt t.isLt)
    have hs := stepPrefixCount_succ S.1 t
    change GridStep
      (u - stepPrefixCount S.1 t.val, t.val - stepPrefixCount S.1 t.val)
      (u - stepPrefixCount S.1 (t.val + 1), t.val + 1 - stepPrefixCount S.1 (t.val + 1))
    dsimp only [GridStep]
    by_cases hm : t ∈ S.1
    · rw [if_pos hm] at hs
      right
      constructor <;> omega
    · rw [if_neg hm] at hs
      left
      constructor <;> omega

def stepSetPath {u v : ℕ} (S : UpStepSet u v) : GridPath u v :=
  ⟨stepSetVertices S, stepSetVertices_isPath S⟩

theorem stepSetPath_upSteps {u v : ℕ} (P : GridPath u v) :
    stepSetPath (gridPathUpStepSet P) = P := by
  apply Subtype.ext
  funext t
  have hr := gridPath_up_prefix P t
  have hc := gridPath_up_prefix_col P t
  apply Prod.ext
  · change u - stepPrefixCount (gridPathUpSteps P) t.val = (P.1 t).1
    omega
  · change t.val - stepPrefixCount (gridPathUpSteps P) t.val = (P.1 t).2
    omega

theorem upSteps_stepSetPath {u v : ℕ} (S : UpStepSet u v) :
    gridPathUpStepSet (stepSetPath S) = S := by
  apply Subtype.ext
  apply Finset.ext
  intro t
  simp only [gridPathUpStepSet, gridPathUpSteps, Finset.mem_filter, Finset.mem_univ, true_and]
  change u - stepPrefixCount S.1 (t.val + 1) + 1 = u - stepPrefixCount S.1 t.val ↔ t ∈ S.1
  have hb := stepPrefixCount_le_card S.1 (t.val + 1)
  rw [S.2] at hb
  have hs := stepPrefixCount_succ S.1 t
  by_cases hm : t ∈ S.1
  · rw [if_pos hm] at hs
    constructor
    · intro h; exact hm
    · intro h; omega
  · rw [if_neg hm] at hs
    constructor
    · intro h
      exfalso
      omega
    · intro h
      exact (hm h).elim

def gridPathStepPositionsEquiv (u v : ℕ) : GridPath u v ≃ UpStepSet u v where
  toFun := gridPathUpStepSet
  invFun := stepSetPath
  left_inv := stepSetPath_upSteps
  right_inv := upSteps_stepSetPath

theorem gridPath_finite (u v : ℕ) : Finite (GridPath u v) := by
  letI : Finite (UpStepSet u v) := by
    unfold UpStepSet
    infer_instance
  exact Finite.of_injective (gridPathStepPositionsEquiv u v) (gridPathStepPositionsEquiv u v).injective

theorem gridPath_card (u v : ℕ) : Nat.card (GridPath u v) = Nat.choose (u + v) u := by
  calc
    Nat.card (GridPath u v) = Nat.card (UpStepSet u v) := Nat.card_congr (gridPathStepPositionsEquiv u v)
    _ = Nat.choose (u + v) u := by
      unfold UpStepSet
      rw [Nat.card_eq_fintype_card, Fintype.card_finset_len, Fintype.card_fin]

theorem gridPath_card_symmetric (u v : ℕ) : Nat.card (GridPath u v) = Nat.choose (u + v) v := by
  rw [gridPath_card, Nat.choose_symm_add]

theorem gridPath_card_zero_left (v : ℕ) : Nat.card (GridPath 0 v) = 1 := by
  simp [gridPath_card]

theorem gridPath_card_zero_right (u : ℕ) : Nat.card (GridPath u 0) = 1 := by
  simp [gridPath_card]

end Hardinian
