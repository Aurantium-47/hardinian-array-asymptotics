import Hardinian.GeneralArrayEncoding
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod

namespace Hardinian.AllParameters

def IsSeparatedCuts (r k : ℕ) (C : Fin k → Finset (Fin (k + r + 1) × Fin (k + r + 1))) : Prop :=
  (∀ t : Fin k, ∀ p q : Fin (k + r + 1) × Fin (k + r + 1),
    q.1 ≤ p.1 → q.2 ≤ p.2 → p ∈ C t → q ∈ C t) ∧
  Monotone C ∧
  (∀ t, ((0, 0) : Fin (k + r + 1) × Fin (k + r + 1)) ∈ C t ∧
    ∀ i, (Fin.last (k + r), i) ∉ C t ∧ (i, Fin.last (k + r)) ∉ C t) ∧
  ∀ t s : Fin k, s.val = t.val + 1 → ∀ i j : Fin (k + r),
    (i.castSucc, j.castSucc) ∈ C t → (i.succ, j.succ) ∈ C s

def SeparatedCuts (r k : ℕ) : Type :=
  {C : Fin k → Finset (Fin (k + r + 1) × Fin (k + r + 1)) // IsSeparatedCuts r k C}

def encodeCuts (r k : ℕ) (A : Fin (k + r + 1) → Fin (k + r + 1) → ℕ) (t : Fin k) :
    Finset (Fin (k + r + 1) × Fin (k + r + 1)) :=
  Finset.univ.filter (fun p => A p.1 p.2 ≤ t.val)

def decodeCuts (r k : ℕ) (C : Fin k → Finset (Fin (k + r + 1) × Fin (k + r + 1)))
    (i j : Fin (k + r + 1)) : ℕ :=
  (Finset.univ.filter (fun t : Fin k => (i, j) ∉ C t)).card

theorem encodeCuts_monotone (r k : ℕ) (A : Fin (k + r + 1) → Fin (k + r + 1) → ℕ) :
    Monotone (encodeCuts r k A) := by
  intro t s hts p hp
  simp only [encodeCuts, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  exact hp.trans hts

theorem decodeCuts_le (r k : ℕ) (C : Fin k → Finset (Fin (k + r + 1) × Fin (k + r + 1)))
    (i j : Fin (k + r + 1)) : decodeCuts r k C i j ≤ k := by
  simpa only [decodeCuts, Finset.card_univ, Fintype.card_fin] using
    (Finset.card_filter_le (Finset.univ : Finset (Fin k)) (fun t => (i, j) ∉ C t))

theorem decodeCuts_le_iff_mem (r k : ℕ) (C : Fin k → Finset (Fin (k + r + 1) × Fin (k + r + 1)))
    (hn : Monotone C) (i j : Fin (k + r + 1)) (t : Fin k) :
    decodeCuts r k C i j ≤ t.val ↔ (i, j) ∈ C t := by
  constructor
  · intro hle
    by_contra hmem
    have hsub : Finset.Iic t ⊆ Finset.univ.filter (fun s : Fin k => (i, j) ∉ C s) := by
      intro s hs
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      intro hCs
      exact hmem (hn (Finset.mem_Iic.mp hs) hCs)
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hc
    change t.val + 1 ≤ decodeCuts r k C i j at hc
    omega
  · intro hmem
    have hsub : Finset.univ.filter (fun s : Fin k => (i, j) ∉ C s) ⊆ Finset.Iio t := by
      intro s hs
      have hnot := (Finset.mem_filter.mp hs).2
      apply Finset.mem_Iio.mpr
      by_contra hlt
      exact hnot (hn (le_of_not_gt hlt) hmem)
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hc
    exact hc

theorem encodeCuts_valid (r k : ℕ) (A : Fin (k + r + 1) → Fin (k + r + 1) → ℕ)
    (hA : IsSquareArray r k A) : IsSeparatedCuts r k (encodeCuts r k A) := by
  have hm := array_steps_monotone r k A hA.2.2.1
  have hb := (isSquareArray_iff_boundary r k A).mp hA
  refine ⟨?_, encodeCuts_monotone r k A, ?_, ?_⟩
  · intro t p q h1 h2 hp
    simp only [encodeCuts, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact (hm q.1 p.1 q.2 p.2 h1 h2).trans hp
  · intro t
    constructor
    · simp only [encodeCuts, Finset.mem_filter, Finset.mem_univ, true_and, hA.1]
      exact Nat.zero_le _
    · intro i
      constructor
      · simp only [encodeCuts, Finset.mem_filter, Finset.mem_univ, true_and, (hb.2.2.1 i).1]
        exact Nat.not_le_of_lt t.isLt
      · simp only [encodeCuts, Finset.mem_filter, Finset.mem_univ, true_and, (hb.2.2.1 i).2]
        exact Nat.not_le_of_lt t.isLt
  · intro t s hst i j hp
    simp only [encodeCuts, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    have hd := (hA.2.2.1.2.2 i j).2
    omega

theorem decodeCuts_monotone (r k : ℕ) (C : Fin k → Finset (Fin (k + r + 1) × Fin (k + r + 1)))
    (hC : IsSeparatedCuts r k C) : ArrayMonotone r k (decodeCuts r k C) := by
  intro i i' j j' hi hj
  apply Finset.card_le_card
  intro t ht
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  intro hnew
  exact (Finset.mem_filter.mp ht).2 (hC.1 t (i', j') (i, j) hi hj hnew)

theorem decodeCuts_origin (r k : ℕ) (C : Fin k → Finset (Fin (k + r + 1) × Fin (k + r + 1)))
    (hC : IsSeparatedCuts r k C) : decodeCuts r k C 0 0 = 0 := by
  apply Finset.card_filter_eq_zero_iff.mpr
  intro t ht hnot
  exact hnot (hC.2.2.1 t).1

theorem decodeCuts_edges (r k : ℕ) (C : Fin k → Finset (Fin (k + r + 1) × Fin (k + r + 1)))
    (hC : IsSeparatedCuts r k C) (i : Fin (k + r + 1)) :
    decodeCuts r k C (Fin.last (k + r)) i = k ∧ decodeCuts r k C i (Fin.last (k + r)) = k := by
  constructor
  · calc
      decodeCuts r k C (Fin.last (k + r)) i = (Finset.univ : Finset (Fin k)).card :=
        Finset.card_filter_eq_iff.mpr (fun t _ => ((hC.2.2.1 t).2 i).1)
      _ = k := by simp
  · calc
      decodeCuts r k C i (Fin.last (k + r)) = (Finset.univ : Finset (Fin k)).card :=
        Finset.card_filter_eq_iff.mpr (fun t _ => ((hC.2.2.1 t).2 i).2)
      _ = k := by simp

theorem decodeCuts_diagonal (r k : ℕ) (C : Fin k → Finset (Fin (k + r + 1) × Fin (k + r + 1)))
    (hC : IsSeparatedCuts r k C) (i j : Fin (k + r)) :
    decodeCuts r k C i.succ j.succ ≤ decodeCuts r k C i.castSucc j.castSucc + 1 := by
  by_contra hbad
  have hhigh := decodeCuts_le r k C i.succ j.succ
  let t : Fin k := ⟨decodeCuts r k C i.castSucc j.castSucc, by omega⟩
  let s : Fin k := ⟨decodeCuts r k C i.castSucc j.castSucc + 1, by omega⟩
  have hp : (i.castSucc, j.castSucc) ∈ C t :=
    (decodeCuts_le_iff_mem r k C hC.2.1 _ _ t).mp (le_refl _)
  have hq := hC.2.2.2 t s rfl i j hp
  have hle := (decodeCuts_le_iff_mem r k C hC.2.1 _ _ s).mpr hq
  change decodeCuts r k C i.succ j.succ ≤ decodeCuts r k C i.castSucc j.castSucc + 1 at hle
  exact hbad hle

theorem decodeCuts_valid (r k : ℕ) (C : Fin k → Finset (Fin (k + r + 1) × Fin (k + r + 1)))
    (hC : IsSeparatedCuts r k C) : IsSquareArray r k (decodeCuts r k C) := by
  apply (isSquareArray_iff_boundary r k (decodeCuts r k C)).mpr
  exact ⟨decodeCuts_origin r k C hC, decodeCuts_monotone r k C hC,
    decodeCuts_edges r k C hC, decodeCuts_diagonal r k C hC⟩

theorem decode_encodeCuts (r k : ℕ) (A : Fin (k + r + 1) → Fin (k + r + 1) → ℕ)
    (hA : ∀ i j, A i j ≤ k) : decodeCuts r k (encodeCuts r k A) = A := by
  funext i j
  apply le_antisymm
  · by_cases ha : A i j < k
    · let t : Fin k := ⟨A i j, ha⟩
      apply (decodeCuts_le_iff_mem r k (encodeCuts r k A) (encodeCuts_monotone r k A) i j t).mpr
      simp only [encodeCuts, Finset.mem_filter, Finset.mem_univ, true_and]
      exact le_refl _
    · exact (decodeCuts_le r k (encodeCuts r k A) i j).trans (Nat.le_of_not_gt ha)
  · by_cases hd : decodeCuts r k (encodeCuts r k A) i j < k
    · let t : Fin k := ⟨decodeCuts r k (encodeCuts r k A) i j, hd⟩
      have hm := (decodeCuts_le_iff_mem r k (encodeCuts r k A) (encodeCuts_monotone r k A) i j t).mp (le_refl _)
      simpa only [encodeCuts, Finset.mem_filter, Finset.mem_univ, true_and] using hm
    · exact (hA i j).trans (Nat.le_of_not_gt hd)

theorem encode_decodeCuts (r k : ℕ) (C : Fin k → Finset (Fin (k + r + 1) × Fin (k + r + 1)))
    (hn : Monotone C) : encodeCuts r k (decodeCuts r k C) = C := by
  funext t
  apply Finset.ext
  intro p
  simp only [encodeCuts, Finset.mem_filter, Finset.mem_univ, true_and]
  exact decodeCuts_le_iff_mem r k C hn p.1 p.2 t

def arrayCutsEquiv (r k : ℕ) : SquareArray r k ≃ SeparatedCuts r k where
  toFun A := ⟨encodeCuts r k A.1, encodeCuts_valid r k A.1 A.2⟩
  invFun C := ⟨decodeCuts r k C.1, decodeCuts_valid r k C.1 C.2⟩
  left_inv A := by
    apply Subtype.ext
    exact decode_encodeCuts r k A.1 (squareArray_value_le_endpoint r k A.1 A.2)
  right_inv C := by
    apply Subtype.ext
    exact encode_decodeCuts r k C.1 C.2.2.1

theorem separatedCuts_finite (r k : ℕ) : Finite (SeparatedCuts r k) := by
  unfold SeparatedCuts
  infer_instance

theorem squareArray_card_eq_separatedCuts (r k : ℕ) :
    Nat.card (SquareArray r k) = Nat.card (SeparatedCuts r k) := Nat.card_congr (arrayCutsEquiv r k)

def emptyCuts (r : ℕ) : SeparatedCuts r 0 := by
  refine ⟨fun t => Fin.elim0 t, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t; exact Fin.elim0 t
  · intro t; exact Fin.elim0 t
  · intro t; exact Fin.elim0 t
  · intro t; exact Fin.elim0 t

theorem separatedCuts_zero_levels_eq (r : ℕ) (C : SeparatedCuts r 0) :
    C = emptyCuts r := by
  apply Subtype.ext
  funext t
  exact Fin.elim0 t

theorem separatedCuts_zero_card (r : ℕ) : Nat.card (SeparatedCuts r 0) = 1 :=
  Nat.card_eq_one_iff_exists.mpr ⟨emptyCuts r, separatedCuts_zero_levels_eq r⟩

theorem arrayCutsEquiv_left_inverse (r k : ℕ) (A : SquareArray r k) :
    (arrayCutsEquiv r k).symm (arrayCutsEquiv r k A) = A :=
  (arrayCutsEquiv r k).symm_apply_apply A

theorem arrayCutsEquiv_right_inverse (r k : ℕ) (C : SeparatedCuts r k) :
    arrayCutsEquiv r k ((arrayCutsEquiv r k).symm C) = C :=
  (arrayCutsEquiv r k).apply_symm_apply C

theorem arrayCutsEquiv_zero_levels (r : ℕ) :
    arrayCutsEquiv r 0 (zeroLevelArray r) = emptyCuts r :=
  separatedCuts_zero_levels_eq r _

theorem arrayCutsEquiv_symm_empty (r : ℕ) :
    (arrayCutsEquiv r 0).symm (emptyCuts r) = zeroLevelArray r :=
  squareArray_zero_levels_eq r _

theorem separatedCuts_zero_dimension_card : Nat.card (SeparatedCuts 0 0) = 1 :=
  separatedCuts_zero_card 0

end Hardinian.AllParameters
