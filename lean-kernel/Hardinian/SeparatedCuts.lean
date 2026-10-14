import Hardinian.ArrayEncoding
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod

namespace Hardinian

def IsSeparatedCuts (k : ℕ) (C : Fin k → Finset (Fin (k + 3) × Fin (k + 3))) : Prop :=
  (∀ t : Fin k, ∀ p q : Fin (k + 3) × Fin (k + 3),
    q.1 ≤ p.1 → q.2 ≤ p.2 → p ∈ C t → q ∈ C t) ∧
  Monotone C ∧
  (∀ t, ((0, 0) : Fin (k + 3) × Fin (k + 3)) ∈ C t ∧
    ∀ i, (Fin.last (k + 2), i) ∉ C t ∧ (i, Fin.last (k + 2)) ∉ C t) ∧
  ∀ t s : Fin k, s.val = t.val + 1 → ∀ i j : Fin (k + 2),
    (i.castSucc, j.castSucc) ∈ C t → (i.succ, j.succ) ∈ C s

def SeparatedCuts (k : ℕ) : Type :=
  {C : Fin k → Finset (Fin (k + 3) × Fin (k + 3)) // IsSeparatedCuts k C}

def encodeCuts (k : ℕ) (A : Fin (k + 3) → Fin (k + 3) → ℕ) (t : Fin k) :
    Finset (Fin (k + 3) × Fin (k + 3)) :=
  Finset.univ.filter (fun p => A p.1 p.2 ≤ t.val)

def decodeCuts (k : ℕ) (C : Fin k → Finset (Fin (k + 3) × Fin (k + 3)))
    (i j : Fin (k + 3)) : ℕ :=
  (Finset.univ.filter (fun t : Fin k => (i, j) ∉ C t)).card

theorem encodeCuts_monotone (k : ℕ) (A : Fin (k + 3) → Fin (k + 3) → ℕ) :
    Monotone (encodeCuts k A) := by
  intro t s hts p hp
  simp only [encodeCuts, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  exact hp.trans hts

theorem decodeCuts_le (k : ℕ) (C : Fin k → Finset (Fin (k + 3) × Fin (k + 3)))
    (i j : Fin (k + 3)) : decodeCuts k C i j ≤ k := by
  simpa only [decodeCuts, Finset.card_univ, Fintype.card_fin] using
    (Finset.card_filter_le (Finset.univ : Finset (Fin k)) (fun t => (i, j) ∉ C t))

theorem decodeCuts_le_iff_mem (k : ℕ) (C : Fin k → Finset (Fin (k + 3) × Fin (k + 3)))
    (hn : Monotone C) (i j : Fin (k + 3)) (t : Fin k) :
    decodeCuts k C i j ≤ t.val ↔ (i, j) ∈ C t := by
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
    change t.val + 1 ≤ decodeCuts k C i j at hc
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

theorem encodeCuts_valid (k : ℕ) (A : Fin (k + 3) → Fin (k + 3) → ℕ)
    (hA : IsR2Array k A) : IsSeparatedCuts k (encodeCuts k A) := by
  have hm := array_steps_monotone k A hA.2.2.1
  have hb := (isR2Array_iff_boundary k A).mp hA
  refine ⟨?_, encodeCuts_monotone k A, ?_, ?_⟩
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

theorem decodeCuts_monotone (k : ℕ) (C : Fin k → Finset (Fin (k + 3) × Fin (k + 3)))
    (hC : IsSeparatedCuts k C) : ArrayMonotone k (decodeCuts k C) := by
  intro i i' j j' hi hj
  apply Finset.card_le_card
  intro t ht
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  intro hnew
  exact (Finset.mem_filter.mp ht).2 (hC.1 t (i', j') (i, j) hi hj hnew)

theorem decodeCuts_origin (k : ℕ) (C : Fin k → Finset (Fin (k + 3) × Fin (k + 3)))
    (hC : IsSeparatedCuts k C) : decodeCuts k C 0 0 = 0 := by
  apply Finset.card_filter_eq_zero_iff.mpr
  intro t ht hnot
  exact hnot (hC.2.2.1 t).1

theorem decodeCuts_edges (k : ℕ) (C : Fin k → Finset (Fin (k + 3) × Fin (k + 3)))
    (hC : IsSeparatedCuts k C) (i : Fin (k + 3)) :
    decodeCuts k C (Fin.last (k + 2)) i = k ∧ decodeCuts k C i (Fin.last (k + 2)) = k := by
  constructor
  · calc
      decodeCuts k C (Fin.last (k + 2)) i = (Finset.univ : Finset (Fin k)).card :=
        Finset.card_filter_eq_iff.mpr (fun t _ => ((hC.2.2.1 t).2 i).1)
      _ = k := by simp
  · calc
      decodeCuts k C i (Fin.last (k + 2)) = (Finset.univ : Finset (Fin k)).card :=
        Finset.card_filter_eq_iff.mpr (fun t _ => ((hC.2.2.1 t).2 i).2)
      _ = k := by simp

theorem decodeCuts_diagonal (k : ℕ) (C : Fin k → Finset (Fin (k + 3) × Fin (k + 3)))
    (hC : IsSeparatedCuts k C) (i j : Fin (k + 2)) :
    decodeCuts k C i.succ j.succ ≤ decodeCuts k C i.castSucc j.castSucc + 1 := by
  by_contra hbad
  have hhigh := decodeCuts_le k C i.succ j.succ
  let t : Fin k := ⟨decodeCuts k C i.castSucc j.castSucc, by omega⟩
  let s : Fin k := ⟨decodeCuts k C i.castSucc j.castSucc + 1, by omega⟩
  have hp : (i.castSucc, j.castSucc) ∈ C t :=
    (decodeCuts_le_iff_mem k C hC.2.1 _ _ t).mp (le_refl _)
  have hq := hC.2.2.2 t s rfl i j hp
  have hle := (decodeCuts_le_iff_mem k C hC.2.1 _ _ s).mpr hq
  change decodeCuts k C i.succ j.succ ≤ decodeCuts k C i.castSucc j.castSucc + 1 at hle
  exact hbad hle

theorem decodeCuts_valid (k : ℕ) (C : Fin k → Finset (Fin (k + 3) × Fin (k + 3)))
    (hC : IsSeparatedCuts k C) : IsR2Array k (decodeCuts k C) := by
  apply (isR2Array_iff_boundary k (decodeCuts k C)).mpr
  exact ⟨decodeCuts_origin k C hC, decodeCuts_monotone k C hC,
    decodeCuts_edges k C hC, decodeCuts_diagonal k C hC⟩

theorem decode_encodeCuts (k : ℕ) (A : Fin (k + 3) → Fin (k + 3) → ℕ)
    (hA : ∀ i j, A i j ≤ k) : decodeCuts k (encodeCuts k A) = A := by
  funext i j
  apply le_antisymm
  · by_cases ha : A i j < k
    · let t : Fin k := ⟨A i j, ha⟩
      apply (decodeCuts_le_iff_mem k (encodeCuts k A) (encodeCuts_monotone k A) i j t).mpr
      simp only [encodeCuts, Finset.mem_filter, Finset.mem_univ, true_and]
      exact le_refl _
    · exact (decodeCuts_le k (encodeCuts k A) i j).trans (Nat.le_of_not_gt ha)
  · by_cases hd : decodeCuts k (encodeCuts k A) i j < k
    · let t : Fin k := ⟨decodeCuts k (encodeCuts k A) i j, hd⟩
      have hm := (decodeCuts_le_iff_mem k (encodeCuts k A) (encodeCuts_monotone k A) i j t).mp (le_refl _)
      simpa only [encodeCuts, Finset.mem_filter, Finset.mem_univ, true_and] using hm
    · exact (hA i j).trans (Nat.le_of_not_gt hd)

theorem encode_decodeCuts (k : ℕ) (C : Fin k → Finset (Fin (k + 3) × Fin (k + 3)))
    (hn : Monotone C) : encodeCuts k (decodeCuts k C) = C := by
  funext t
  apply Finset.ext
  intro p
  simp only [encodeCuts, Finset.mem_filter, Finset.mem_univ, true_and]
  exact decodeCuts_le_iff_mem k C hn p.1 p.2 t

def arrayCutsEquiv (k : ℕ) : R2Array k ≃ SeparatedCuts k where
  toFun A := ⟨encodeCuts k A.1, encodeCuts_valid k A.1 A.2⟩
  invFun C := ⟨decodeCuts k C.1, decodeCuts_valid k C.1 C.2⟩
  left_inv A := by
    apply Subtype.ext
    exact decode_encodeCuts k A.1 (r2Array_value_le_endpoint k A.1 A.2)
  right_inv C := by
    apply Subtype.ext
    exact encode_decodeCuts k C.1 C.2.2.1

theorem separatedCuts_finite (k : ℕ) : Finite (SeparatedCuts k) := by
  unfold SeparatedCuts
  infer_instance

theorem r2Array_card_eq_separatedCuts (k : ℕ) :
    Nat.card (R2Array k) = Nat.card (SeparatedCuts k) := Nat.card_congr (arrayCutsEquiv k)

theorem separatedCuts_zero_card : Nat.card (SeparatedCuts 0) = 1 := by
  apply Nat.card_eq_one_iff_unique.mpr
  constructor
  · constructor
    intro C D
    apply Subtype.ext
    funext t
    exact Fin.elim0 t
  · refine ⟨⟨fun t => Fin.elim0 t, ?_⟩⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t; exact Fin.elim0 t
    · intro t; exact Fin.elim0 t
    · intro t; exact Fin.elim0 t
    · intro t; exact Fin.elim0 t

theorem r2Array_three_card : Nat.card (R2Array 0) = 1 := by
  rw [r2Array_card_eq_separatedCuts, separatedCuts_zero_card]

end Hardinian
