import Hardinian.CanonicalBadFamilySwap
import Hardinian.NonintersectingSignedFamily
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Hardinian

open scoped BigOperators

theorem not_bad_iff_signedVertexDisjoint {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (F : SignedFamily u v) : ¬ IsBadFamily F ↔ SignedVertexDisjoint F := by
  constructor
  · intro hn i j hij s t he
    exact hn ⟨i, j, hij, s, t, he⟩
  · rintro hd ⟨i, j, hij, s, t, he⟩
    exact hd i j hij s t he

theorem badFamily_finite {k N : ℕ} (u v : Fin k → Fin (N + 1)) :
    Finite (BadFamily u v) := by
  infer_instance

noncomputable instance badFamilyFintype {k N : ℕ} (u v : Fin k → Fin (N + 1)) :
    Fintype (BadFamily u v) := by
  letI := badFamily_finite u v
  exact Fintype.ofFinite (BadFamily u v)

noncomputable def badContribution {k N : ℕ} (u v : Fin k → Fin (N + 1)) : ℤ :=
  ∑ B : BadFamily u v, signedFamilyWeight B.1

noncomputable def goodContribution {k N : ℕ} (u v : Fin k → Fin (N + 1)) : ℤ :=
  ∑ G : GoodSignedFamily u v, signedFamilyWeight G.1

theorem badContribution_zero {k N : ℕ} (u v : Fin k → Fin (N + 1)) :
    badContribution u v = 0 := by
  classical
  unfold badContribution
  exact Finset.sum_involution (fun B _ => badSwap B)
    (fun B _ => by rw [badSwap_sign, add_neg_cancel])
    (fun B _ _ => badSwap_ne_self B)
    (fun B _ => Finset.mem_univ (badSwap B))
    (fun B _ => badSwap_involutive B)

noncomputable def signedFamilyPartitionEquiv {k N : ℕ} (u v : Fin k → Fin (N + 1)) :
    SignedFamily u v ≃ BadFamily u v ⊕ GoodSignedFamily u v := by
  classical
  exact
    { toFun := fun F => if h : IsBadFamily F then Sum.inl ⟨F, h⟩
        else Sum.inr ⟨F, (not_bad_iff_signedVertexDisjoint F).1 h⟩
      invFun := fun X => X.elim Subtype.val Subtype.val
      left_inv := by
        intro F
        by_cases h : IsBadFamily F <;> simp [h]
      right_inv := by
        intro X
        cases X with
        | inl B => simp [B.2]
        | inr G =>
          have hn : ¬ IsBadFamily G.1 := (not_bad_iff_signedVertexDisjoint G.1).2 G.2
          simp [hn] }

theorem signedFamilyPartition_weight {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (F : SignedFamily u v) : signedFamilyWeight F =
      Sum.elim (fun B : BadFamily u v => signedFamilyWeight B.1)
        (fun G : GoodSignedFamily u v => signedFamilyWeight G.1)
        (signedFamilyPartitionEquiv u v F) := by
  classical
  by_cases h : IsBadFamily F <;> simp [signedFamilyPartitionEquiv, h]

theorem signedFamilySum_partition {k N : ℕ} (u v : Fin k → Fin (N + 1)) :
    signedFamilySum u v = badContribution u v + goodContribution u v := by
  classical
  calc
    signedFamilySum u v = ∑ X : BadFamily u v ⊕ GoodSignedFamily u v,
        Sum.elim (fun B : BadFamily u v => signedFamilyWeight B.1)
          (fun G : GoodSignedFamily u v => signedFamilyWeight G.1) X :=
      Fintype.sum_equiv (signedFamilyPartitionEquiv u v) _ _ signedFamilyPartition_weight
    _ = badContribution u v + goodContribution u v := Fintype.sum_sum_type _

theorem signedFamilySum_eq_goodContribution {k N : ℕ} (u v : Fin k → Fin (N + 1)) :
    signedFamilySum u v = goodContribution u v := by
  rw [signedFamilySum_partition, badContribution_zero, zero_add]

theorem gridPathMatrix_det_eq_goodContribution {k N : ℕ} (u v : Fin k → Fin (N + 1)) :
    (gridPathMatrix u v).det = goodContribution u v := by
  rw [gridPathMatrix_det_eq_signedFamilySum, signedFamilySum_eq_goodContribution]

theorem gridPathMatrix_det_eq_identityDisjoint_card {k N : ℕ}
    {u v : Fin k → Fin (N + 1)} (hu : StrictMono u) (hv : StrictMono v) :
    (gridPathMatrix u v).det = (Nat.card (IdentityDisjointFamily u v) : ℤ) := by
  rw [gridPathMatrix_det_eq_goodContribution]
  exact goodContribution_eq_card hu hv

theorem ordered_grid_lgv_zero {N : ℕ} (u v : Fin 0 → Fin (N + 1)) :
    (gridPathMatrix u v).det = (Nat.card (IdentityDisjointFamily u v) : ℤ) := by
  rw [gridPathMatrix_det_zero, identityDisjointFamily_zero_card]

theorem ordered_grid_lgv_one {N : ℕ} (u v : Fin 1 → Fin (N + 1)) :
    (gridPathMatrix u v).det = (Nat.card (IdentityDisjointFamily u v) : ℤ) := by
  apply gridPathMatrix_det_eq_identityDisjoint_card
  · intro i j hij
    exact ((ne_of_lt hij) (Subsingleton.elim i j)).elim
  · intro i j hij
    exact ((ne_of_lt hij) (Subsingleton.elim i j)).elim

end Hardinian
