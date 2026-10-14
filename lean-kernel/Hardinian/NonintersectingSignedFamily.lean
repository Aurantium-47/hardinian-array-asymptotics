import Hardinian.MarkedPathFamilySwap
import Hardinian.GridPathSeparation
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Sigma.Basic
import Mathlib.Logic.Equiv.Basic

namespace Hardinian

open scoped BigOperators

def SignedVertexDisjoint {k N : ℕ} {u v : Fin k → Fin (N + 1)} (F : SignedFamily u v) : Prop :=
  ∀ i j : Fin k, i ≠ j → VertexDisjoint (F.2 i) (F.2 j)

def GoodSignedFamily {k N : ℕ} (u v : Fin k → Fin (N + 1)) :=
  {F : SignedFamily u v // SignedVertexDisjoint F}

def IdentityDisjointFamily {k N : ℕ} (u v : Fin k → Fin (N + 1)) :=
  {P : ∀ i : Fin k, GridPath (u i).val (v i).val //
    ∀ i j : Fin k, i ≠ j → VertexDisjoint (P i) (P j)}

theorem nonintersecting_sinks_strictMono {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (hu : StrictMono u) (F : SignedFamily u v) (hd : SignedVertexDisjoint F) :
    StrictMono (fun i => v (F.1 i)) := by
  intro i j hij
  exact ordered_paths_sink_lt (F.2 i) (F.2 j) (hu hij) (hd i j (ne_of_lt hij))

theorem ordered_nonintersecting_perm_eq_id {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (hu : StrictMono u) (hv : StrictMono v) (F : SignedFamily u v)
    (hd : SignedVertexDisjoint F) : F.1 = Equiv.refl (Fin k) := by
  have hs := nonintersecting_sinks_strictMono hu F hd
  have hcomp := Tuple.unique_monotone (f := v) (σ := F.1) (τ := Equiv.refl (Fin k))
    hs.monotone (by intro i j hij; exact hv.monotone hij)
  apply Equiv.ext
  intro i
  exact hv.injective (congrFun hcomp i)

def identityToGood {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (P : IdentityDisjointFamily u v) : GoodSignedFamily u v :=
  ⟨⟨Equiv.refl (Fin k), P.1⟩, P.2⟩

theorem identityToGood_injective {k N : ℕ} {u v : Fin k → Fin (N + 1)} :
    Function.Injective (@identityToGood k N u v) := by
  intro P Q h
  apply Subtype.ext
  have hval : (⟨Equiv.refl (Fin k), P.1⟩ : SignedFamily u v) = ⟨Equiv.refl (Fin k), Q.1⟩ :=
    congrArg Subtype.val h
  exact sigma_mk_injective (β := fun σ : Equiv.Perm (Fin k) => PathTuple u v σ)
    (i := Equiv.refl (Fin k)) hval

theorem identityToGood_surjective {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (hu : StrictMono u) (hv : StrictMono v) : Function.Surjective (@identityToGood k N u v) := by
  intro G
  rcases G with ⟨⟨σ, P⟩, hP⟩
  have hσ : σ = Equiv.refl (Fin k) :=
    ordered_nonintersecting_perm_eq_id hu hv (⟨σ, P⟩ : SignedFamily u v) hP
  subst σ
  exact ⟨⟨P, hP⟩, rfl⟩

noncomputable def goodSignedIdentityEquiv {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (hu : StrictMono u) (hv : StrictMono v) : GoodSignedFamily u v ≃ IdentityDisjointFamily u v :=
  (Equiv.ofBijective (@identityToGood k N u v)
    ⟨identityToGood_injective, identityToGood_surjective hu hv⟩).symm

theorem goodSigned_identity_inverse_left {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (hu : StrictMono u) (hv : StrictMono v) (G : GoodSignedFamily u v) :
    (goodSignedIdentityEquiv hu hv).symm (goodSignedIdentityEquiv hu hv G) = G :=
  (goodSignedIdentityEquiv hu hv).symm_apply_apply G

theorem goodSigned_identity_inverse_right {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (hu : StrictMono u) (hv : StrictMono v) (P : IdentityDisjointFamily u v) :
    goodSignedIdentityEquiv hu hv ((goodSignedIdentityEquiv hu hv).symm P) = P :=
  (goodSignedIdentityEquiv hu hv).apply_symm_apply P

theorem goodSignedFamily_finite {k N : ℕ} (u v : Fin k → Fin (N + 1)) :
    Finite (GoodSignedFamily u v) := by
  unfold GoodSignedFamily
  infer_instance

noncomputable instance goodSignedFamilyFintype {k N : ℕ} (u v : Fin k → Fin (N + 1)) :
    Fintype (GoodSignedFamily u v) := by
  letI := goodSignedFamily_finite u v
  exact Fintype.ofFinite (GoodSignedFamily u v)

theorem identityDisjointFamily_finite {k N : ℕ} (u v : Fin k → Fin (N + 1)) :
    Finite (IdentityDisjointFamily u v) :=
  Finite.of_injective (@identityToGood k N u v) identityToGood_injective

theorem goodSigned_weight_one {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (hu : StrictMono u) (hv : StrictMono v) (G : GoodSignedFamily u v) :
    signedFamilyWeight G.1 = 1 := by
  change (Equiv.Perm.sign G.1.1 : ℤ) = 1
  rw [ordered_nonintersecting_perm_eq_id hu hv G.1 G.2]
  simp

theorem goodContribution_eq_card {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (hu : StrictMono u) (hv : StrictMono v) :
    (∑ G : GoodSignedFamily u v, signedFamilyWeight G.1) = (Nat.card (IdentityDisjointFamily u v) : ℤ) := by
  calc
    (∑ G : GoodSignedFamily u v, signedFamilyWeight G.1) = ∑ _G : GoodSignedFamily u v, (1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro G hG
      exact goodSigned_weight_one hu hv G
    _ = (Nat.card (GoodSignedFamily u v) : ℤ) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Nat.card_eq_fintype_card]
    _ = (Nat.card (IdentityDisjointFamily u v) : ℤ) :=
      congrArg (fun n : ℕ => (n : ℤ)) (Nat.card_congr (goodSignedIdentityEquiv hu hv))

theorem signedVertexDisjoint_iff_no_shared_visit {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (F : SignedFamily u v) : SignedVertexDisjoint F ↔
      ∀ i j : Fin k, i ≠ j → ∀ p, ¬ (familyVisits F i p ∧ familyVisits F j p) := by
  constructor
  · rintro hd i j hij p ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    exact hd i j hij s t (hs.trans ht.symm)
  · intro hn i j hij s t he
    exact hn i j hij ((F.2 i).1 s) ⟨⟨s, rfl⟩, ⟨t, he.symm⟩⟩

theorem signedVertexDisjoint_iff_no_mark {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (F : SignedFamily u v) : SignedVertexDisjoint F ↔
      ¬ ∃ M : MarkedFamily u v, M.family = F := by
  constructor
  · rintro hd ⟨M, hM⟩
    subst F
    exact hd M.left M.right (ne_of_lt M.ordered) (markedLeftCut M) (markedRightCut M) M.meet
  · intro hn i j hij s t he
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · apply hn
      exact ⟨⟨F, i, j, hlt, s.val, t.val, s.isLt, t.isLt, he⟩, rfl⟩
    · apply hn
      exact ⟨⟨F, j, i, hgt, t.val, s.val, t.isLt, s.isLt, he.symm⟩, rfl⟩

theorem goodSignedFamily_small_all {k N : ℕ} {u v : Fin k → Fin (N + 1)}
    (hk : k ≤ 1) (F : SignedFamily u v) : SignedVertexDisjoint F := by
  intro i j hij
  have hi := i.isLt
  have hj := j.isLt
  exact (hij (Fin.ext (by omega))).elim

theorem identityDisjointFamily_zero_card {N : ℕ} (u v : Fin 0 → Fin (N + 1)) :
    Nat.card (IdentityDisjointFamily u v) = 1 := by
  apply Nat.card_eq_one_iff_unique.mpr
  constructor
  · constructor
    intro P Q
    apply Subtype.ext
    funext i
    exact Fin.elim0 i
  · exact ⟨⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩⟩

theorem goodSignedFamily_zero_card {N : ℕ} (u v : Fin 0 → Fin (N + 1)) :
    Nat.card (GoodSignedFamily u v) = 1 := by
  have hu : StrictMono u := by intro i; exact Fin.elim0 i
  have hv : StrictMono v := by intro i; exact Fin.elim0 i
  exact (Nat.card_congr (goodSignedIdentityEquiv hu hv)).trans (identityDisjointFamily_zero_card u v)

noncomputable def identityDisjointFamily_one_equiv {N : ℕ} (u v : Fin 1 → Fin (N + 1)) :
    IdentityDisjointFamily u v ≃ GridPath (u 0).val (v 0).val := by
  let e : IdentityDisjointFamily u v ≃ (∀ i : Fin 1, GridPath (u i).val (v i).val) :=
    Equiv.subtypeUnivEquiv (fun P => by
      intro i j hij
      exact (hij (Subsingleton.elim i j)).elim)
  exact e.trans (Equiv.piUnique _)

noncomputable def goodSignedFamily_one_equiv {N : ℕ} (u v : Fin 1 → Fin (N + 1)) :
    GoodSignedFamily u v ≃ GridPath (u 0).val (v 0).val := by
  have hu : StrictMono u := by
    intro i j hij
    exact ((ne_of_lt hij) (Subsingleton.elim i j)).elim
  have hv : StrictMono v := by
    intro i j hij
    exact ((ne_of_lt hij) (Subsingleton.elim i j)).elim
  exact (goodSignedIdentityEquiv hu hv).trans (identityDisjointFamily_one_equiv u v)

end Hardinian
