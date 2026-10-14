import Hardinian.EndpointFibers
import Hardinian.ComplementaryMinorTwo

open scoped BigOperators

namespace Hardinian

open FiniteAlgebra

def endpointOmissions {k : ℕ} (S : EndpointSet k) : TwoSet (k + 2) :=
  ⟨S.1ᶜ, by
    rw [Finset.card_compl, Fintype.card_fin, S.2]
    omega⟩

def remainingEndpointSet {k : ℕ} (I : TwoSet (k + 2)) : EndpointSet k :=
  ⟨I.1ᶜ, two_complement_card I⟩

theorem remainingEndpointSet_endpointOmissions {k : ℕ} (S : EndpointSet k) :
    remainingEndpointSet (endpointOmissions S) = S := by
  apply Subtype.ext
  change (S.1ᶜ)ᶜ = S.1
  exact compl_compl S.1

theorem endpointOmissions_remainingEndpointSet {k : ℕ} (I : TwoSet (k + 2)) :
    endpointOmissions (remainingEndpointSet I) = I := by
  apply Subtype.ext
  change (I.1ᶜ)ᶜ = I.1
  exact compl_compl I.1

def endpointSetComplementEquiv (k : ℕ) : EndpointSet k ≃ TwoSet (k + 2) where
  toFun := endpointOmissions
  invFun := remainingEndpointSet
  left_inv := remainingEndpointSet_endpointOmissions
  right_inv := endpointOmissions_remainingEndpointSet

theorem endpointEnum_complement {k : ℕ} (I : TwoSet (k + 2)) :
    endpointEnum (remainingEndpointSet I) = omit₂ I := rfl

theorem omit₂_endpointOmissions {k : ℕ} (S : EndpointSet k) :
    omit₂ (endpointOmissions S) = endpointEnum S :=
  (endpointEnum_complement (endpointOmissions S)).symm.trans
    (congrArg (fun T : EndpointSet k => endpointEnum T) (remainingEndpointSet_endpointOmissions S))

noncomputable def OmittedEndpointFiber {k : ℕ} (I J : TwoSet (k + 2)) :=
  DisjointEndpointTuple (omit₂ I) (omit₂ J)

noncomputable def OmittedEndpointFamily (k : ℕ) :=
  Σ I : TwoSet (k + 2), Σ J : TwoSet (k + 2), OmittedEndpointFiber I J

noncomputable def remainingEndpointFiberEquiv {k : ℕ} (I J : TwoSet (k + 2)) :
    EndpointPathFiber (remainingEndpointSet I) (remainingEndpointSet J) ≃ OmittedEndpointFiber I J :=
  disjointEndpointTupleCongr (endpointEnum_complement I) (endpointEnum_complement J)

noncomputable def endpointFiberOmissionEquiv (k : ℕ) :
    EndpointFiberFamily k ≃ OmittedEndpointFamily k :=
  Equiv.sigmaCongr (endpointSetComplementEquiv k) (fun S =>
    Equiv.sigmaCongr (endpointSetComplementEquiv k) (fun T =>
      disjointEndpointTupleCongr (omit₂_endpointOmissions S).symm (omit₂_endpointOmissions T).symm))

noncomputable def familyOmittedEndpointEquiv (k : ℕ) :
    OrderedPathFamily k ≃ OmittedEndpointFamily k :=
  (familyEndpointFiberEquiv k).trans (endpointFiberOmissionEquiv k)

noncomputable def arrayOmittedEndpointEquiv (k : ℕ) : R2Array k ≃ OmittedEndpointFamily k :=
  (arrayPathFamilyEquiv k).trans (familyOmittedEndpointEquiv k)

theorem omittedEndpoint_inverse_left (k : ℕ) (F : OrderedPathFamily k) :
    (familyOmittedEndpointEquiv k).symm (familyOmittedEndpointEquiv k F) = F :=
  (familyOmittedEndpointEquiv k).symm_apply_apply F

theorem omittedEndpoint_inverse_right (k : ℕ) (E : OmittedEndpointFamily k) :
    familyOmittedEndpointEquiv k ((familyOmittedEndpointEquiv k).symm E) = E :=
  (familyOmittedEndpointEquiv k).apply_symm_apply E

theorem arrayOmittedEndpoint_inverse_left (k : ℕ) (A : R2Array k) :
    (arrayOmittedEndpointEquiv k).symm (arrayOmittedEndpointEquiv k A) = A :=
  (arrayOmittedEndpointEquiv k).symm_apply_apply A

theorem arrayOmittedEndpoint_inverse_right (k : ℕ) (E : OmittedEndpointFamily k) :
    arrayOmittedEndpointEquiv k ((arrayOmittedEndpointEquiv k).symm E) = E :=
  (arrayOmittedEndpointEquiv k).apply_symm_apply E

theorem familyOmittedEndpoint_source (k : ℕ) (F : OrderedPathFamily k) :
    (familyOmittedEndpointEquiv k F).1.1 = (Finset.univ.image (fun t => (F.1 t).1))ᶜ := rfl

theorem familyOmittedEndpoint_sink (k : ℕ) (F : OrderedPathFamily k) :
    (familyOmittedEndpointEquiv k F).2.1.1 = (Finset.univ.image (fun t => (F.1 t).2.1))ᶜ := rfl

theorem omittedEndpointFiber_finite {k : ℕ} (I J : TwoSet (k + 2)) :
    Finite (OmittedEndpointFiber I J) := by
  letI := endpointPathFiber_finite (remainingEndpointSet I) (remainingEndpointSet J)
  exact Finite.of_equiv (EndpointPathFiber (remainingEndpointSet I) (remainingEndpointSet J))
    (remainingEndpointFiberEquiv I J)

theorem family_card_eq_omitted_fiber_sum (k : ℕ) :
    Nat.card (OrderedPathFamily k) =
      ∑ I : TwoSet (k + 2), ∑ J : TwoSet (k + 2), Nat.card (OmittedEndpointFiber I J) := by
  letI (I J : TwoSet (k + 2)) : Finite (OmittedEndpointFiber I J) := omittedEndpointFiber_finite I J
  letI (I J : TwoSet (k + 2)) : Fintype (OmittedEndpointFiber I J) := Fintype.ofFinite _
  calc
    Nat.card (OrderedPathFamily k) = Nat.card (OmittedEndpointFamily k) :=
      Nat.card_congr (familyOmittedEndpointEquiv k)
    _ = ∑ I : TwoSet (k + 2), Nat.card (Σ J : TwoSet (k + 2), OmittedEndpointFiber I J) :=
      Nat.card_sigma
    _ = ∑ I : TwoSet (k + 2), ∑ J : TwoSet (k + 2), Nat.card (OmittedEndpointFiber I J) := by
      apply Finset.sum_congr rfl
      intro I hI
      exact Nat.card_sigma

theorem array_card_eq_omitted_fiber_sum (k : ℕ) :
    Nat.card (R2Array k) =
      ∑ I : TwoSet (k + 2), ∑ J : TwoSet (k + 2), Nat.card (OmittedEndpointFiber I J) :=
  (array_card_eq_pathFamily k).trans (family_card_eq_omitted_fiber_sum k)

theorem omittedEndpointFiber_zero_card (I J : TwoSet 2) :
    Nat.card (OmittedEndpointFiber (k := 0) I J) = 1 :=
  (Nat.card_congr (remainingEndpointFiberEquiv I J)).symm.trans
    (endpointPathFiber_zero_card (remainingEndpointSet I) (remainingEndpointSet J))

theorem omittedEndpointFamily_zero_card : Nat.card (OmittedEndpointFamily 0) = 1 :=
  (Nat.card_congr (familyOmittedEndpointEquiv 0)).symm.trans pathFamily_zero_card

end Hardinian
