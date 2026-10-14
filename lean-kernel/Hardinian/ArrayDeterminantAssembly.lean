import Hardinian.EndpointOmissions
import Hardinian.SignedCancellationLGV
import Hardinian.PascalMatrices
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Hardinian

open FiniteAlgebra
open scoped BigOperators

noncomputable def omittedIdentityEquiv {k : ℕ} (I J : TwoSet (k + 2)) :
    OmittedEndpointFiber I J ≃
      IdentityDisjointFamily (N := k + 1) (fun i => omit₂ I i) (fun i => omit₂ J i) :=
  Equiv.refl _

theorem omittedIdentity_inverse_left {k : ℕ} (I J : TwoSet (k + 2))
    (P : OmittedEndpointFiber I J) :
    (omittedIdentityEquiv I J).symm (omittedIdentityEquiv I J P) = P :=
  (omittedIdentityEquiv I J).symm_apply_apply P

theorem omittedIdentity_inverse_right {k : ℕ} (I J : TwoSet (k + 2))
    (P : IdentityDisjointFamily (N := k + 1) (fun i => omit₂ I i) (fun i => omit₂ J i)) :
    omittedIdentityEquiv I J ((omittedIdentityEquiv I J).symm P) = P :=
  (omittedIdentityEquiv I J).apply_symm_apply P

theorem omittedIdentity_path {k : ℕ} (I J : TwoSet (k + 2))
    (P : OmittedEndpointFiber I J) (i : Fin k) :
    (omittedIdentityEquiv I J P).1 i = P.1 i := rfl

theorem omitted_gridPathMatrix_eq_submatrix {k : ℕ} (I J : TwoSet (k + 2)) :
    gridPathMatrix (N := k + 1) (fun i => omit₂ I i) (fun j => omit₂ J j) =
      (symmetricPascal (k + 2)).submatrix (omit₂ I) (omit₂ J) := rfl

theorem omitted_fiber_card_eq_complementary_det {k : ℕ} (I J : TwoSet (k + 2)) :
    (Nat.card (OmittedEndpointFiber I J) : ℤ) =
      complement₂ (symmetricPascal (k + 2)) I J := by
  calc
    (Nat.card (OmittedEndpointFiber I J) : ℤ) =
        (Nat.card (IdentityDisjointFamily (N := k + 1)
          (fun i => omit₂ I i) (fun i => omit₂ J i)) : ℤ) :=
      congrArg (fun q : ℕ => (q : ℤ)) (Nat.card_congr (omittedIdentityEquiv I J))
    _ = (gridPathMatrix (N := k + 1) (fun i => omit₂ I i) (fun i => omit₂ J i)).det :=
      (gridPathMatrix_det_eq_identityDisjoint_card (N := k + 1)
        (u := fun i => omit₂ I i) (v := fun i => omit₂ J i)
        (omit₂ I).strictMono (omit₂ J).strictMono).symm
    _ = complement₂ (symmetricPascal (k + 2)) I J :=
      congrArg Matrix.det (omitted_gridPathMatrix_eq_submatrix I J)

/-- The original arrays have side k+3. I deletes source rows and J deletes sink columns. -/
theorem array_card_eq_complementary_det_sum (k : ℕ) :
    (Nat.card (R2Array k) : ℤ) =
      ∑ I : TwoSet (k + 2), ∑ J : TwoSet (k + 2),
        complement₂ (symmetricPascal (k + 2)) I J := by
  calc
    (Nat.card (R2Array k) : ℤ) =
        ((∑ I : TwoSet (k + 2), ∑ J : TwoSet (k + 2),
          Nat.card (OmittedEndpointFiber I J) : ℕ) : ℤ) :=
      congrArg (fun q : ℕ => (q : ℤ)) (array_card_eq_omitted_fiber_sum k)
    _ = ∑ I : TwoSet (k + 2), ∑ J : TwoSet (k + 2),
        (Nat.card (OmittedEndpointFiber I J) : ℤ) := by simp only [Nat.cast_sum]
    _ = ∑ I : TwoSet (k + 2), ∑ J : TwoSet (k + 2),
        complement₂ (symmetricPascal (k + 2)) I J := by
      apply Finset.sum_congr rfl
      intro I hI
      apply Finset.sum_congr rfl
      intro J hJ
      exact omitted_fiber_card_eq_complementary_det I J

theorem array_card_eq_pascal_submatrix_det_sum (k : ℕ) :
    (Nat.card (R2Array k) : ℤ) =
      ∑ I : TwoSet (k + 2), ∑ J : TwoSet (k + 2),
        Matrix.det ((symmetricPascal (k + 2)).submatrix (omit₂ I) (omit₂ J)) :=
  array_card_eq_complementary_det_sum k

theorem omittedIndex_zero_card : Nat.card (TwoSet 2) = 1 :=
  (Nat.card_congr (endpointSetComplementEquiv 0)).symm.trans endpointSet_zero_card

theorem omitted_complementary_det_zero (I J : TwoSet 2) :
    complement₂ (k := 0) (symmetricPascal 2) I J = 1 :=
  complement₂_zero (symmetricPascal 2) I J

theorem array_determinant_zero_card : Nat.card (R2Array 0) = 1 :=
  (array_card_eq_pathFamily 0).trans pathFamily_zero_card

theorem array_complementary_det_sum_zero :
    (∑ I : TwoSet 2, ∑ J : TwoSet 2,
      complement₂ (k := 0) (symmetricPascal 2) I J) = (1 : ℤ) := by
  rw [← array_card_eq_complementary_det_sum 0, array_determinant_zero_card, Nat.cast_one]

end Hardinian
