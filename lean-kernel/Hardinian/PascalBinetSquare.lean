import Hardinian.PascalComplementaryMinor
import Hardinian.TwoSetOrdered
import Hardinian.RectangularBinetTwo

open scoped BigOperators

namespace Hardinian.FiniteAlgebra

/-- The actual sum of Pascal minors with the two specified rows. -/
noncomputable def pascalTwoRowSum (m : ℕ) (u v : Fin m) : ℤ :=
  ∑ I : TwoSet m,
    Matrix.det ((pascalLower m).submatrix (![u, v] : Fin 2 → Fin m) (select₂ I))

theorem minor₂_pascalGram_ordered (m : ℕ) (I J : TwoSet m) :
    minor₂ (pascalGram m) J I =
      ∑ u : Fin m,
        ∑ v ∈ (Finset.univ : Finset (Fin m)).filter (fun v => u < v),
          Matrix.det ((pascalLower m).submatrix (![u, v] : Fin 2 → Fin m) (select₂ J)) *
          Matrix.det ((pascalLower m).submatrix (![u, v] : Fin 2 → Fin m) (select₂ I)) := by
  unfold minor₂ pascalGram
  rw [Matrix.submatrix_mul (pascalLower m).transpose (pascalLower m)
    (select₂ J) (id : Fin m → Fin m) (select₂ I) (Equiv.refl (Fin m)).bijective]
  rw [rectangular_binet_two_ordered]
  simp only [Matrix.submatrix_submatrix, Function.comp_def, id_eq,
    ← Matrix.transpose_submatrix, Matrix.det_transpose]

theorem sum_minor₂_pascalGram_eq_ordered_square (m : ℕ) :
    (∑ I : TwoSet m, ∑ J : TwoSet m, minor₂ (pascalGram m) J I) =
      ∑ u : Fin m,
        ∑ v ∈ (Finset.univ : Finset (Fin m)).filter (fun v => u < v),
          pascalTwoRowSum m u v ^ 2 := by
  classical
  let T : Fin m → Fin m → TwoSet m → ℤ := fun u v I =>
    Matrix.det ((pascalLower m).submatrix (![u, v] : Fin 2 → Fin m) (select₂ I))
  have hswap (I : TwoSet m) :
      (∑ J : TwoSet m, ∑ u : Fin m,
        ∑ v ∈ (Finset.univ : Finset (Fin m)).filter (fun v => u < v), T u v J * T u v I) =
      ∑ u : Fin m, ∑ v ∈ (Finset.univ : Finset (Fin m)).filter (fun v => u < v),
        ∑ J : TwoSet m, T u v J * T u v I := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u hu
    exact Finset.sum_comm
  calc
    (∑ I : TwoSet m, ∑ J : TwoSet m, minor₂ (pascalGram m) J I) =
        ∑ I : TwoSet m, ∑ u : Fin m,
          ∑ v ∈ (Finset.univ : Finset (Fin m)).filter (fun v => u < v),
            ∑ J : TwoSet m, T u v J * T u v I := by
      simp_rw [minor₂_pascalGram_ordered]
      exact Finset.sum_congr rfl (fun I hI => hswap I)
    _ = ∑ u : Fin m, ∑ v ∈ (Finset.univ : Finset (Fin m)).filter (fun v => u < v),
        ∑ I : TwoSet m, ∑ J : TwoSet m, T u v J * T u v I := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u hu
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      change (∑ I : TwoSet m, ∑ J : TwoSet m, T u v J * T u v I) =
        (∑ I : TwoSet m, T u v I) ^ 2
      rw [pow_two, Fintype.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro I hI
      apply Finset.sum_congr rfl
      intro J hJ
      exact mul_comm _ _

theorem complementary_pascal_sum_eq_ordered_square (k : ℕ) :
    (∑ I : TwoSet (k + 2), ∑ J : TwoSet (k + 2),
      complement₂ (symmetricPascal (k + 2)) I J) =
      ∑ u : Fin (k + 2),
        ∑ v ∈ (Finset.univ : Finset (Fin (k + 2))).filter (fun v => u < v),
          pascalTwoRowSum (k + 2) u v ^ 2 := by
  simp_rw [complementary_symmetricPascal]
  exact sum_minor₂_pascalGram_eq_ordered_square (k + 2)

theorem pascalTwoRowSum_eq_ordered (m : ℕ) (u v : Fin m) :
    pascalTwoRowSum m u v =
      ∑ i : Fin m,
        ∑ j ∈ (Finset.univ : Finset (Fin m)).filter (fun j => i < j),
          ((Nat.choose u.val i.val : ℤ) * (Nat.choose v.val j.val : ℤ) -
           (Nat.choose u.val j.val : ℤ) * (Nat.choose v.val i.val : ℤ)) := by
  simpa only [pascalTwoRowSum, Matrix.det_fin_two, Matrix.submatrix_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, pascalLower] using
    sum_twoSet_eq_ordered m (fun i j =>
      (Nat.choose u.val i.val : ℤ) * (Nat.choose v.val j.val : ℤ) -
        (Nat.choose u.val j.val : ℤ) * (Nat.choose v.val i.val : ℤ))

theorem pascal_square_sum_eq_zero_of_lt_two (m : ℕ) (hm : m < 2) :
    (∑ u : Fin m,
      ∑ v ∈ (Finset.univ : Finset (Fin m)).filter (fun v => u < v),
        pascalTwoRowSum m u v ^ 2) = 0 := by
  apply Finset.sum_eq_zero
  intro u hu
  apply Finset.sum_eq_zero
  intro v hv
  have huv := (Finset.mem_filter.mp hv).2
  change u.val < v.val at huv
  have hu' := u.isLt
  have hv' := v.isLt
  omega

theorem pascal_square_sum_two :
    (∑ u : Fin 2,
      ∑ v ∈ (Finset.univ : Finset (Fin 2)).filter (fun v => u < v),
        pascalTwoRowSum 2 u v ^ 2) = 1 := by
  norm_num [pascalTwoRowSum_eq_ordered, Finset.sum_filter, Fin.sum_univ_two]

theorem complementary_pascal_sum_zero :
    (∑ I : TwoSet 2, ∑ J : TwoSet 2,
      complement₂ (k := 0) (symmetricPascal 2) I J) = 1 := by
  rw [complementary_pascal_sum_eq_ordered_square 0]
  exact pascal_square_sum_two

end Hardinian.FiniteAlgebra
