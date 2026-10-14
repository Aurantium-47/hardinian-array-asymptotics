import Hardinian.ComplementaryJacobiTwo
import Hardinian.PascalMatrices

namespace Hardinian.FiniteAlgebra

/-- Restricting the two diagonal signs to the canonical ascending rows and columns. -/
theorem minor₂_pascalSign_conjugate {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℤ) (I J : TwoSet m) :
    minor₂ (pascalSign m * A * pascalSign m) I J =
      (-1 : ℤ) ^ (indexSum₂ I + indexSum₂ J) * minor₂ A I J := by
  simp only [minor₂, Matrix.det_fin_two, Matrix.submatrix_apply, pascalSign,
    Matrix.mul_diagonal, Matrix.diagonal_mul, indexSum₂, pow_add]
  ring

/-- The actual Pascal complementary minor is the reversed Gram minor, including k = 0. -/
theorem complementary_symmetricPascal (k : ℕ) (I J : TwoSet (k + 2)) :
    complement₂ (symmetricPascal (k + 2)) I J = minor₂ (pascalGram (k + 2)) J I := by
  rw [complementary_two_of_right_inverse k (symmetricPascal (k + 2))
    (symmetricPascalInverseWitness (k + 2))
    (symmetricPascal_mul_inverseWitness (k + 2)) I J,
    det_symmetricPascal, mul_one]
  unfold symmetricPascalInverseWitness
  rw [minor₂_pascalSign_conjugate]
  have hs : (-1 : ℤ) ^ (indexSum₂ I + indexSum₂ J) *
      (-1 : ℤ) ^ (indexSum₂ I + indexSum₂ J) = 1 :=
    pow_mul_pow_eq_one (a := (-1 : ℤ)) (b := (-1 : ℤ))
      (indexSum₂ I + indexSum₂ J) (by norm_num)
  rw [Nat.add_comm (indexSum₂ J) (indexSum₂ I), ← mul_assoc, hs, one_mul]

theorem complementary_symmetricPascal_zero (I J : TwoSet 2) :
    (1 : ℤ) = minor₂ (pascalGram 2) J I := by
  simpa only [complement₂_zero] using complementary_symmetricPascal 0 I J

end Hardinian.FiniteAlgebra
