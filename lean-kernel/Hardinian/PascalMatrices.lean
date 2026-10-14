import Hardinian.PascalConvolution
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.SemiringInverse

/-!
The finite integer Pascal matrices and their explicit two-sided inverses.
All identities hold in arbitrary natural dimension, without an invertibility hypothesis.
-/

open scoped BigOperators

namespace Hardinian.FiniteAlgebra

def pascalLower (m : ℕ) : Matrix (Fin m) (Fin m) ℤ :=
  fun u v => (Nat.choose u.val v.val : ℤ)

def pascalSign (m : ℕ) : Matrix (Fin m) (Fin m) ℤ :=
  Matrix.diagonal (fun i => (-1 : ℤ) ^ i.val)

def pascalInverseWitness (m : ℕ) : Matrix (Fin m) (Fin m) ℤ :=
  pascalSign m * pascalLower m * pascalSign m

def symmetricPascal (m : ℕ) : Matrix (Fin m) (Fin m) ℤ :=
  fun u v => (Nat.choose (u.val + v.val) u.val : ℤ)

def pascalGram (m : ℕ) : Matrix (Fin m) (Fin m) ℤ :=
  (pascalLower m).transpose * pascalLower m

def symmetricPascalInverseWitness (m : ℕ) : Matrix (Fin m) (Fin m) ℤ :=
  pascalSign m * pascalGram m * pascalSign m

theorem pascalSign_mul_self (m : ℕ) :
    pascalSign m * pascalSign m = 1 := by
  calc
    pascalSign m * pascalSign m =
        Matrix.diagonal (fun i : Fin m => (-1 : ℤ) ^ i.val * (-1 : ℤ) ^ i.val) :=
      Matrix.diagonal_mul_diagonal _ _
    _ = Matrix.diagonal (fun _ : Fin m => (1 : ℤ)) := by
      apply congrArg Matrix.diagonal
      funext i
      rw [← mul_pow]
      norm_num
    _ = 1 := Matrix.diagonal_one

theorem pascalInverseWitness_apply (m : ℕ) (u v : Fin m) :
    pascalInverseWitness m u v =
      (-1 : ℤ) ^ (u.val + v.val) * (Nat.choose u.val v.val : ℤ) := by
  simp only [pascalInverseWitness, pascalSign, Matrix.mul_diagonal,
    Matrix.diagonal_mul, pascalLower]
  rw [pow_add]
  ring

theorem pascalLower_mul_inverseWitness (m : ℕ) :
    pascalLower m * pascalInverseWitness m = 1 := by
  ext u v
  simpa only [Matrix.mul_apply, Matrix.one_apply, pascalLower,
    pascalInverseWitness_apply] using pascal_signed_convolution m u v

theorem pascalInverseWitness_mul_lower (m : ℕ) :
    pascalInverseWitness m * pascalLower m = 1 :=
  Matrix.mul_eq_one_comm.mp (pascalLower_mul_inverseWitness m)

theorem symmetricPascal_eq_mul_transpose (m : ℕ) :
    symmetricPascal m = pascalLower m * (pascalLower m).transpose := by
  ext u v
  symm
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, pascalLower,
    symmetricPascal] using pascal_gram_sum m u v

theorem det_pascalLower (m : ℕ) :
    Matrix.det (pascalLower m) = 1 := by
  have htri : (pascalLower m).BlockTriangular OrderDual.toDual := by
    intro u v huv
    change u.val < v.val at huv
    simp [pascalLower, Nat.choose_eq_zero_of_lt huv]
  rw [Matrix.det_of_lowerTriangular (pascalLower m) htri]
  simp [pascalLower]

theorem det_symmetricPascal (m : ℕ) :
    Matrix.det (symmetricPascal m) = 1 := by
  simp only [symmetricPascal_eq_mul_transpose, Matrix.det_mul,
    Matrix.det_transpose, det_pascalLower, one_mul]

theorem symmetricPascalInverseWitness_eq_transpose_mul (m : ℕ) :
    symmetricPascalInverseWitness m =
      (pascalInverseWitness m).transpose * pascalInverseWitness m := by
  have ht : (pascalSign m).transpose = pascalSign m :=
    Matrix.diagonal_transpose _
  calc
    symmetricPascalInverseWitness m =
        pascalSign m * ((pascalLower m).transpose * pascalLower m) * pascalSign m := rfl
    _ = (pascalSign m * (pascalLower m).transpose) *
        (pascalSign m * pascalSign m) * (pascalLower m * pascalSign m) := by
      rw [pascalSign_mul_self]
      simp only [mul_one, mul_assoc]
    _ = (pascalInverseWitness m).transpose * pascalInverseWitness m := by
      simp only [pascalInverseWitness, Matrix.transpose_mul, ht, mul_assoc]

theorem symmetricPascal_mul_inverseWitness (m : ℕ) :
    symmetricPascal m * symmetricPascalInverseWitness m = 1 := by
  rw [symmetricPascal_eq_mul_transpose,
    symmetricPascalInverseWitness_eq_transpose_mul]
  calc
    (pascalLower m * (pascalLower m).transpose) *
        ((pascalInverseWitness m).transpose * pascalInverseWitness m) =
        pascalLower m * ((pascalLower m).transpose * (pascalInverseWitness m).transpose) *
          pascalInverseWitness m := by simp only [mul_assoc]
    _ = pascalLower m * (pascalInverseWitness m * pascalLower m).transpose *
        pascalInverseWitness m := by rw [Matrix.transpose_mul]
    _ = 1 := by
      rw [pascalInverseWitness_mul_lower, Matrix.transpose_one, mul_one,
        pascalLower_mul_inverseWitness]

theorem symmetricPascalInverseWitness_mul (m : ℕ) :
    symmetricPascalInverseWitness m * symmetricPascal m = 1 :=
  Matrix.mul_eq_one_comm.mp (symmetricPascal_mul_inverseWitness m)

end Hardinian.FiniteAlgebra
