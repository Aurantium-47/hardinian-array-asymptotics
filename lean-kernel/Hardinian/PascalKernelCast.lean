import Hardinian.PascalWInterval
import Hardinian.IntervalKernel
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators

namespace Hardinian.FiniteAlgebra

theorem binomialKernel_eq_int_interval (u v : ℕ) :
    Hardinian.binomialKernel u v =
      (((∑ t ∈ Finset.Ico u v, (Nat.choose (u + v) t : ℤ)) : ℤ) : ℝ) /
        (2 : ℝ) ^ (u + v) := by
  simp only [Hardinian.binomialKernel, Hardinian.binomialMass,
    Int.cast_sum, Int.cast_natCast, Finset.sum_div]

theorem pascalTwoRowSum_cast_eq_pow_mul_kernel
    (m : ℕ) (u v : Fin m) (huv : u < v) :
    ((pascalTwoRowSum m u v : ℤ) : ℝ) =
      (2 : ℝ) ^ (u.val + v.val) * Hardinian.binomialKernel u.val v.val := by
  have hpow : (2 : ℝ) ^ (u.val + v.val) ≠ 0 := by positivity
  have hcast : ((pascalTwoRowSum m u v : ℤ) : ℝ) =
      (((∑ t ∈ Finset.Ico u.val v.val, (Nat.choose (u.val + v.val) t : ℤ)) : ℤ) : ℝ) :=
    congrArg (fun z : ℤ => (z : ℝ)) (pascalTwoRowSum_eq_interval m u v huv)
  rw [hcast, binomialKernel_eq_int_interval]
  field_simp [hpow] <;> ring

theorem pascalTwoRowSum_cast_square
    (m : ℕ) (u v : Fin m) (huv : u < v) :
    ((pascalTwoRowSum m u v : ℤ) : ℝ) ^ 2 =
      (4 : ℝ) ^ (u.val + v.val) * Hardinian.binomialKernel u.val v.val ^ 2 := by
  rw [pascalTwoRowSum_cast_eq_pow_mul_kernel m u v huv, mul_pow]
  have hpow : ((2 : ℝ) ^ (u.val + v.val)) ^ 2 = (4 : ℝ) ^ (u.val + v.val) := by
    rw [← pow_mul, Nat.mul_comm (u.val + v.val) 2, pow_mul]
    norm_num
  rw [hpow]

theorem pascalTwoRowSum_self_cast_eq_kernel (m : ℕ) (u : Fin m) :
    ((pascalTwoRowSum m u u : ℤ) : ℝ) =
      (2 : ℝ) ^ (u.val + u.val) * Hardinian.binomialKernel u.val u.val := by
  simp [pascalTwoRowSum_self, Hardinian.binomialKernel]

end Hardinian.FiniteAlgebra
