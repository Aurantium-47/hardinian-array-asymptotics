import Hardinian.ArrayDeterminantAssembly
import Hardinian.FiniteKernelScaling

open scoped BigOperators

namespace Hardinian

open FiniteAlgebra

/-- The count is the cardinal of the original arrays of side k+3. -/
theorem array_card_eq_pascal_square_sum (k : ℕ) :
    (Nat.card (R2Array k) : ℤ) =
      ∑ u : Fin (k + 2),
        ∑ v ∈ (Finset.univ : Finset (Fin (k + 2))).filter (fun v => u < v),
          pascalTwoRowSum (k + 2) u v ^ 2 :=
  (array_card_eq_complementary_det_sum k).trans
    (complementary_pascal_sum_eq_ordered_square k)

theorem array_card_cast_eq_pascal_square_sum (k : ℕ) :
    (Nat.card (R2Array k) : ℝ) =
      ∑ u : Fin (k + 2),
        ∑ v ∈ (Finset.univ : Finset (Fin (k + 2))).filter (fun v => u < v),
          ((pascalTwoRowSum (k + 2) u v : ℤ) : ℝ) ^ 2 := by
  have h := congrArg (fun z : ℤ => (z : ℝ)) (array_card_eq_pascal_square_sum k)
  simpa only [Int.cast_natCast, Int.cast_sum, Int.cast_pow] using h

theorem weightedKernelSum_eq_array_card (k : ℕ) :
    weightedKernelSum (k + 1) =
      (((k + 1 : ℕ) : ℝ) / (16 : ℝ) ^ (k + 1)) * (Nat.card (R2Array k) : ℝ) := by
  calc
    weightedKernelSum (k + 1) =
        (((k + 1 : ℕ) : ℝ) / (16 : ℝ) ^ (k + 1)) *
          (∑ u : Fin (k + 2),
            ∑ v ∈ (Finset.univ : Finset (Fin (k + 2))).filter (fun v => u < v),
              ((pascalTwoRowSum (k + 2) u v : ℤ) : ℝ) ^ 2) := by
      simpa only [Nat.add_assoc] using weightedKernelSum_eq_pascal_square_sum (k + 1)
    _ = _ := by rw [← array_card_cast_eq_pascal_square_sum k]

theorem array_kernel_zero_index : weightedKernelSum 1 = (1 / 16 : ℝ) := by
  simpa only [Nat.zero_add, Nat.cast_one, pow_one, mul_one, array_determinant_zero_card]
    using weightedKernelSum_eq_array_card 0

end Hardinian
