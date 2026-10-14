import Hardinian.PascalBinetSquare
import Hardinian.PascalIntervalConvolution
import Mathlib.Algebra.BigOperators.Intervals

open scoped BigOperators

namespace Hardinian.FiniteAlgebra

theorem pascal_weighted_support_range (m v : ℕ) (hv : v < m) (f : ℕ → ℤ) :
    (∑ j ∈ Finset.range m, f j * (Nat.choose v j : ℤ)) =
      ∑ j ∈ Finset.range (v + 1), f j * (Nat.choose v j : ℤ) := by
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt hv))
  intro j hj hnot
  have hvj : v < j := by
    have : ¬ j < v + 1 := by simpa only [Finset.mem_range] using hnot
    omega
  simp [Nat.choose_eq_zero_of_lt hvj]

/-- Reflect only the column support where the binomial coefficient can be nonzero. -/
theorem pascal_column_reflection (m u v i : ℕ) (hv : v < m) :
    (∑ j ∈ Finset.range m,
      if i < j then (Nat.choose u i : ℤ) * (Nat.choose v j : ℤ) else 0) =
      ∑ j ∈ Finset.range m,
        if i + j < v then (Nat.choose u i : ℤ) * (Nat.choose v j : ℤ) else 0 := by
  let f : ℕ → ℤ := fun j => if i < j then (Nat.choose u i : ℤ) else 0
  let g : ℕ → ℤ := fun j => if i + j < v then (Nat.choose u i : ℤ) else 0
  have hf :
      (∑ j ∈ Finset.range m,
        if i < j then (Nat.choose u i : ℤ) * (Nat.choose v j : ℤ) else 0) =
        ∑ j ∈ Finset.range (v + 1), f j * (Nat.choose v j : ℤ) := by
    simpa only [f, ite_mul, zero_mul] using pascal_weighted_support_range m v hv f
  have hg :
      (∑ j ∈ Finset.range m,
        if i + j < v then (Nat.choose u i : ℤ) * (Nat.choose v j : ℤ) else 0) =
        ∑ j ∈ Finset.range (v + 1), g j * (Nat.choose v j : ℤ) := by
    simpa only [g, ite_mul, zero_mul] using pascal_weighted_support_range m v hv g
  rw [hf, hg]
  calc
    (∑ j ∈ Finset.range (v + 1), f j * (Nat.choose v j : ℤ)) =
        ∑ j ∈ Finset.range (v + 1), f (v - j) * (Nat.choose v (v - j) : ℤ) := by
      simpa only [Nat.add_sub_cancel] using
        (Finset.sum_range_reflect (fun j => f j * (Nat.choose v j : ℤ)) (v + 1)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjv : j ≤ v := by
        have := Finset.mem_range.mp hj
        omega
      rw [Nat.choose_symm hjv]
      have hcond : i < v - j ↔ i + j < v := by omega
      simp only [f, g, hcond]

theorem pascal_strict_range_eq_prefix (m u v : ℕ) (hu : u < m) (hv : v < m) :
    (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
      if i < j then (Nat.choose u i : ℤ) * (Nat.choose v j : ℤ) else 0) =
      ∑ t ∈ Finset.range v, (Nat.choose (u + v) t : ℤ) := by
  calc
    (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
      if i < j then (Nat.choose u i : ℤ) * (Nat.choose v j : ℤ) else 0) =
        ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
          if i + j < v then (Nat.choose u i : ℤ) * (Nat.choose v j : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact pascal_column_reflection m u v i hv
    _ = _ := pascal_bounded_prefix_convolution m u v v hu hv

theorem pascal_strict_fin_eq_prefix (m : ℕ) (u v : Fin m) :
    (∑ i : Fin m,
      ∑ j ∈ (Finset.univ : Finset (Fin m)).filter (fun j => i < j),
        (Nat.choose u.val i.val : ℤ) * (Nat.choose v.val j.val : ℤ)) =
      ∑ t ∈ Finset.range v.val, (Nat.choose (u.val + v.val) t : ℤ) := by
  simp only [Finset.sum_filter]
  change (∑ i : Fin m, ∑ j : Fin m,
    if i.val < j.val then
      (Nat.choose u.val i.val : ℤ) * (Nat.choose v.val j.val : ℤ) else 0) = _
  simpa only [Finset.sum_range] using
    pascal_strict_range_eq_prefix m u.val v.val u.isLt v.isLt

/-- The signed row-minor sum is the exact difference of two binomial prefixes. -/
theorem pascalTwoRowSum_prefix_difference (m : ℕ) (u v : Fin m) :
    pascalTwoRowSum m u v =
      (∑ t ∈ Finset.range v.val, (Nat.choose (u.val + v.val) t : ℤ)) -
        ∑ t ∈ Finset.range u.val, (Nat.choose (u.val + v.val) t : ℤ) := by
  have hcross :
      (∑ i : Fin m,
        ∑ j ∈ (Finset.univ : Finset (Fin m)).filter (fun j => i < j),
          (Nat.choose u.val j.val : ℤ) * (Nat.choose v.val i.val : ℤ)) =
        ∑ i : Fin m,
          ∑ j ∈ (Finset.univ : Finset (Fin m)).filter (fun j => i < j),
            (Nat.choose v.val i.val : ℤ) * (Nat.choose u.val j.val : ℤ) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    exact mul_comm _ _
  rw [pascalTwoRowSum_eq_ordered]
  simp only [Finset.sum_sub_distrib]
  rw [hcross]
  simp only [pascal_strict_fin_eq_prefix, Nat.add_comm v.val u.val]

theorem pascalTwoRowSum_eq_interval (m : ℕ) (u v : Fin m) (huv : u < v) :
    pascalTwoRowSum m u v =
      ∑ t ∈ Finset.Ico u.val v.val, (Nat.choose (u.val + v.val) t : ℤ) := by
  rw [pascalTwoRowSum_prefix_difference]
  exact (Finset.sum_Ico_eq_sub
    (fun t => (Nat.choose (u.val + v.val) t : ℤ)) (Nat.le_of_lt huv)).symm

theorem pascalTwoRowSum_self (m : ℕ) (u : Fin m) :
    pascalTwoRowSum m u u = 0 := by
  rw [pascalTwoRowSum_prefix_difference, sub_self]

end Hardinian.FiniteAlgebra
