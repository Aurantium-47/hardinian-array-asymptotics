import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.NormNum

open scoped BigOperators

namespace Hardinian.FiniteAlgebra

/-- A finite first-coordinate cutoff contains the complete nonzero Vandermonde support. -/
theorem pascal_antidiagonal_range (m u v t : ℕ) (hu : u < m) :
    (∑ i ∈ Finset.range m,
      if i ≤ t then (Nat.choose u i : ℤ) * (Nat.choose v (t - i) : ℤ) else 0) =
      (Nat.choose (u + v) t : ℤ) := by
  let f : ℕ → ℤ := fun i =>
    if i ≤ t then (Nat.choose u i : ℤ) * (Nat.choose v (t - i) : ℤ) else 0
  have hbase : (∑ i ∈ Finset.range (t + 1), f i) = (Nat.choose (u + v) t : ℤ) := by
    calc
      (∑ i ∈ Finset.range (t + 1), f i) =
          ∑ i ∈ Finset.range (t + 1), (Nat.choose u i : ℤ) * (Nat.choose v (t - i) : ℤ) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hit : i ≤ t := by
          have := Finset.mem_range.mp hi
          omega
        exact if_pos hit
      _ = (Nat.choose (u + v) t : ℤ) := by
        have h := congrArg (fun z : ℕ => (z : ℤ)) (Nat.add_choose_eq u v t)
        simpa only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
          Nat.cast_sum, Nat.cast_mul] using h.symm
  change (∑ i ∈ Finset.range m, f i) = _
  by_cases hm : m ≤ t + 1
  · calc
      (∑ i ∈ Finset.range m, f i) = ∑ i ∈ Finset.range (t + 1), f i := by
        apply Finset.sum_subset (Finset.range_mono hm)
        intro i hi hnot
        have hmi : m ≤ i := by
          have : ¬ i < m := by simpa only [Finset.mem_range] using hnot
          omega
        have hui : u < i := lt_of_lt_of_le hu hmi
        simp [f, Nat.choose_eq_zero_of_lt hui]
      _ = _ := hbase
  · have htm : t + 1 ≤ m := by omega
    have hext : (∑ i ∈ Finset.range (t + 1), f i) = ∑ i ∈ Finset.range m, f i := by
      apply Finset.sum_subset (Finset.range_mono htm)
      intro i hi hnot
      have hit : ¬ i ≤ t := by
        have : ¬ i < t + 1 := by simpa only [Finset.mem_range] using hnot
        omega
      simp [f, hit]
    exact hext.symm.trans hbase

/-- The second-coordinate cutoff discards only zero binomial coefficients. -/
theorem pascal_antidiagonal_inner (m u v i t : ℕ) (hv : v < m) :
    (∑ j ∈ Finset.range m,
      if i + j = t then (Nat.choose u i : ℤ) * (Nat.choose v j : ℤ) else 0) =
      if i ≤ t then (Nat.choose u i : ℤ) * (Nat.choose v (t - i) : ℤ) else 0 := by
  by_cases hi : i ≤ t
  · rw [if_pos hi]
    have hit : i + (t - i) = t := by omega
    calc
      (∑ j ∈ Finset.range m,
        if i + j = t then (Nat.choose u i : ℤ) * (Nat.choose v j : ℤ) else 0) =
          if i + (t - i) = t then
            (Nat.choose u i : ℤ) * (Nat.choose v (t - i) : ℤ) else 0 := by
        apply Finset.sum_eq_single (t - i)
        · intro j hj hne
          have hij : i + j ≠ t := by omega
          exact if_neg hij
        · intro hnot
          have hm : m ≤ t - i := by
            have : ¬ t - i < m := by simpa only [Finset.mem_range] using hnot
            omega
          have hvt : v < t - i := lt_of_lt_of_le hv hm
          simp [Nat.choose_eq_zero_of_lt hvt]
      _ = _ := by simp only [hit, if_true]
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro j hj
    have hij : i + j ≠ t := by omega
    exact if_neg hij

theorem pascal_bounded_antidiagonal (m u v t : ℕ) (hu : u < m) (hv : v < m) :
    (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
      if i + j = t then (Nat.choose u i : ℤ) * (Nat.choose v j : ℤ) else 0) =
      (Nat.choose (u + v) t : ℤ) := by
  calc
    (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
      if i + j = t then (Nat.choose u i : ℤ) * (Nat.choose v j : ℤ) else 0) =
        ∑ i ∈ Finset.range m,
          if i ≤ t then (Nat.choose u i : ℤ) * (Nat.choose v (t - i) : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact pascal_antidiagonal_inner m u v i t hv
    _ = _ := pascal_antidiagonal_range m u v t hu

theorem pascal_fin_antidiagonal (m : ℕ) (u v : Fin m) (t : ℕ) :
    (∑ i : Fin m, ∑ j : Fin m,
      if i.val + j.val = t then
        (Nat.choose u.val i.val : ℤ) * (Nat.choose v.val j.val : ℤ) else 0) =
      (Nat.choose (u.val + v.val) t : ℤ) := by
  simpa only [Finset.sum_range] using
    pascal_bounded_antidiagonal m u.val v.val t u.isLt v.isLt

/-- A strict threshold in the actual finite rectangle is a binomial prefix sum. -/
theorem pascal_bounded_prefix_convolution (m u v r : ℕ) (hu : u < m) (hv : v < m) :
    (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
      if i + j < r then (Nat.choose u i : ℤ) * (Nat.choose v j : ℤ) else 0) =
      ∑ t ∈ Finset.range r, (Nat.choose (u + v) t : ℤ) := by
  symm
  calc
    (∑ t ∈ Finset.range r, (Nat.choose (u + v) t : ℤ)) =
        ∑ t ∈ Finset.range r, ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
          if i + j = t then (Nat.choose u i : ℤ) * (Nat.choose v j : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro t ht
      exact (pascal_bounded_antidiagonal m u v t hu hv).symm
    _ = ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, ∑ t ∈ Finset.range r,
        if i + j = t then (Nat.choose u i : ℤ) * (Nat.choose v j : ℤ) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.sum_ite_eq, Finset.mem_range]

theorem pascal_fin_prefix_convolution (m : ℕ) (u v : Fin m) (r : ℕ) :
    (∑ i : Fin m, ∑ j : Fin m,
      if i.val + j.val < r then
        (Nat.choose u.val i.val : ℤ) * (Nat.choose v.val j.val : ℤ) else 0) =
      ∑ t ∈ Finset.range r, (Nat.choose (u.val + v.val) t : ℤ) := by
  simpa only [Finset.sum_range] using
    pascal_bounded_prefix_convolution m u.val v.val r u.isLt v.isLt

end Hardinian.FiniteAlgebra
