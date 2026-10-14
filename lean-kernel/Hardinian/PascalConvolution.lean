import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-!
Finite integer Pascal convolutions, including their zero-support cases.
These scalar identities do not assert an array-count or a matrix-minor formula.
-/

open scoped BigOperators

namespace Hardinian.FiniteAlgebra

theorem pascal_signed_range (m u v : ℕ) (hu : u < m) :
    (∑ t ∈ Finset.range m,
      (Nat.choose u t : ℤ) *
        ((-1 : ℤ) ^ (t + v) * (Nat.choose t v : ℤ))) =
      if u = v then 1 else 0 := by
  let f : ℕ → ℤ := fun t =>
    (Nat.choose u t : ℤ) * ((-1 : ℤ) ^ (t + v) * (Nat.choose t v : ℤ))
  change (∑ t ∈ Finset.range m, f t) = if u = v then 1 else 0
  by_cases huv : u < v
  · rw [if_neg (Nat.ne_of_lt huv)]
    apply Finset.sum_eq_zero
    intro t ht
    by_cases hut : u < t
    · simp [f, Nat.choose_eq_zero_of_lt hut]
    · have htv : t < v := by omega
      simp [f, Nat.choose_eq_zero_of_lt htv]
  · have hvu : v ≤ u := Nat.le_of_not_gt huv
    have hrestrict :
        (∑ t ∈ Finset.Ico v (u + 1), f t) = ∑ t ∈ Finset.range m, f t := by
      apply Finset.sum_subset
      · intro t ht
        have h := Finset.mem_Ico.mp ht
        exact Finset.mem_range.mpr (by omega)
      · intro t ht hnot
        by_cases htv : t < v
        · simp [f, Nat.choose_eq_zero_of_lt htv]
        · have hut : u < t := by
            have : ¬ (v ≤ t ∧ t < u + 1) := by simpa only [Finset.mem_Ico] using hnot
            omega
          simp [f, Nat.choose_eq_zero_of_lt hut]
    have hlen : u + 1 - v = (u - v) + 1 := by omega
    rw [← hrestrict, Finset.sum_Ico_eq_sum_range, hlen]
    calc
      (∑ s ∈ Finset.range ((u - v) + 1), f (v + s)) =
          ∑ s ∈ Finset.range ((u - v) + 1),
            (Nat.choose u v : ℤ) *
              ((-1 : ℤ) ^ s * (Nat.choose (u - v) s : ℤ)) := by
        apply Finset.sum_congr rfl
        intro s hs
        have hsu : v + s ≤ u := by
          have := Finset.mem_range.mp hs
          omega
        have hc : (Nat.choose u (v + s) : ℤ) * (Nat.choose (v + s) v : ℤ) =
            (Nat.choose u v : ℤ) * (Nat.choose (u - v) s : ℤ) := by
          have h := Nat.choose_mul hsu (Nat.le_add_right v s)
          simpa only [Nat.add_sub_cancel_left, Nat.cast_mul] using
            congrArg (fun x : ℕ => (x : ℤ)) h
        have hp : (-1 : ℤ) ^ ((v + s) + v) = (-1 : ℤ) ^ s := by
          have he : (v + s) + v = s + 2 * v := by omega
          rw [he, pow_add, pow_mul]
          norm_num
        dsimp [f]
        rw [hp]
        calc
          (Nat.choose u (v + s) : ℤ) *
              ((-1 : ℤ) ^ s * (Nat.choose (v + s) v : ℤ)) =
              (-1 : ℤ) ^ s *
                ((Nat.choose u (v + s) : ℤ) * (Nat.choose (v + s) v : ℤ)) := by ring
          _ = (Nat.choose u v : ℤ) *
              ((-1 : ℤ) ^ s * (Nat.choose (u - v) s : ℤ)) := by rw [hc]; ring
      _ = (Nat.choose u v : ℤ) *
          (∑ s ∈ Finset.range ((u - v) + 1),
            (-1 : ℤ) ^ s * (Nat.choose (u - v) s : ℤ)) := by rw [Finset.mul_sum]
      _ = if u = v then 1 else 0 := by
        rw [Int.alternating_sum_range_choose]
        by_cases heq : u = v
        · subst v
          simp
        · have hd : u - v ≠ 0 := by omega
          rw [if_neg hd, if_neg heq, mul_zero]

theorem pascal_signed_convolution (m : ℕ) (u v : Fin m) :
    (∑ t : Fin m,
      (Nat.choose u.val t.val : ℤ) *
        ((-1 : ℤ) ^ (t.val + v.val) * (Nat.choose t.val v.val : ℤ))) =
      if u = v then 1 else 0 := by
  simpa only [Finset.sum_range, Fin.ext_iff] using
    pascal_signed_range m u.val v.val u.isLt

theorem pascal_gram_range (m u v : ℕ) (hu : u < m) :
    (∑ t ∈ Finset.range m,
      (Nat.choose u t : ℤ) * (Nat.choose v t : ℤ)) =
      (Nat.choose (u + v) u : ℤ) := by
  have hn : (∑ t ∈ Finset.range (u + 1), Nat.choose u t * Nat.choose v t) =
      Nat.choose (u + v) u := by
    calc
      (∑ t ∈ Finset.range (u + 1), Nat.choose u t * Nat.choose v t) =
          ∑ t ∈ Finset.range (u + 1), Nat.choose v t * Nat.choose u (u - t) := by
        apply Finset.sum_congr rfl
        intro t ht
        have htu : t ≤ u := by
          have := Finset.mem_range.mp ht
          omega
        rw [Nat.choose_symm htu, Nat.mul_comm]
      _ = Nat.choose (v + u) u := by
        simpa only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] using
          (Nat.add_choose_eq v u u).symm
      _ = Nat.choose (u + v) u := by rw [Nat.add_comm v u]
  have hz :
      (∑ t ∈ Finset.range (u + 1),
        (Nat.choose u t : ℤ) * (Nat.choose v t : ℤ)) =
        (Nat.choose (u + v) u : ℤ) := by
    simpa only [Nat.cast_sum, Nat.cast_mul] using congrArg (fun x : ℕ => (x : ℤ)) hn
  have hext :
      (∑ t ∈ Finset.range (u + 1),
        (Nat.choose u t : ℤ) * (Nat.choose v t : ℤ)) =
      ∑ t ∈ Finset.range m, (Nat.choose u t : ℤ) * (Nat.choose v t : ℤ) := by
    apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt hu))
    intro t ht hnot
    have hut : u < t := by
      have : ¬ t < u + 1 := by simpa only [Finset.mem_range] using hnot
      omega
    simp [Nat.choose_eq_zero_of_lt hut]
  exact hext.symm.trans hz

theorem pascal_gram_sum (m : ℕ) (u v : Fin m) :
    (∑ t : Fin m,
      (Nat.choose u.val t.val : ℤ) * (Nat.choose v.val t.val : ℤ)) =
      (Nat.choose (u.val + v.val) u.val : ℤ) := by
  simpa only [Finset.sum_range] using pascal_gram_range m u.val v.val u.isLt

end Hardinian.FiniteAlgebra
