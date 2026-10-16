import Hardinian.BinomialExponentialCoefficients
import Mathlib.Algebra.GeomSum

namespace Hardinian

open Finset MvPolynomial

theorem binomialExpComposition_sum_degree (n k : ℕ) :
    (∑ v ∈ binomialPositiveCompositions n k,
      ∏ i : Fin k, binomialLogCoeff ((v i).val + 1)).totalDegree ≤ n + k := by
  classical
  apply totalDegree_finsetSum_le
  intro v hv
  have ho := (mem_filter.mp hv).2
  calc
    _ ≤ ∑ i : Fin k, (binomialLogCoeff ((v i).val + 1)).totalDegree :=
      totalDegree_finset_prod univ _
    _ ≤ ∑ i : Fin k, ((v i).val + 1 + 1) :=
      sum_le_sum (fun i _ => binomialLogCoeff_totalDegree _)
    _ = binomialCompositionOrder v + k := by
      simp [binomialCompositionOrder, sum_add_distrib]
    _ = n + k := by rw [ho]

theorem binomialExpComposition_diagonal (n : ℕ) (hn : 1 ≤ n) :
    (∑ v ∈ binomialPositiveCompositions n n,
      ∏ i : Fin n, binomialLogCoeff ((v i).val + 1)) = binomialLogCoeff 1 ^ n := by
  classical
  simp [binomialPositiveCompositions_diagonal n (by omega)]

theorem binomialExpCoeff_split_last (n : ℕ) (hn : 1 ≤ n) :
    binomialExpCoeff n =
      (∑ k ∈ range n, C ((1 : ℚ) / (k.factorial : ℚ)) *
        ∑ v ∈ binomialPositiveCompositions n k,
          ∏ i : Fin k, binomialLogCoeff ((v i).val + 1)) +
      C ((1 : ℚ) / (n.factorial : ℚ)) * binomialLogCoeff 1 ^ n := by
  classical
  unfold binomialExpCoeff
  rw [sum_range_succ, binomialExpComposition_diagonal n hn]

theorem binomialExpCoeff_lower_lengths_degree (n : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ range n, C ((1 : ℚ) / (k.factorial : ℚ)) *
      ∑ v ∈ binomialPositiveCompositions n k,
        ∏ i : Fin k, binomialLogCoeff ((v i).val + 1)).totalDegree ≤ 2 * n - 1 := by
  classical
  apply totalDegree_finsetSum_le
  intro k hk
  have hkn : k < n := mem_range.mp hk
  have hc := totalDegree_mul (C ((1 : ℚ) / (k.factorial : ℚ)))
    (∑ v ∈ binomialPositiveCompositions n k,
      ∏ i : Fin k, binomialLogCoeff ((v i).val + 1))
  rw [totalDegree_C, zero_add] at hc
  exact hc.trans ((binomialExpComposition_sum_degree n k).trans (by omega))

theorem binomialLogCoeff_one_minus_square_degree :
    (binomialLogCoeff 1 - (-((X 1 : MvPolynomial (Fin 2) ℚ) ^ 2))).totalDegree ≤ 1 := by
  have he : binomialLogCoeff 1 - (-((X 1 : MvPolynomial (Fin 2) ℚ) ^ 2)) =
      C (1 / 4 : ℚ) * X 0 - C (1 / 8 : ℚ) := by
    rw [binomialLogCoeff_one]
    ring
  rw [he]
  have hlin : (C (1 / 4 : ℚ) * (X 0 : MvPolynomial (Fin 2) ℚ)).totalDegree ≤ 1 := by
    simpa only [totalDegree_C, totalDegree_X, zero_add] using
      totalDegree_mul (C (1 / 4 : ℚ)) (X (0 : Fin 2))
  exact (binomialPoly_degree_sub _ _).trans (max_le hlin (by simp))

theorem binomialLogCoeff_one_power_remainder_degree (n : ℕ) (hn : 1 ≤ n) :
    (binomialLogCoeff 1 ^ n - (-((X 1 : MvPolynomial (Fin 2) ℚ) ^ 2)) ^ n).totalDegree ≤
      2 * n - 1 := by
  classical
  let Q : MvPolynomial (Fin 2) ℚ := -((X 1) ^ 2)
  have hP : (binomialLogCoeff 1).totalDegree ≤ 2 := by
    simpa using binomialLogCoeff_totalDegree 1
  have hQ : Q.totalDegree ≤ 2 := by
    dsimp only [Q]
    exact (binomialPoly_degree_neg _).trans (by simp)
  have hsum : (∑ i ∈ range n, binomialLogCoeff 1 ^ i * Q ^ (n - 1 - i)).totalDegree ≤
      2 * n - 2 := by
    apply totalDegree_finsetSum_le
    intro i hi
    have hin : i < n := mem_range.mp hi
    have hile : i ≤ n - 1 := by omega
    calc
      _ ≤ (binomialLogCoeff 1 ^ i).totalDegree + (Q ^ (n - 1 - i)).totalDegree :=
        totalDegree_mul _ _
      _ ≤ i * 2 + (n - 1 - i) * 2 := add_le_add
        ((totalDegree_pow _ _).trans (Nat.mul_le_mul_left i hP))
        ((totalDegree_pow _ _).trans (Nat.mul_le_mul_left (n - 1 - i) hQ))
      _ ≤ 2 * n - 2 := by omega
  change (binomialLogCoeff 1 ^ n - Q ^ n).totalDegree ≤ _
  rw [← geom_sum₂_mul (binomialLogCoeff 1) Q n]
  calc
    _ ≤ (∑ i ∈ range n, binomialLogCoeff 1 ^ i * Q ^ (n - 1 - i)).totalDegree +
        (binomialLogCoeff 1 - Q).totalDegree := totalDegree_mul _ _
    _ ≤ (2 * n - 2) + 1 := add_le_add hsum binomialLogCoeff_one_minus_square_degree
    _ ≤ 2 * n - 1 := by omega

theorem binomialNegativeSquare_power (n : ℕ) :
    (-((X 1 : MvPolynomial (Fin 2) ℚ) ^ 2)) ^ n =
      C ((-1 : ℚ) ^ n) * (X 1) ^ (2 * n) := by
  rw [neg_pow, ← pow_mul]
  simp only [map_pow, map_neg, map_one]

theorem binomialExpCoeff_top_remainder (n : ℕ) (hn : 1 ≤ n) :
    (binomialExpCoeff n - C (((-1 : ℚ) ^ n) / (n.factorial : ℚ)) *
      (X (1 : Fin 2)) ^ (2 * n)).totalDegree ≤ 2 * n - 1 := by
  classical
  have hc : (C ((1 : ℚ) / (n.factorial : ℚ)) : MvPolynomial (Fin 2) ℚ) *
      C ((-1 : ℚ) ^ n) = C (((-1 : ℚ) ^ n) / (n.factorial : ℚ)) := by
    rw [← map_mul]
    congr 1
    ring
  have he : binomialExpCoeff n - C (((-1 : ℚ) ^ n) / (n.factorial : ℚ)) *
      (X (1 : Fin 2)) ^ (2 * n) =
      (∑ k ∈ range n, C ((1 : ℚ) / (k.factorial : ℚ)) *
        ∑ v ∈ binomialPositiveCompositions n k,
          ∏ i : Fin k, binomialLogCoeff ((v i).val + 1)) +
      C ((1 : ℚ) / (n.factorial : ℚ)) *
        (binomialLogCoeff 1 ^ n - (-((X 1 : MvPolynomial (Fin 2) ℚ) ^ 2)) ^ n) := by
    rw [binomialExpCoeff_split_last n hn, binomialNegativeSquare_power, mul_sub, ← mul_assoc, hc]
    ring
  rw [he]
  have hr := totalDegree_mul (C ((1 : ℚ) / (n.factorial : ℚ)))
    (binomialLogCoeff 1 ^ n - (-((X 1 : MvPolynomial (Fin 2) ℚ) ^ 2)) ^ n)
  rw [totalDegree_C, zero_add] at hr
  exact (totalDegree_add _ _).trans
    (max_le (binomialExpCoeff_lower_lengths_degree n hn)
      (hr.trans (binomialLogCoeff_one_power_remainder_degree n hn)))

end Hardinian
