import Hardinian.CentralMassLimit
import Hardinian.LogWindowRelative

open Filter
open scoped Topology

namespace Hardinian

theorem sqrt_ratio_bounds (x : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 2) :
    1 ≤ Real.sqrt x ∧ Real.sqrt x ≤ 2 ∧ Real.sqrt x - 1 ≤ x - 1 := by
  have hs1 : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx1
  have hs2 : Real.sqrt x ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩
  have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
  refine ⟨hs1, hs2, ?_⟩
  nlinarith [sq_nonneg (Real.sqrt x - 1)]

theorem centralMass_scaling_identity (N m : ℕ) (hm : 0 < m) :
    Real.sqrt (Real.pi * (N : ℝ)) * centralMass m =
      Real.sqrt (2 * (N : ℝ) / (m : ℝ)) *
        (Real.sqrt (Real.pi * (m : ℝ) / 2) * centralMass m) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  rw [← mul_assoc, ← Real.sqrt_mul (by positivity)]
  have he : (2 * (N : ℝ) / (m : ℝ)) * (Real.pi * (m : ℝ) / 2) =
      Real.pi * (N : ℝ) := by field_simp [hm0] <;> ring
  rw [he]

theorem centralMass_scaling_error (N m : ℕ) (hN : 1 ≤ N)
    (hNm : N ≤ m) (hmN : m ≤ 2 * N) :
    |Real.sqrt (Real.pi * (N : ℝ)) * centralMass m - 1| ≤
      2 * |Real.sqrt (Real.pi * (m : ℝ) / 2) * centralMass m - 1| +
        (2 * (N : ℝ) - (m : ℝ)) / (m : ℝ) := by
  have hm : 0 < m := by omega
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hNm' : (N : ℝ) ≤ m := by exact_mod_cast hNm
  have hmN' : (m : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hmN
  have hq1 : (1 : ℝ) ≤ 2 * (N : ℝ) / (m : ℝ) := (one_le_div hm0).mpr hmN'
  have hq2 : 2 * (N : ℝ) / (m : ℝ) ≤ 2 := (div_le_iff₀ hm0).mpr (by linarith)
  have hs := sqrt_ratio_bounds (2 * (N : ℝ) / (m : ℝ)) hq1 hq2
  have he : 2 * (N : ℝ) / (m : ℝ) - 1 =
      (2 * (N : ℝ) - (m : ℝ)) / (m : ℝ) := by field_simp [hm0.ne']
  have hserr := hs.2.2
  rw [he] at hserr
  rw [centralMass_scaling_identity N m hm]
  calc
    |Real.sqrt (2 * (N : ℝ) / (m : ℝ)) *
        (Real.sqrt (Real.pi * (m : ℝ) / 2) * centralMass m) - 1| =
      |Real.sqrt (2 * (N : ℝ) / (m : ℝ)) *
          (Real.sqrt (Real.pi * (m : ℝ) / 2) * centralMass m - 1) +
        (Real.sqrt (2 * (N : ℝ) / (m : ℝ)) - 1)| := by congr 1 <;> ring
    _ ≤ |Real.sqrt (2 * (N : ℝ) / (m : ℝ)) *
          (Real.sqrt (Real.pi * (m : ℝ) / 2) * centralMass m - 1)| +
        |Real.sqrt (2 * (N : ℝ) / (m : ℝ)) - 1| := abs_add _ _
    _ = Real.sqrt (2 * (N : ℝ) / (m : ℝ)) *
          |Real.sqrt (Real.pi * (m : ℝ) / 2) * centralMass m - 1| +
        (Real.sqrt (2 * (N : ℝ) / (m : ℝ)) - 1) := by
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (sub_nonneg.mpr hs.1)]
    _ ≤ _ := by
      have hmul := mul_le_mul_of_nonneg_right hs.2.1
        (abs_nonneg (Real.sqrt (Real.pi * (m : ℝ) / 2) * centralMass m - 1))
      linarith

theorem centralMass_offset_scaling_error (N a b : ℕ) (hN : 1 ≤ N)
    (hba : b < a) (ha : a ≤ N) (hsum : a + b ≤ N) :
    |Real.sqrt (Real.pi * (N : ℝ)) * centralMass ((N - a) + (N - b)) - 1| ≤
      2 * |Real.sqrt (Real.pi * (((N - a) + (N - b) : ℕ) : ℝ) / 2) *
          centralMass ((N - a) + (N - b)) - 1| + 2 * (a : ℝ) / (N : ℝ) := by
  have hNm : N ≤ (N - a) + (N - b) := by omega
  have hmN : (N - a) + (N - b) ≤ 2 * N := by omega
  have h := centralMass_scaling_error N ((N - a) + (N - b)) hN hNm hmN
  apply h.trans
  apply add_le_add_left
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNm' : (N : ℝ) ≤ (((N - a) + (N - b) : ℕ) : ℝ) := by exact_mod_cast hNm
  have hba' : (b : ℝ) ≤ a := by exact_mod_cast (Nat.le_of_lt hba)
  have hm : (((N - a) + (N - b) : ℕ) : ℝ) = 2 * (N : ℝ) - a - b := by
    rw [Nat.cast_add, Nat.cast_sub ha, Nat.cast_sub (by omega : b ≤ N)]
    ring
  calc
    (2 * (N : ℝ) - (((N - a) + (N - b) : ℕ) : ℝ)) /
        (((N - a) + (N - b) : ℕ) : ℝ) =
      ((a : ℝ) + b) / (((N - a) + (N - b) : ℕ) : ℝ) := by congr 1 <;> linarith
    _ ≤ ((a : ℝ) + b) / (N : ℝ) := div_le_div_of_nonneg_left (by positivity) hN0 hNm'
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _)

theorem uniform_centralMass_logWindow (C ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N ≥ N0, ∀ a b : ℕ,
      b < a → a ≤ N → (a : ℝ) ≤ C * Real.log (N : ℝ) →
      |Real.sqrt (Real.pi * (N : ℝ)) * centralMass ((N - a) + (N - b)) - 1| < ε := by
  obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.mp centralMass_tendsto) (ε / 4) (by linarith)
  obtain ⟨J, hJ2, hJ⟩ := logWindow_eventually_below_half C
  have hrate : Tendsto (fun N : ℕ => (2 * C) * (Real.log (N : ℝ) / (N : ℝ)))
      atTop (𝓝 0) := by
    simpa only [pow_one, mul_zero] using (log_nat_pow_div_tendsto 1).const_mul (2 * C)
  obtain ⟨K, hK⟩ := eventually_atTop.mp ((tendsto_order.mp hrate).2 (ε / 2) (by linarith))
  refine ⟨max J (max M K), le_trans hJ2 (le_max_left _ _), ?_⟩
  intro N hN a b hba ha hlog
  have hJN : J ≤ N := le_trans (le_max_left _ _) hN
  have hMKN : max M K ≤ N := le_trans (le_max_right _ _) hN
  have hMN : M ≤ N := le_trans (le_max_left _ _) hMKN
  have hKN : K ≤ N := le_trans (le_max_right _ _) hMKN
  have hN2 : 2 ≤ N := le_trans hJ2 hJN
  have hhalf := hJ N hJN
  have hba' : (b : ℝ) ≤ a := by exact_mod_cast (Nat.le_of_lt hba)
  have hsum' : (a : ℝ) + b ≤ N := by linarith
  have hsum : a + b ≤ N := by exact_mod_cast hsum'
  have hmM : M ≤ (N - a) + (N - b) := by omega
  have hc : |Real.sqrt (Real.pi * (((N - a) + (N - b) : ℕ) : ℝ) / 2) *
      centralMass ((N - a) + (N - b)) - 1| < ε / 4 := by
    simpa only [Real.dist_eq] using hM ((N - a) + (N - b)) hmM
  have hr : 2 * (C * Real.log (N : ℝ)) / (N : ℝ) < ε / 2 := by
    convert hK N hKN using 1 <;> ring
  have haerr : 2 * (a : ℝ) / (N : ℝ) ≤
      2 * (C * Real.log (N : ℝ)) / (N : ℝ) :=
    div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  have h := centralMass_offset_scaling_error N a b (by omega) hba ha hsum
  linarith

end Hardinian
