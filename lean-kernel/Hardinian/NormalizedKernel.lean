import Hardinian.UniformCentralScaling

namespace Hardinian

theorem binomialKernel_nonneg (u v : ℕ) : 0 ≤ binomialKernel u v := by
  unfold binomialKernel
  apply Finset.sum_nonneg
  intro j hj
  unfold binomialMass
  positivity

theorem mul_unit_interval_error (A B : ℝ) (hB0 : 0 ≤ B) (hB1 : B ≤ 1) :
    |A * B - 1| ≤ |A - 1| + |B - 1| := by
  calc
    |A * B - 1| = |(A - 1) * B + (B - 1)| := by congr 1 <;> ring
    _ ≤ |(A - 1) * B| + |B - 1| := abs_add _ _
    _ = |A - 1| * B + |B - 1| := by rw [abs_mul, abs_of_nonneg hB0]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hB1 (abs_nonneg (A - 1))
      linarith

theorem uniform_binomialKernel_logWindow (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N ≥ N0, ∀ a b : ℕ,
      b < a → a ≤ N → (a : ℝ) ≤ C * Real.log (N : ℝ) →
      |Real.sqrt (Real.pi * (N : ℝ)) * binomialKernel (N - a) (N - b) /
          ((a : ℝ) - b) - 1| < ε := by
  obtain ⟨M, hM2, hM⟩ := uniform_centralMass_logWindow C (ε / 2) (by linarith)
  obtain ⟨K, hK2, hK⟩ := uniform_kernel_relative_logWindow C (ε / 2) hC (by linarith)
  refine ⟨max M K, le_trans hM2 (le_max_left _ _), ?_⟩
  intro N hN a b hba ha hlog
  have hMN : M ≤ N := le_trans (le_max_left _ _) hN
  have hKN : K ≤ N := le_trans (le_max_right _ _) hN
  let A : ℝ := Real.sqrt (Real.pi * (N : ℝ)) * centralMass ((N - a) + (N - b))
  let B : ℝ := binomialKernel (N - a) (N - b) /
    (((a : ℝ) - b) * centralMass ((N - a) + (N - b)))
  have hA : |A - 1| < ε / 2 := hM N hMN a b hba ha hlog
  have hB : |B - 1| < ε / 2 := hK N hKN a b hba ha hlog
  have hba' : (b : ℝ) < a := by exact_mod_cast hba
  have hd : (0 : ℝ) < (a : ℝ) - b := by linarith
  have hc := centralMass_pos ((N - a) + (N - b))
  have hB0 : 0 ≤ B := div_nonneg (binomialKernel_nonneg _ _) (mul_nonneg hd.le hc.le)
  have hwidth : (N - b) - (N - a) = a - b := by omega
  have herr := binomialKernel_relative_error (N - a) (N - b) (by omega)
  rw [hwidth, Nat.cast_sub (Nat.le_of_lt hba)] at herr
  have hB1 : B ≤ 1 := by dsimp [B]; linarith [herr.1]
  have hf : Real.sqrt (Real.pi * (N : ℝ)) * binomialKernel (N - a) (N - b) /
      ((a : ℝ) - b) = A * B := by
    dsimp [A, B]
    field_simp [hd.ne', hc.ne'] <;> ring
  rw [hf]
  exact lt_of_le_of_lt (mul_unit_interval_error A B hB0 hB1) (by linarith)

end Hardinian
