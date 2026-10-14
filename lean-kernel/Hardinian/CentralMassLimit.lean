import Hardinian.CentralMassWallis

open Filter
open scoped Topology

namespace Hardinian

theorem odd_central_factor_tendsto :
    Tendsto (fun n : ℕ => (2 * (n : ℝ) + 1) / (2 * n + 2)) atTop (𝓝 1) := by
  have hd : Tendsto (fun n : ℕ => 2 * (n : ℝ) + 2) atTop atTop := by
    exact Tendsto.atTop_add
      (tendsto_natCast_atTop_atTop.const_mul_atTop (show (0 : ℝ) < 2 by norm_num))
      tendsto_const_nhds
  have hz : Tendsto (fun n : ℕ => (1 : ℝ) / (2 * n + 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hd
  have h : Tendsto (fun n : ℕ => (1 : ℝ) - 1 / (2 * n + 2)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hz
  apply h.congr'
  exact Filter.Eventually.of_forall fun n => by
    have hd' : 2 * (n : ℝ) + 2 ≠ 0 := by positivity
    field_simp [hd'] <;> ring

theorem centralMass_even_square_tendsto :
    Tendsto (fun n : ℕ => Real.pi * (n : ℝ) * centralMass (2 * n) ^ 2)
      atTop (𝓝 1) := by
  have hp : Real.pi / 2 ≠ 0 := ne_of_gt Real.pi_div_two_pos
  have h : Tendsto (fun n : ℕ =>
      (Real.pi * ((n : ℝ) / (2 * n + 1))) / Real.Wallis.W n)
      atTop (𝓝 (Real.pi * (1 / 2) / (Real.pi / 2))) :=
    (tendsto_const_nhds.mul Stirling.tendsto_self_div_two_mul_self_add_one).div
      Real.Wallis.tendsto_W_nhds_pi_div_two hp
  have he : Real.pi * (1 / 2) / (Real.pi / 2) = (1 : ℝ) := by
    field_simp [Real.pi_ne_zero]
  simpa only [← centralMass_even_square, he] using h

theorem centralMass_odd_square_tendsto :
    Tendsto (fun n : ℕ => Real.pi * (2 * (n : ℝ) + 1) / 2 *
      centralMass (2 * n + 1) ^ 2) atTop (𝓝 1) := by
  have hp : Real.pi / 2 ≠ 0 := ne_of_gt Real.pi_div_two_pos
  have h : Tendsto (fun n : ℕ =>
      ((Real.pi / 2) * ((2 * (n : ℝ) + 1) / (2 * n + 2)) ^ 2) / Real.Wallis.W n)
      atTop (𝓝 ((Real.pi / 2) * (1 : ℝ) ^ 2 / (Real.pi / 2))) :=
    (tendsto_const_nhds.mul (odd_central_factor_tendsto.pow 2)).div
      Real.Wallis.tendsto_W_nhds_pi_div_two hp
  have he : (Real.pi / 2) * (1 : ℝ) ^ 2 / (Real.pi / 2) = 1 := by
    simp [hp]
  simpa only [← centralMass_odd_square, he] using h

theorem tendsto_of_even_and_odd (f : ℕ → ℝ) (a : ℝ)
    (he : Tendsto (fun n => f (2 * n)) atTop (𝓝 a))
    (ho : Tendsto (fun n => f (2 * n + 1)) atTop (𝓝 a)) :
    Tendsto f atTop (𝓝 a) := by
  apply Filter.tendsto_def.2
  intro s hs
  obtain ⟨ne, hne⟩ := eventually_atTop.1 (he.eventually_mem hs)
  obtain ⟨no, hno⟩ := eventually_atTop.1 (ho.eventually_mem hs)
  refine eventually_atTop.2 ⟨2 * max ne no, ?_⟩
  intro m hm
  have hneMax : ne ≤ max ne no := le_max_left _ _
  have hnoMax : no ≤ max ne no := le_max_right _ _
  have hme : ne ≤ m / 2 := by omega
  have hmo : no ≤ m / 2 := by omega
  have hcases : m = 2 * (m / 2) ∨ m = 2 * (m / 2) + 1 := by omega
  rcases hcases with h | h
  · simpa only [← h] using hne (m / 2) hme
  · simpa only [← h] using hno (m / 2) hmo

theorem centralMass_square_tendsto :
    Tendsto (fun m : ℕ => Real.pi * (m : ℝ) / 2 * centralMass m ^ 2)
      atTop (𝓝 1) := by
  apply tendsto_of_even_and_odd
  · apply centralMass_even_square_tendsto.congr'
    exact Filter.Eventually.of_forall fun n => by push_cast; ring
  · simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
      centralMass_odd_square_tendsto

theorem centralMass_tendsto :
    Tendsto (fun m : ℕ => Real.sqrt (Real.pi * (m : ℝ) / 2) * centralMass m)
      atTop (𝓝 1) := by
  have h := centralMass_square_tendsto.sqrt
  have hf : (fun m : ℕ => Real.sqrt (Real.pi * (m : ℝ) / 2 * centralMass m ^ 2)) =
      (fun m : ℕ => Real.sqrt (Real.pi * (m : ℝ) / 2) * centralMass m) := by
    funext m
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (le_of_lt (centralMass_pos m))]
  rw [hf, Real.sqrt_one] at h
  exact h

end Hardinian
