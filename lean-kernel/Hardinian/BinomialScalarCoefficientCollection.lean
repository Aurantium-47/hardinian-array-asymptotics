import Hardinian.BinomialFiniteLogReexpansion

namespace Hardinian

open Finset

noncomputable def binomialScalarLogCoeff (n : ℕ) (s t : ℝ) : ℝ :=
  let u := s / 2
  if n = 0 then 0 else
    (((1 : ℚ) / ((2 : ℚ) ^ (n + 1) * (n : ℚ)) : ℚ) : ℝ) * s ^ n
      - (∑ i ∈ range ((n + 1) / 2),
          (((Nat.choose (n - 1) (2 * i) : ℚ) /
            (((i : ℚ) + 1) * (2 * (i : ℚ) + 1)) : ℚ) : ℝ) *
          t ^ (2 * i + 2) * u ^ (n - (2 * i + 1)))
      + (∑ i ∈ range (n / 2),
          (((Nat.choose (n - 1) (2 * i + 1) : ℚ) / (2 * ((i : ℚ) + 1)) : ℚ) : ℝ) *
          t ^ (2 * i + 2) * u ^ (n - (2 * i + 2)))
      + (∑ i ∈ range n,
          ((stirlingCorrectionCoeff i * (Nat.choose (n - 1) i : ℚ) : ℚ) : ℝ) *
          ((((1 : ℚ) / (2 : ℚ) ^ (i + 1) : ℚ) : ℝ) * u ^ (n - (i + 1))
            - (u - t) ^ (n - (i + 1)) - (u + t) ^ (n - (i + 1))))

theorem binomialScalarLogCoeff_zero (s t : ℝ) : binomialScalarLogCoeff 0 s t = 0 := by
  simp [binomialScalarLogCoeff]

theorem binomialScalarLogCoeff_real (n : ℕ) (s t : ℝ) (hn : 1 ≤ n) :
    binomialScalarLogCoeff n s t =
      (1 / ((2 : ℝ) ^ (n + 1) * (n : ℝ))) * s ^ n
      - (∑ i ∈ range ((n + 1) / 2),
          (Nat.choose (n - 1) (2 * i) : ℝ) / (((i : ℝ) + 1) * (2 * (i : ℝ) + 1)) *
          t ^ (2 * i + 2) * (s / 2) ^ (n - (2 * i + 1)))
      + (∑ i ∈ range (n / 2),
          (Nat.choose (n - 1) (2 * i + 1) : ℝ) / (2 * ((i : ℝ) + 1)) *
          t ^ (2 * i + 2) * (s / 2) ^ (n - (2 * i + 2)))
      + (∑ i ∈ range n,
          (stirlingCorrectionCoeff i : ℝ) * (Nat.choose (n - 1) i : ℝ) *
          ((1 / (2 : ℝ) ^ (i + 1)) * (s / 2) ^ (n - (i + 1))
            - (s / 2 - t) ^ (n - (i + 1)) - (s / 2 + t) ^ (n - (i + 1)))) := by
  unfold binomialScalarLogCoeff
  rw [if_neg (by omega : n ≠ 0)]
  push_cast <;> rfl

theorem range_succ_sum_Icc (K : ℕ) (f : ℕ → ℝ) :
    (∑ i ∈ range K, f (i + 1)) = ∑ n ∈ Icc 1 K, f n := by
  refine sum_bij (fun i hi => i + 1) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [mem_range, mem_Icc] at hi ⊢
    omega
  · intro i hi j hj h
    omega
  · intro n hn
    simp only [mem_Icc] at hn
    refine ⟨n - 1, ?_, ?_⟩
    · simp only [mem_range]
      omega
    · omega
  · intro i hi
    rfl

theorem odd_reciprocal_triangle_sum (K : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ i ∈ range ((K + 1) / 2), ∑ l ∈ range (K - (2 * i + 1) + 1), f i l) =
      ∑ n ∈ Icc 1 K, ∑ i ∈ range ((n + 1) / 2), f i (n - (2 * i + 1)) := by
  classical
  rw [sum_sigma', sum_sigma']
  refine sum_bij (fun a ha => (⟨2 * a.1 + 1 + a.2, a.1⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [mem_sigma, mem_range, mem_Icc] at ha ⊢
    omega
  · rintro ⟨i,l⟩ ha ⟨i',l'⟩ hb h
    have hs := congrArg Sigma.fst h
    have hi := congrArg (fun z : (Σ _ : ℕ, ℕ) => z.2) h
    dsimp at hs hi
    have hl : l = l' := by omega
    subst i'
    subst l'
    rfl
  · rintro ⟨n,i⟩ hn
    simp only [mem_sigma, mem_range, mem_Icc] at hn
    refine ⟨⟨i,n - (2 * i + 1)⟩, ?_, ?_⟩
    · simp only [mem_sigma, mem_range]
      omega
    · change (⟨2 * i + 1 + (n - (2 * i + 1)), i⟩ : Σ _ : ℕ, ℕ) = ⟨n,i⟩
      rw [show 2 * i + 1 + (n - (2 * i + 1)) = n by omega]
  · intro a ha
    dsimp
    rw [Nat.add_sub_cancel_left]

theorem even_reciprocal_triangle_sum (K : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ i ∈ range (K / 2), ∑ l ∈ range (K - (2 * i + 2) + 1), f i l) =
      ∑ n ∈ Icc 1 K, ∑ i ∈ range (n / 2), f i (n - (2 * i + 2)) := by
  classical
  rw [sum_sigma', sum_sigma']
  refine sum_bij (fun a ha => (⟨2 * a.1 + 2 + a.2, a.1⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [mem_sigma, mem_range, mem_Icc] at ha ⊢
    omega
  · rintro ⟨i,l⟩ ha ⟨i',l'⟩ hb h
    have hs := congrArg Sigma.fst h
    have hi := congrArg (fun z : (Σ _ : ℕ, ℕ) => z.2) h
    dsimp at hs hi
    have hl : l = l' := by omega
    subst i'
    subst l'
    rfl
  · rintro ⟨n,i⟩ hn
    simp only [mem_sigma, mem_range, mem_Icc] at hn
    refine ⟨⟨i,n - (2 * i + 2)⟩, ?_, ?_⟩
    · simp only [mem_sigma, mem_range]
      omega
    · change (⟨2 * i + 2 + (n - (2 * i + 2)), i⟩ : Σ _ : ℕ, ℕ) = ⟨n,i⟩
      rw [show 2 * i + 2 + (n - (2 * i + 2)) = n by omega]
  · intro a ha
    dsimp
    rw [Nat.add_sub_cancel_left]

theorem successor_reciprocal_triangle_sum (K : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ i ∈ range K, ∑ l ∈ range (K - (i + 1) + 1), f i l) =
      ∑ n ∈ Icc 1 K, ∑ i ∈ range n, f i (n - (i + 1)) := by
  calc
    _ = ∑ i ∈ range K, ∑ l ∈ range (K - i), f i l := by
      apply sum_congr rfl
      intro i hi
      have hi' := mem_range.mp hi
      rw [show K - (i + 1) + 1 = K - i by omega]
    _ = ∑ p ∈ range K, ∑ i ∈ range (p + 1), f i (p - i) := stirling_triangle_sum K f
    _ = _ := by
      rw [← range_succ_sum_Icc K (fun n => ∑ i ∈ range n, f i (n - (i + 1)))]
      simp only [Nat.add_sub_add_right]

theorem choose_reciprocal_total_order (r n : ℕ) (hr : 1 ≤ r) (hrn : r ≤ n) :
    Nat.choose (r - 1 + (n - r)) (n - r) = Nat.choose (n - 1) (r - 1) := by
  rw [show r - 1 + (n - r) = n - 1 by omega]
  exact Nat.choose_symm_of_eq_add (by omega)

theorem shiftedReciprocalPrefix_neg_scale (K r : ℕ) (A z : ℝ)
    (hr : 1 ≤ r) (hA : 0 < A) :
    shiftedReciprocalPrefix K r A (-z) =
      ∑ l ∈ range (K - r + 1), (Nat.choose (r - 1 + l) l : ℝ) * z ^ l / A ^ (r + l) := by
  rw [shiftedReciprocalPrefix_scale K r A (-z) hr hA]
  apply sum_congr rfl
  intro l hl
  have hp : (-1 : ℝ) ^ l * (-z) ^ l = z ^ l := by rw [← mul_pow]; simp
  calc
    _ = (Nat.choose (r - 1 + l) l : ℝ) * ((-1 : ℝ) ^ l * (-z) ^ l) / A ^ (r + l) := by ring
    _ = _ := by rw [hp]

theorem shiftedReciprocalPrefix_double_scale (K r : ℕ) (N s : ℝ)
    (hr : 1 ≤ r) (hN : 0 < N) :
    shiftedReciprocalPrefix K r (2 * N) (-s) =
      ∑ l ∈ range (K - r + 1),
        (Nat.choose (r - 1 + l) l : ℝ) * (1 / (2 : ℝ) ^ r) *
          (s / 2) ^ l / N ^ (r + l) := by
  rw [shiftedReciprocalPrefix_neg_scale K r (2 * N) s hr (by positivity)]
  apply sum_congr rfl
  intro l hl
  rw [mul_pow, show (2 : ℝ) ^ (r + l) = 2 ^ r * 2 ^ l from pow_add _ _ _, div_pow]
  field_simp [hN.ne']
  <;> ring

theorem binomialYLog_scalar_collection (K : ℕ) (N s : ℝ) (hN : 0 < N) :
    (∑ i ∈ range K, (s / (2 * N)) ^ (i + 1) / ((i : ℝ) + 1)) / 2 =
      ∑ n ∈ Icc 1 K, ((1 / ((2 : ℝ) ^ (n + 1) * (n : ℝ))) * s ^ n) / N ^ n := by
  calc
    _ = ∑ i ∈ range K, ((s / (2 * N)) ^ (i + 1) / ((i + 1 : ℕ) : ℝ)) / 2 := by
      rw [sum_div]
      simp only [Nat.cast_add, Nat.cast_one]
    _ = ∑ n ∈ Icc 1 K, ((s / (2 * N)) ^ n / (n : ℝ)) / 2 :=
      range_succ_sum_Icc K _
    _ = _ := by
      apply sum_congr rfl
      intro n hn
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by have := (mem_Icc.mp hn).1; omega)
      rw [div_pow, mul_pow, pow_succ]
      field_simp [hN.ne', hn0]
      <;> ring

theorem binomialEntropy_scalar_collection (K : ℕ) (N s t : ℝ) (hN : 0 < N) :
    (∑ i ∈ range ((K + 1) / 2),
      ((2 : ℝ) ^ (2 * i + 1) * t ^ (2 * i + 2) /
        (((i : ℝ) + 1) * (2 * (i : ℝ) + 1))) *
      shiftedReciprocalPrefix K (2 * i + 1) (2 * N) (-s)) =
      ∑ n ∈ Icc 1 K,
        (∑ i ∈ range ((n + 1) / 2),
          (Nat.choose (n - 1) (2 * i) : ℝ) / (((i : ℝ) + 1) * (2 * (i : ℝ) + 1)) *
            t ^ (2 * i + 2) * (s / 2) ^ (n - (2 * i + 1))) / N ^ n := by
  calc
    _ = ∑ i ∈ range ((K + 1) / 2), ∑ l ∈ range (K - (2 * i + 1) + 1),
        ((Nat.choose ((2 * i + 1) - 1 + l) l : ℝ) /
          (((i : ℝ) + 1) * (2 * (i : ℝ) + 1)) * t ^ (2 * i + 2) * (s / 2) ^ l) /
          N ^ (2 * i + 1 + l) := by
      apply sum_congr rfl
      intro i hi
      have hiK : 2 * i + 1 ≤ K := by have := mem_range.mp hi; omega
      rw [shiftedReciprocalPrefix_double_scale K (2 * i + 1) N s (by omega) hN, mul_sum]
      apply sum_congr rfl
      intro l hl
      have hd1 : (i : ℝ) + 1 ≠ 0 := by positivity
      have hd2 : 2 * (i : ℝ) + 1 ≠ 0 := by positivity
      field_simp [hN.ne', hd1, hd2]
      <;> ring
    _ = ∑ n ∈ Icc 1 K, ∑ i ∈ range ((n + 1) / 2),
        ((Nat.choose ((2 * i + 1) - 1 + (n - (2 * i + 1))) (n - (2 * i + 1)) : ℝ) /
          (((i : ℝ) + 1) * (2 * (i : ℝ) + 1)) * t ^ (2 * i + 2) *
            (s / 2) ^ (n - (2 * i + 1))) / N ^ (2 * i + 1 + (n - (2 * i + 1))) :=
      odd_reciprocal_triangle_sum K _
    _ = _ := by
      apply sum_congr rfl
      intro n hn
      rw [sum_div]
      apply sum_congr rfl
      intro i hi
      have hir : 2 * i + 1 ≤ n := by have := mem_range.mp hi; omega
      rw [choose_reciprocal_total_order (2 * i + 1) n (by omega) hir,
        show 2 * i + 1 - 1 = 2 * i by omega,
        show 2 * i + 1 + (n - (2 * i + 1)) = n by omega]

theorem binomialSquareLog_scalar_collection (K : ℕ) (N s t : ℝ) (hN : 0 < N) :
    (∑ i ∈ range (K / 2),
      ((2 : ℝ) ^ (2 * i + 1) * t ^ (2 * i + 2) / ((i : ℝ) + 1)) *
      shiftedReciprocalPrefix K (2 * i + 2) (2 * N) (-s)) =
      ∑ n ∈ Icc 1 K,
        (∑ i ∈ range (n / 2),
          (Nat.choose (n - 1) (2 * i + 1) : ℝ) / (2 * ((i : ℝ) + 1)) *
            t ^ (2 * i + 2) * (s / 2) ^ (n - (2 * i + 2))) / N ^ n := by
  calc
    _ = ∑ i ∈ range (K / 2), ∑ l ∈ range (K - (2 * i + 2) + 1),
        ((Nat.choose ((2 * i + 2) - 1 + l) l : ℝ) / (2 * ((i : ℝ) + 1)) *
          t ^ (2 * i + 2) * (s / 2) ^ l) / N ^ (2 * i + 2 + l) := by
      apply sum_congr rfl
      intro i hi
      have hiK : 2 * i + 2 ≤ K := by have := mem_range.mp hi; omega
      rw [shiftedReciprocalPrefix_double_scale K (2 * i + 2) N s (by omega) hN, mul_sum]
      apply sum_congr rfl
      intro l hl
      have hd : (i : ℝ) + 1 ≠ 0 := by positivity
      rw [show (2 : ℝ) ^ (2 * i + 2) = 2 ^ (2 * i + 1) * 2 from pow_succ _ _]
      field_simp [hN.ne', hd]
      <;> ring
    _ = ∑ n ∈ Icc 1 K, ∑ i ∈ range (n / 2),
        ((Nat.choose ((2 * i + 2) - 1 + (n - (2 * i + 2))) (n - (2 * i + 2)) : ℝ) /
          (2 * ((i : ℝ) + 1)) * t ^ (2 * i + 2) * (s / 2) ^ (n - (2 * i + 2))) /
          N ^ (2 * i + 2 + (n - (2 * i + 2))) := even_reciprocal_triangle_sum K _
    _ = _ := by
      apply sum_congr rfl
      intro n hn
      rw [sum_div]
      apply sum_congr rfl
      intro i hi
      have hir : 2 * i + 2 ≤ n := by have := mem_range.mp hi; omega
      rw [choose_reciprocal_total_order (2 * i + 2) n (by omega) hir,
        show 2 * i + 2 - 1 = 2 * i + 1 by omega,
        show 2 * i + 2 + (n - (2 * i + 2)) = n by omega]

theorem binomialStirling_scalar_collection (K : ℕ) (N s t : ℝ) (hN : 0 < N) :
    (∑ i ∈ range K, (stirlingCorrectionCoeff i : ℝ) *
      (shiftedReciprocalPrefix K (i + 1) (2 * N) (-s)
        - shiftedReciprocalPrefix K (i + 1) N (t - s / 2)
        - shiftedReciprocalPrefix K (i + 1) N (-t - s / 2))) =
      ∑ n ∈ Icc 1 K,
        (∑ i ∈ range n, (stirlingCorrectionCoeff i : ℝ) * (Nat.choose (n - 1) i : ℝ) *
          ((1 / (2 : ℝ) ^ (i + 1)) * (s / 2) ^ (n - (i + 1))
            - (s / 2 - t) ^ (n - (i + 1)) - (s / 2 + t) ^ (n - (i + 1)))) / N ^ n := by
  calc
    _ = ∑ i ∈ range K, ∑ l ∈ range (K - (i + 1) + 1),
        ((stirlingCorrectionCoeff i : ℝ) * (Nat.choose ((i + 1) - 1 + l) l : ℝ) *
          ((1 / (2 : ℝ) ^ (i + 1)) * (s / 2) ^ l - (s / 2 - t) ^ l - (s / 2 + t) ^ l)) /
          N ^ (i + 1 + l) := by
      apply sum_congr rfl
      intro i hi
      have hiK : i + 1 ≤ K := by have := mem_range.mp hi; omega
      rw [shiftedReciprocalPrefix_double_scale K (i + 1) N s (by omega) hN,
        show t - s / 2 = -(s / 2 - t) by ring,
        show -t - s / 2 = -(s / 2 + t) by ring,
        shiftedReciprocalPrefix_neg_scale K (i + 1) N (s / 2 - t) (by omega) hN,
        shiftedReciprocalPrefix_neg_scale K (i + 1) N (s / 2 + t) (by omega) hN,
        ← sum_sub_distrib, ← sum_sub_distrib, mul_sum]
      apply sum_congr rfl
      intro l hl
      ring
    _ = ∑ n ∈ Icc 1 K, ∑ i ∈ range n,
        ((stirlingCorrectionCoeff i : ℝ) *
          (Nat.choose ((i + 1) - 1 + (n - (i + 1))) (n - (i + 1)) : ℝ) *
          ((1 / (2 : ℝ) ^ (i + 1)) * (s / 2) ^ (n - (i + 1))
            - (s / 2 - t) ^ (n - (i + 1)) - (s / 2 + t) ^ (n - (i + 1)))) /
          N ^ (i + 1 + (n - (i + 1))) := successor_reciprocal_triangle_sum K _
    _ = _ := by
      apply sum_congr rfl
      intro n hn
      rw [sum_div]
      apply sum_congr rfl
      intro i hi
      have hir : i + 1 ≤ n := by have := mem_range.mp hi; omega
      rw [choose_reciprocal_total_order (i + 1) n (by omega) hir,
        show i + 1 - 1 = i by omega, show i + 1 + (n - (i + 1)) = n by omega]

theorem binomialReexpandedLogApprox_eq_scalar_coeff_sum
    (N m j K : ℕ) (hN : 1 ≤ N) :
    let s : ℝ := 2 * (N : ℝ) - (m : ℝ)
    let t : ℝ := (j : ℝ) - (m : ℝ) / 2
    binomialReexpandedLogApprox N m j K =
      ∑ n ∈ Icc 1 K, binomialScalarLogCoeff n s t / (N : ℝ) ^ n := by
  let s : ℝ := 2 * (N : ℝ) - (m : ℝ)
  let t : ℝ := (j : ℝ) - (m : ℝ) / 2
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  change binomialReexpandedLogApprox N m j K =
    ∑ n ∈ Icc 1 K, binomialScalarLogCoeff n s t / (N : ℝ) ^ n
  dsimp only [binomialReexpandedLogApprox]
  rw [binomialYLog_scalar_collection K (N : ℝ) s hn,
    binomialEntropy_scalar_collection K (N : ℝ) s t hn,
    binomialSquareLog_scalar_collection K (N : ℝ) s t hn,
    binomialStirling_scalar_collection K (N : ℝ) s t hn,
    ← sum_sub_distrib, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro n hn'
  rw [binomialScalarLogCoeff_real n s t (mem_Icc.mp hn').1]
  ring

end Hardinian
