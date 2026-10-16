import HardinianHandoff.AlternatingVandermonde

/-! # D 线：低次数消失与临界项（TASKS.md 目标 17–21）

固定库没有 `totalDegree_mul` 的等式版本，这里先用齐次分量补出
"齐次因子乘非零多项式的次数下界"，再推出 17/18 的消失与唯一标量倍。
K_r 的平衡恒等式按奇偶分情况直接计算。 -/

open scoped BigOperators

noncomputable section
namespace HardinianHandoff

variable {r : ℕ}

/-! ## 齐次分量工具 -/

/-- 非零多项式的最高齐次分量非零。 -/
private theorem hc_top_ne_zero {q : AltPoly r} (hq0 : q ≠ 0) :
    MvPolynomial.homogeneousComponent q.totalDegree q ≠ 0 := by
  intro h0
  have hfull := MvPolynomial.sum_homogeneousComponent (φ := q)
  rw [Finset.sum_range_succ] at hfull
  rw [h0, add_zero] at hfull
  -- hfull : ∑ i ∈ range (td q), hc i q = q
  rcases Nat.eq_zero_or_pos q.totalDegree with htd0 | htdpos
  · rw [htd0, Finset.range_zero, Finset.sum_empty] at hfull
    exact hq0 hfull.symm
  · have hle : (∑ i ∈ Finset.range q.totalDegree,
        MvPolynomial.homogeneousComponent i q).totalDegree ≤ q.totalDegree - 1 := by
      refine MvPolynomial.totalDegree_finsetSum_le fun i hi => ?_
      by_cases h : MvPolynomial.homogeneousComponent i q = 0
      · rw [h, MvPolynomial.totalDegree_zero]
        omega
      · rw [(MvPolynomial.IsHomogeneous.totalDegree
          (MvPolynomial.homogeneousComponent_isHomogeneous i q) h)]
        have himem : i < q.totalDegree := Finset.mem_range.mp hi
        omega
    have hqtd : q.totalDegree
        = (∑ i ∈ Finset.range q.totalDegree,
            MvPolynomial.homogeneousComponent i q).totalDegree :=
      congrArg MvPolynomial.totalDegree hfull.symm
    omega

/-- 齐次因子乘积的齐次分量分解。 -/
private theorem hc_mul_of_hom {φ : AltPoly r} {m : ℕ}
    (hφ : MvPolynomial.IsHomogeneous φ m) (q : AltPoly r) (k : ℕ) :
    MvPolynomial.homogeneousComponent (m + k) (φ * q)
      = φ * MvPolynomial.homogeneousComponent k q := by
  calc MvPolynomial.homogeneousComponent (m + k) (φ * q)
      = MvPolynomial.homogeneousComponent (m + k)
          (φ * ∑ i ∈ Finset.range (q.totalDegree + 1),
            MvPolynomial.homogeneousComponent i q) := by
        rw [MvPolynomial.sum_homogeneousComponent]
    _ = ∑ i ∈ Finset.range (q.totalDegree + 1),
          MvPolynomial.homogeneousComponent (m + k)
            (φ * MvPolynomial.homogeneousComponent i q) := by
        rw [Finset.mul_sum]
        have hmap : (MvPolynomial.homogeneousComponent (m + k) :
              AltPoly r →ₗ[ℚ] AltPoly r)
            (∑ i ∈ Finset.range (q.totalDegree + 1),
              φ * MvPolynomial.homogeneousComponent i q)
            = ∑ i ∈ Finset.range (q.totalDegree + 1),
              MvPolynomial.homogeneousComponent (m + k)
                (φ * MvPolynomial.homogeneousComponent i q) :=
          map_sum _ _ _
        rw [hmap]
    _ = φ * MvPolynomial.homogeneousComponent k q := by
        refine (Finset.sum_eq_single k ?_ ?_).trans ?_
        · intro i hi hik
          rw [MvPolynomial.homogeneousComponent_of_mem
            (MvPolynomial.IsHomogeneous.mul hφ
              (MvPolynomial.homogeneousComponent_isHomogeneous i q))]
          rw [if_neg (fun hcon => hik (by omega))]
        · intro hk
          have hlt : q.totalDegree < k := by
            rw [Finset.mem_range] at hk
            omega
          have hh : φ * MvPolynomial.homogeneousComponent k q = 0 := by
            rw [MvPolynomial.homogeneousComponent_eq_zero _ q hlt]
            simp
          rw [MvPolynomial.homogeneousComponent_of_mem
            (MvPolynomial.IsHomogeneous.mul hφ
              (MvPolynomial.homogeneousComponent_isHomogeneous k q))]
          rw [if_pos rfl, hh]
        · rw [MvPolynomial.homogeneousComponent_of_mem
            (MvPolynomial.IsHomogeneous.mul hφ
              (MvPolynomial.homogeneousComponent_isHomogeneous k q))]
          rw [if_pos rfl]

/-- 齐次因子乘非零多项式：总次数下界（配固定库的 `≤` 上界即等式）。 -/
private theorem totalDegree_mul_ge {φ : AltPoly r} {m : ℕ}
    (hφ : MvPolynomial.IsHomogeneous φ m) (hφ0 : φ ≠ 0) {q : AltPoly r}
    (hq0 : q ≠ 0) : m + q.totalDegree ≤ (φ * q).totalDegree := by
  by_contra hcon
  have hlt : (φ * q).totalDegree < m + q.totalDegree := by omega
  have h1 : MvPolynomial.homogeneousComponent (m + q.totalDegree) (φ * q) = 0 :=
    MvPolynomial.homogeneousComponent_eq_zero _ (φ * q) hlt
  rw [hc_mul_of_hom hφ] at h1
  exact (mul_ne_zero hφ0 (hc_top_ne_zero hq0)) h1

/-! ## 目标 17：低次交错多项式为零 -/

theorem alternating_zero_of_degree_lt (r : ℕ) (p : AltPoly r) (hp : IsAlternating p)
    (hdeg : p.totalDegree < Nat.choose r 2) : p = 0 := by
  by_contra h0
  obtain ⟨q, hq⟩ := vandermonde_dvd r p hp
  have hq0 : q ≠ 0 := fun hq0 => h0 (by rw [hq, hq0, mul_zero])
  have hge : Nat.choose r 2 + q.totalDegree
      ≤ (vandermonde r * q).totalDegree :=
    totalDegree_mul_ge (vandermonde_isHomogeneous r) (vandermonde_ne_zero r) hq0
  rw [hq] at hdeg
  omega

/-! ## 目标 18：临界次数恰为唯一标量倍 -/

theorem alternating_scalar_of_degree_le (r : ℕ) (p : AltPoly r) (hp : IsAlternating p)
    (hdeg : p.totalDegree ≤ Nat.choose r 2) :
    ∃! c : ℚ, p = MvPolynomial.C c * vandermonde r := by
  obtain ⟨q, hq⟩ := vandermonde_dvd r p hp
  have hex : p = MvPolynomial.C (MvPolynomial.coeff 0 q) * vandermonde r := by
    by_cases h0 : q = 0
    · rw [hq, h0, mul_zero]
      simp
    · have hge : Nat.choose r 2 + q.totalDegree
          ≤ (vandermonde r * q).totalDegree :=
        totalDegree_mul_ge (vandermonde_isHomogeneous r) (vandermonde_ne_zero r) h0
      have hle : (vandermonde r * q).totalDegree ≤ Nat.choose r 2 := by
        rw [← hq]
        exact hdeg
      have htdq : q.totalDegree = 0 := by omega
      rw [← MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp htdq, hq, mul_comm]
  refine ⟨MvPolynomial.coeff 0 q, hex, ?_⟩
  intro c' hc'
  have hcc : MvPolynomial.C c' * vandermonde r
      = MvPolynomial.C (MvPolynomial.coeff 0 q) * vandermonde r := by
    rw [← hc', ← hex]
  exact (MvPolynomial.C_inj ℚ c' (MvPolynomial.coeff 0 q)).mp
    (mul_right_cancel₀ (vandermonde_ne_zero r) hcc)

/-! ## 目标 19：K_r 平衡恒等式（含 r = 0/1） -/

/-! 奇偶两种情况的平衡计算（先整除化简，再消除截断减法）。 -/

private theorem even_case (k : ℕ) :
    2 * k / 2 + 2 * ((2 * k * (2 * k - 1) / 2 - 2 * k / 2) / 2)
      = 2 * k * (2 * k - 1) / 2 := by
  have hA : 2 * k * (2 * k - 1) / 2 = k * (2 * k - 1) := by
    have hcalc : 2 * k * (2 * k - 1) = 2 * (k * (2 * k - 1)) := by ring
    rw [hcalc]
    exact Nat.mul_div_cancel_left _ two_pos
  have hB : 2 * k / 2 = k := Nat.mul_div_cancel_left _ two_pos
  rw [hA, hB]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · norm_num
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have e2 : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
    rw [e2]
    have e : (j + 1) * (2 * j + 1) - (j + 1) = 2 * ((j + 1) * j) := by
      have hcalc : (j + 1) * (2 * j + 1) = 2 * ((j + 1) * j) + (j + 1) := by ring
      omega
    rw [e, Nat.mul_div_cancel_left _ two_pos]
    ring

private theorem odd_case (k : ℕ) :
    (2 * k + 1) / 2
      + 2 * (((2 * k + 1) * (2 * k + 1 - 1) / 2 - (2 * k + 1) / 2) / 2)
      = (2 * k + 1) * (2 * k + 1 - 1) / 2 := by
  have e1 : 2 * k + 1 - 1 = 2 * k := by omega
  rw [e1]
  have hA : (2 * k + 1) * (2 * k) / 2 = k * (2 * k + 1) := by
    have hcalc : (2 * k + 1) * (2 * k) = 2 * (k * (2 * k + 1)) := by ring
    rw [hcalc]
    exact Nat.mul_div_cancel_left _ two_pos
  have hB : (2 * k + 1) / 2 = k := by omega
  rw [hA, hB]
  have e : k * (2 * k + 1) - k = 2 * (k * k) := by
    have hcalc : k * (2 * k + 1) = 2 * (k * k) + k := by ring
    omega
  rw [e, Nat.mul_div_cancel_left _ two_pos]
  ring

theorem criticalOrder_balance (r : ℕ) :
    r / 2 + 2 * criticalOrder r = Nat.choose r 2 := by
  rw [criticalOrder, Nat.choose_two_right]
  rcases Nat.even_or_odd r with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst hk
    rw [show k + k = 2 * k from by omega]
    exact even_case k
  · subst hk
    exact odd_case k

/-! ## 目标 20：临界阶以下的系数全为零 -/

theorem coefficient_below_critical (r : ℕ) (F : ℕ → AltPoly r)
    (hAlt : ∀ k, IsAlternating (F k))
    (hdeg : ∀ k, (F k).totalDegree ≤ r / 2 + 2 * k)
    (k : ℕ) (hk : k < criticalOrder r) : F k = 0 :=
  alternating_zero_of_degree_lt r (F k) (hAlt k) (by
    have h1 := hdeg k
    have h2 := criticalOrder_balance r
    omega)

/-! ## 目标 21：临界项是唯一标量倍 -/

theorem coefficient_at_critical (r : ℕ) (F : ℕ → AltPoly r)
    (hAlt : ∀ k, IsAlternating (F k))
    (hdeg : ∀ k, (F k).totalDegree ≤ r / 2 + 2 * k) :
    ∃! c : ℚ, F (criticalOrder r) = MvPolynomial.C c * vandermonde r :=
  alternating_scalar_of_degree_le r (F (criticalOrder r)) (hAlt _)
    (by
      have h1 := hdeg (criticalOrder r)
      have h2 := criticalOrder_balance r
      omega)

end HardinianHandoff
