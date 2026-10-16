import HardinianHandoff.Definitions

/-! # A 线：半整数格点偶次幂和（TASKS.md 目标 1–5）

`moment h d = Σ_{j<d} (j - d/2)^{2h}` 与 Bernoulli 多项式
`P_h = [B_{2h+1}(X/2) - B_{2h+1}(-X/2)]/(2h+1)` 的一致性、奇性、精确次数、
最高次系数与 h=0 特例。 -/

open scoped BigOperators

noncomputable section
namespace HardinianHandoff

/-! ## 小工具 -/

private theorem natDegree_sum_le' {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℚ)
    (n : ℕ) (h : ∀ i ∈ s, (f i).natDegree ≤ n) : (∑ i ∈ s, f i).natDegree ≤ n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact le_trans (Polynomial.natDegree_add_le _ _)
      (max_le (h a (Finset.mem_insert_self a s))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

private theorem neg_pow_two_mul_add_one (a : ℚ) (h : ℕ) :
    (-(a : ℚ)) ^ (2 * h + 1) = -(a ^ (2 * h + 1)) := by
  induction h with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by omega]
    rw [pow_add (-(a : ℚ)) (2 * k + 1) 2, pow_add a (2 * k + 1) 2, ih, pow_two]
    ring

private theorem comp_C_mul_X (a : ℚ) (r : Polynomial ℚ) :
    (Polynomial.C a * Polynomial.X).comp r = Polynomial.C a * r := by
  simp [Polynomial.comp]

private theorem sum_range_telescope (f : ℕ → ℚ) (d : ℕ) :
    ∑ j ∈ Finset.range d, (f (j + 1) - f j) = f d - f 0 := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-! ## Bernoulli 多项式的次数结构（由固定库的有限和定义直接推出） -/

theorem bernoulli_coeff_top (n : ℕ) : (Polynomial.bernoulli n).coeff n = 1 := by
  rw [Polynomial.bernoulli, Polynomial.finset_sum_coeff,
    Finset.sum_eq_single_of_mem 0 (by simp)
      (fun b hb_mem hb => by
        have hb1 : b < n + 1 := Finset.mem_range.mp hb_mem
        rw [Polynomial.coeff_monomial, if_neg (fun hcon => hb (by omega))])]
  simp

theorem bernoulli_natDegree_le (n : ℕ) : (Polynomial.bernoulli n).natDegree ≤ n := by
  rw [Polynomial.bernoulli]
  refine natDegree_sum_le' _ _ n fun i _ => ?_
  rcases eq_or_ne (_root_.bernoulli i * n.choose i) 0 with h | h
  · rw [h, map_zero]
    exact Nat.zero_le n
  · rw [Polynomial.natDegree_monomial, if_neg h]
    exact Nat.sub_le n i

theorem bernoulli_natDegree (n : ℕ) : (Polynomial.bernoulli n).natDegree = n :=
  Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (bernoulli_natDegree_le n)
    (by rw [bernoulli_coeff_top]; exact one_ne_zero)

/-! ## 目标 4：最高次系数 -/

theorem momentPolynomial_top_coeff (h : ℕ) :
    (momentPolynomial h).coeff (2 * h + 1) =
      1 / (((4 : ℚ) ^ h * ((2 * h + 1 : ℕ) : ℚ))) := by
  have hn : ((2 * h + 1 : ℕ) : ℚ) ≠ 0 := by norm_cast
  have h4 : ((4 : ℚ) ^ h) ≠ 0 := pow_ne_zero _ four_ne_zero
  rw [momentPolynomial, Polynomial.coeff_C_mul, Polynomial.coeff_sub,
    Polynomial.comp_C_mul_X_coeff, Polynomial.comp_C_mul_X_coeff,
    bernoulli_coeff_top, one_mul, one_mul, neg_pow_two_mul_add_one]
  have hpow : ((1 : ℚ) / 2) ^ (2 * h + 1) = 1 / (((2 : ℚ)) * ((4 : ℚ) ^ h)) := by
    have h24 : ((2 : ℚ)) * ((4 : ℚ) ^ h) = ((2 : ℚ)) ^ (2 * h + 1) := by
      rw [show (4 : ℚ) = ((2 : ℚ)) ^ 2 from by norm_num, ← pow_mul, pow_succ]
      ring
    rw [h24, one_div, one_div, inv_pow]
  rw [hpow, sub_neg_eq_add]
  field_simp
  ring

/-! ## 目标 3：精确次数 -/

theorem momentPolynomial_natDegree (h : ℕ) :
    (momentPolynomial h).natDegree = 2 * h + 1 := by
  refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
  · have hcx1 : (Polynomial.C ((1 : ℚ) / 2) * Polynomial.X).natDegree = 1 := by
      have hge : 1 ≤ (Polynomial.C ((1 : ℚ) / 2) * Polynomial.X).natDegree :=
        Polynomial.le_natDegree_of_ne_zero (by
          rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_one]; norm_num)
      have hle := Polynomial.natDegree_mul_le (p := Polynomial.C ((1 : ℚ) / 2))
        (q := Polynomial.X)
      rw [Polynomial.natDegree_C, Polynomial.natDegree_X] at hle
      omega
    have hcx2 : (Polynomial.C (-(1 / 2 : ℚ)) * Polynomial.X).natDegree = 1 := by
      have hge : 1 ≤ (Polynomial.C (-(1 / 2 : ℚ)) * Polynomial.X).natDegree :=
        Polynomial.le_natDegree_of_ne_zero (by
          rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_one]; norm_num)
      have hle := Polynomial.natDegree_mul_le (p := Polynomial.C (-(1 / 2 : ℚ)))
        (q := Polynomial.X)
      rw [Polynomial.natDegree_C, Polynomial.natDegree_X] at hle
      omega
    have hc1 : ((Polynomial.bernoulli (2 * h + 1)).comp
        (Polynomial.C ((1 : ℚ) / 2) * Polynomial.X)).natDegree ≤ 2 * h + 1 := by
      have hk := Polynomial.natDegree_comp_le (p := Polynomial.bernoulli (2 * h + 1))
        (q := Polynomial.C ((1 : ℚ) / 2) * Polynomial.X)
      rw [bernoulli_natDegree, hcx1, Nat.mul_one] at hk
      exact hk
    have hc2 : ((Polynomial.bernoulli (2 * h + 1)).comp
        (Polynomial.C (-(1 / 2 : ℚ)) * Polynomial.X)).natDegree ≤ 2 * h + 1 := by
      have hk := Polynomial.natDegree_comp_le (p := Polynomial.bernoulli (2 * h + 1))
        (q := Polynomial.C (-(1 / 2 : ℚ)) * Polynomial.X)
      rw [bernoulli_natDegree, hcx2, Nat.mul_one] at hk
      exact hk
    have hsub : ((Polynomial.bernoulli (2 * h + 1)).comp
          (Polynomial.C ((1 : ℚ) / 2) * Polynomial.X) -
        (Polynomial.bernoulli (2 * h + 1)).comp
          (Polynomial.C (-(1 / 2 : ℚ)) * Polynomial.X)).natDegree ≤ 2 * h + 1 :=
      le_trans (Polynomial.natDegree_sub_le _ _) (Nat.max_le.mpr ⟨hc1, hc2⟩)
    have hc0 : (Polynomial.C (((2 * h + 1 : ℕ) : ℚ)⁻¹)).natDegree = 0 := by simp
    rw [momentPolynomial]
    exact le_trans Polynomial.natDegree_mul_le (by omega)
  · rw [momentPolynomial_top_coeff]
    exact one_div_ne_zero (mul_ne_zero (pow_ne_zero _ four_ne_zero)
      (by norm_cast))

/-! ## 目标 1：幂和恒等式（bernoulli_eval_one_add 望远镜） -/

theorem moment_eq_eval (h d : ℕ) : moment h d = (momentPolynomial h).eval (d : ℚ) := by
  have hn : ((2 * h + 1 : ℕ) : ℚ) ≠ 0 := by norm_cast
  have key : ∀ j : ℕ, ((2 * h + 1 : ℕ) : ℚ) * ((j : ℚ) - (d : ℚ) / 2) ^ (2 * h) =
      (Polynomial.bernoulli (2 * h + 1)).eval (((j + 1 : ℕ) : ℚ) - (d : ℚ) / 2) -
      (Polynomial.bernoulli (2 * h + 1)).eval (((j : ℕ) : ℚ) - (d : ℚ) / 2) := by
    intro j
    rw [show ((j + 1 : ℕ) : ℚ) - (d : ℚ) / 2 = 1 + ((j : ℚ) - (d : ℚ) / 2) from by
        push_cast; ring,
      Polynomial.bernoulli_eval_one_add,
      show (2 * h + 1 : ℕ) - 1 = 2 * h from by omega]
    ring
  have hL : ((2 * h + 1 : ℕ) : ℚ) * moment h d =
      (Polynomial.bernoulli (2 * h + 1)).eval (((d : ℚ)) / 2) -
      (Polynomial.bernoulli (2 * h + 1)).eval (-((d : ℚ) / 2)) := by
    rw [moment, Finset.mul_sum,
      Finset.sum_congr rfl fun j _ => key j,
      sum_range_telescope (fun j =>
        (Polynomial.bernoulli (2 * h + 1)).eval (((j : ℕ) : ℚ) - (d : ℚ) / 2)) d,
      show ((d : ℕ) : ℚ) - (d : ℚ) / 2 = (d : ℚ) / 2 from by push_cast; ring,
      Nat.cast_zero, zero_sub]
  have hR : ((2 * h + 1 : ℕ) : ℚ) * (momentPolynomial h).eval (d : ℚ) =
      (Polynomial.bernoulli (2 * h + 1)).eval (((d : ℚ)) / 2) -
      (Polynomial.bernoulli (2 * h + 1)).eval (-((d : ℚ) / 2)) := by
    rw [momentPolynomial]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
      Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_X]
    rw [show ((1 : ℚ) / 2) * (d : ℚ) = (d : ℚ) / 2 from by ring,
      show (-(1 / 2 : ℚ)) * (d : ℚ) = -((d : ℚ) / 2) from by ring,
      ← mul_assoc, mul_inv_cancel₀ hn, one_mul]
  exact (mul_right_inj' hn).mp (hL.trans hR.symm)

/-! ## 目标 2：奇性（复合表达式自身的反对称） -/

theorem momentPolynomial_odd (h : ℕ) :
    (momentPolynomial h).comp (-Polynomial.X) = -momentPolynomial h := by
  rw [momentPolynomial]
  rw [show ∀ (p q : Polynomial ℚ) (c : ℚ), (Polynomial.C c * (p - q)).comp (-Polynomial.X)
      = Polynomial.C c * (p.comp (-Polynomial.X) - q.comp (-Polynomial.X)) from
      fun p q c => by simp [Polynomial.comp]]
  rw [Polynomial.comp_assoc, Polynomial.comp_assoc, comp_C_mul_X, comp_C_mul_X,
    mul_neg, mul_neg]
  rw [show -(Polynomial.C (-(1 / 2 : ℚ)) * Polynomial.X) =
        Polynomial.C ((1 : ℚ) / 2) * Polynomial.X from by
      rw [← neg_mul, Polynomial.C_neg, neg_neg],
    show -(Polynomial.C ((1 : ℚ) / 2) * Polynomial.X) =
        Polynomial.C (-(1 / 2 : ℚ)) * Polynomial.X from by
      rw [← neg_mul, Polynomial.C_neg]]
  ring

/-! ## 目标 5：h=0 特例 P_0 = X -/

theorem momentPolynomial_zero : momentPolynomial 0 = Polynomial.X := by
  have hb1 : Polynomial.bernoulli 1 = Polynomial.X - Polynomial.C ((1 : ℚ) / 2) := by
    rw [Polynomial.bernoulli, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [_root_.bernoulli_zero, _root_.bernoulli_one, Nat.choose_zero_right,
      Nat.choose_one_right, mul_one, one_mul, Nat.cast_one, Nat.sub_zero, Nat.sub_self]
    rw [show ((-1 : ℚ) / 2) = -((1 : ℚ) / 2) from by norm_num]
    rw [Polynomial.monomial_one_one_eq_X, Polynomial.monomial_zero_left,
      Polynomial.C_neg, sub_eq_add_neg]
  rw [momentPolynomial, show (2 * 0 + 1 : ℕ) = 1 from by norm_num,
    hb1, Nat.cast_one, inv_one, Polynomial.C_1, one_mul]
  simp only [Polynomial.comp, Polynomial.eval₂_sub, map_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_X]
  have hab : ∀ (u v : Polynomial ℚ),
      (u - Polynomial.C ((1 : ℚ) / 2)) - (v - Polynomial.C ((1 : ℚ) / 2)) = u - v := by
    intro u v; abel
  rw [hab, ← sub_mul, ← Polynomial.C_sub]
  have h12 : ((1 : ℚ) / 2) - (-(1 / 2 : ℚ)) = 1 := by norm_num
  rw [h12, Polynomial.C_1, one_mul]

end HardinianHandoff
