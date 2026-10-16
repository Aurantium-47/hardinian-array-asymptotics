import HardinianHandoff.HalfGridMoments

/-! # B 线：多项式组装（TASKS.md 目标 6–10）

`gridLift K c = Σ_{h≤K} c_h(X₀)·P_h(X₁)` 的求值恒等式、d→-d 奇性、
总次数上界、精确最高项与 a/b 反对称。 -/

open scoped BigOperators

noncomputable section
namespace HardinianHandoff

/-! ## 通用辅助：单变量嵌入与替换同态的交换 -/

/-- 单变量多项式沿变量 `X i` 嵌入后，再对多变量赋值 `e`。 -/
private theorem eval_eval₂_uni (p : Polynomial ℚ) (i : Fin 2) (e : Fin 2 → ℚ) :
    MvPolynomial.eval e
        (p.eval₂ (MvPolynomial.C : ℚ →+* BiPoly) (MvPolynomial.X i)) =
      p.eval (e i) := by
  have hEq : ((MvPolynomial.eval e : BiPoly →+* ℚ).comp
      (Polynomial.eval₂RingHom (MvPolynomial.C : ℚ →+* BiPoly) (MvPolynomial.X i))) =
      Polynomial.evalRingHom (e i) := by
    apply Polynomial.ringHom_ext
    · intro a; simp
    · simp
  rw [← Polynomial.coe_eval₂RingHom, ← RingHom.comp_apply, hEq]
  simp

/-- 替换同态（`reflectD` 的自变量函数）作用于单变量嵌入。 -/
private theorem subst_eval₂_uni (p : Polynomial ℚ) (i : Fin 2) :
    MvPolynomial.eval₂ (MvPolynomial.C : ℚ →+* BiPoly)
        (fun k : Fin 2 => if k = 0 then MvPolynomial.X 0 else -(MvPolynomial.X 1 : BiPoly))
        (p.eval₂ (MvPolynomial.C : ℚ →+* BiPoly) (MvPolynomial.X i)) =
      p.eval₂ (MvPolynomial.C : ℚ →+* BiPoly)
        (if i = 0 then MvPolynomial.X 0 else -(MvPolynomial.X 1 : BiPoly)) := by
  have hEq : ((MvPolynomial.eval₂Hom (MvPolynomial.C : ℚ →+* BiPoly)
        (fun k : Fin 2 => if k = 0 then MvPolynomial.X 0
          else -(MvPolynomial.X 1 : BiPoly))).comp
      (Polynomial.eval₂RingHom (MvPolynomial.C : ℚ →+* BiPoly) (MvPolynomial.X i))) =
      Polynomial.eval₂RingHom (MvPolynomial.C : ℚ →+* BiPoly)
        (if i = 0 then MvPolynomial.X 0 else -(MvPolynomial.X 1 : BiPoly)) := by
    apply Polynomial.ringHom_ext
    · intro a; simp
    · simp
  rw [← MvPolynomial.coe_eval₂Hom, ← Polynomial.coe_eval₂RingHom,
    ← RingHom.comp_apply, hEq, Polynomial.coe_eval₂RingHom]

/-- 奇多项式沿 `X ↦ -X₁` 嵌入等于沿 `X₁` 嵌入取负。 -/
private theorem eval₂_neg_X_one (p : Polynomial ℚ)
    (hp : p.comp (-Polynomial.X) = -p) :
    p.eval₂ (MvPolynomial.C : ℚ →+* BiPoly) (-(MvPolynomial.X 1 : BiPoly)) =
      -(p.eval₂ (MvPolynomial.C : ℚ →+* BiPoly) (MvPolynomial.X 1)) := by
  rw [show (-(MvPolynomial.X 1 : BiPoly)) =
        (-Polynomial.X).eval₂ (MvPolynomial.C : ℚ →+* BiPoly) (MvPolynomial.X 1) from by
      simp,
    ← Polynomial.eval₂_comp, hp, Polynomial.eval₂_neg]

private theorem eval_sum_uni {ι : Type*} (s : Finset ι) (f : ι → BiPoly)
    (e : Fin 2 → ℚ) :
    MvPolynomial.eval e (∑ i ∈ s, f i) = ∑ i ∈ s, MvPolynomial.eval e (f i) :=
  map_sum (MvPolynomial.eval e) f s

private theorem sum_neg_uni {ι : Type*} (s : Finset ι) (f : ι → BiPoly) :
    ∑ i ∈ s, -(f i) = -∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ih]
    ring

/-! ## 目标 6：真实有限双重求和 -/

theorem gridLift_eval (K : ℕ) (c : Fin (K + 1) → Polynomial ℚ) (s : ℚ) (d : ℕ) :
    evalSD (gridLift K c) s (d : ℚ) =
      ∑ j ∈ Finset.range d, ∑ h : Fin (K + 1),
        (c h).eval s * ((j : ℚ) - (d : ℚ) / 2) ^ (2 * h.val) := by
  have hstep : ∀ h : Fin (K + 1),
      MvPolynomial.eval (fun i : Fin 2 => if i = 0 then s else (d : ℚ))
        ((c h).eval₂ (MvPolynomial.C : ℚ →+* BiPoly) (MvPolynomial.X 0) *
          (momentPolynomial h.val).eval₂ (MvPolynomial.C : ℚ →+* BiPoly)
            (MvPolynomial.X 1)) =
      (c h).eval s * (momentPolynomial h.val).eval (d : ℚ) := by
    intro h
    rw [MvPolynomial.eval_mul, eval_eval₂_uni, eval_eval₂_uni]
    simp
  have hm : ∀ h : Fin (K + 1), moment h.val d =
      ∑ j ∈ Finset.range d, ((j : ℚ) - (d : ℚ) / 2) ^ (2 * h.val) := fun h => rfl
  show MvPolynomial.eval (fun i : Fin 2 => if i = 0 then s else (d : ℚ))
      (gridLift K c) = _
  rw [gridLift, eval_sum_uni]
  simp only [hstep, ← moment_eq_eval, hm, Finset.mul_sum]
  exact Finset.sum_comm

/-! ## 目标 7：d ↦ -d 的奇性 -/

theorem gridLift_odd (K : ℕ) (c : Fin (K + 1) → Polynomial ℚ) :
    reflectD (gridLift K c) = -gridLift K c := by
  have key : ∀ h : Fin (K + 1),
      MvPolynomial.eval₂ (MvPolynomial.C : ℚ →+* BiPoly)
          (fun k : Fin 2 => if k = 0 then MvPolynomial.X 0
            else -(MvPolynomial.X 1 : BiPoly))
          ((c h).eval₂ (MvPolynomial.C : ℚ →+* BiPoly) (MvPolynomial.X 0) *
            (momentPolynomial h.val).eval₂ (MvPolynomial.C : ℚ →+* BiPoly)
              (MvPolynomial.X 1)) =
        -((c h).eval₂ (MvPolynomial.C : ℚ →+* BiPoly) (MvPolynomial.X 0) *
            (momentPolynomial h.val).eval₂ (MvPolynomial.C : ℚ →+* BiPoly)
              (MvPolynomial.X 1)) := by
    intro h
    rw [MvPolynomial.eval₂_mul, subst_eval₂_uni (c h) 0,
      subst_eval₂_uni (momentPolynomial h.val) 1,
      if_pos rfl, if_neg (show ¬((1 : Fin 2) = 0) by decide),
      eval₂_neg_X_one (momentPolynomial h.val) (momentPolynomial_odd h.val), mul_neg]
  simp only [reflectD, gridLift, map_sum, MvPolynomial.coe_eval₂Hom]
  rw [Finset.sum_congr rfl fun h _ => key h, sum_neg_uni]

/-! ## 目标 8：总次数上界 -/

private theorem totalDegree_eval₂_le (p : Polynomial ℚ) (i : Fin 2) :
    (p.eval₂ (MvPolynomial.C : ℚ →+* BiPoly) (MvPolynomial.X i)).totalDegree ≤
      p.natDegree := by
  rw [Polynomial.eval₂_eq_sum_range]
  refine MvPolynomial.totalDegree_finsetSum_le fun k _ => ?_
  have hmul : ((MvPolynomial.C : ℚ →+* BiPoly) (p.coeff k) *
      (MvPolynomial.X i : BiPoly) ^ k).totalDegree ≤
      ((MvPolynomial.C : ℚ →+* BiPoly) (p.coeff k)).totalDegree +
      ((MvPolynomial.X i : BiPoly) ^ k).totalDegree :=
    MvPolynomial.totalDegree_mul _ _
  have hC : ((MvPolynomial.C : ℚ →+* BiPoly) (p.coeff k)).totalDegree = 0 :=
    MvPolynomial.totalDegree_C _
  have hpow := MvPolynomial.totalDegree_pow (MvPolynomial.X i : BiPoly) k
  rw [MvPolynomial.totalDegree_X] at hpow
  have hk : k ≤ p.natDegree := Finset.mem_range_succ_iff.mp (by assumption)
  omega

theorem gridLift_totalDegree (K : ℕ) (c : Fin (K + 1) → Polynomial ℚ)
    (hc : ∀ h, (c h).natDegree + 2 * h.val ≤ 2 * K) :
    (gridLift K c).totalDegree ≤ 2 * K + 1 := by
  rw [gridLift]
  refine MvPolynomial.totalDegree_finsetSum_le fun h _ => ?_
  have hmul : ((c h).eval₂ (MvPolynomial.C : ℚ →+* BiPoly) (MvPolynomial.X 0) *
      (momentPolynomial h.val).eval₂ (MvPolynomial.C : ℚ →+* BiPoly)
        (MvPolynomial.X 1)).totalDegree ≤
      ((c h).eval₂ (MvPolynomial.C : ℚ →+* BiPoly) (MvPolynomial.X 0)).totalDegree +
      ((momentPolynomial h.val).eval₂ (MvPolynomial.C : ℚ →+* BiPoly)
        (MvPolynomial.X 1)).totalDegree :=
    MvPolynomial.totalDegree_mul _ _
  have h1 := totalDegree_eval₂_le (c h) 0
  have h2 := totalDegree_eval₂_le (momentPolynomial h.val) 1
  rw [momentPolynomial_natDegree] at h2
  have hbound := hc h
  omega

/-! ## 目标 9：精确最高次项 -/

theorem gridLift_top (K : ℕ) (c : Fin (K + 1) → Polynomial ℚ)
    (hlow : ∀ h, h.val < K → (c h).natDegree + 2 * h.val < 2 * K)
    (hlast : c ⟨K, Nat.lt_succ_self K⟩ =
      Polynomial.C ((-1 : ℚ) ^ K / (Nat.factorial K : ℚ))) :
    (gridLift K c - MvPolynomial.C (topCoefficient K) *
      (MvPolynomial.X (1 : Fin 2)) ^ (2 * K + 1)).totalDegree ≤ 2 * K := by
  classical
  have htp : (1 : ℚ) / (((4 : ℚ) ^ K * ((2 * K + 1 : ℕ) : ℚ))) ≠ 0 :=
    one_div_ne_zero (mul_ne_zero (pow_ne_zero _ four_ne_zero) (by norm_cast))
  have htopEq : ((-1 : ℚ) ^ K / (Nat.factorial K : ℚ)) *
      (1 / (((4 : ℚ) ^ K * ((2 * K + 1 : ℕ) : ℚ)))) = topCoefficient K := by
    rw [topCoefficient]
    field_simp
    ring
  -- 撤去最高项后的余式 Q
  have hQdeg : (momentPolynomial K - Polynomial.C
        (1 / (((4 : ℚ) ^ K * ((2 * K + 1 : ℕ) : ℚ)))) *
      Polynomial.X ^ (2 * K + 1)).natDegree ≤ 2 * K := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    have hPle : (momentPolynomial K).natDegree ≤ 2 * K + 1 := by
      rw [momentPolynomial_natDegree]
    rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    rcases Nat.lt_trichotomy N (2 * K + 1) with h | h | h
    · exact absurd h (by omega)
    · subst h
      rw [if_pos rfl, mul_one, momentPolynomial_top_coeff, sub_self]
    · rw [if_neg (by omega), mul_zero, sub_zero]
      exact Polynomial.natDegree_le_iff_coeff_eq_zero.mp hPle N (by omega)
  -- 最高项恰好被吸收
  have hlastTerm : (c ⟨K, Nat.lt_succ_self K⟩).eval₂
        (MvPolynomial.C : ℚ →+* BiPoly) (MvPolynomial.X 0) =
      MvPolynomial.C ((-1 : ℚ) ^ K / (Nat.factorial K : ℚ)) := by
    rw [hlast]; simp
  have hPsplit : (momentPolynomial K).eval₂
        (MvPolynomial.C : ℚ →+* BiPoly) (MvPolynomial.X (1 : Fin 2)) =
      (momentPolynomial K - Polynomial.C
          (1 / (((4 : ℚ) ^ K * ((2 * K + 1 : ℕ) : ℚ)))) *
        Polynomial.X ^ (2 * K + 1)).eval₂
        (MvPolynomial.C : ℚ →+* BiPoly) (MvPolynomial.X (1 : Fin 2)) +
      MvPolynomial.C (1 / (((4 : ℚ) ^ K * ((2 * K + 1 : ℕ) : ℚ)))) *
        (MvPolynomial.X (1 : Fin 2)) ^ (2 * K + 1) := by
    have hEq : (momentPolynomial K - Polynomial.C
          (1 / (((4 : ℚ) ^ K * ((2 * K + 1 : ℕ) : ℚ)))) *
        Polynomial.X ^ (2 * K + 1)) +
      Polynomial.C (1 / (((4 : ℚ) ^ K * ((2 * K + 1 : ℕ) : ℚ)))) *
        Polynomial.X ^ (2 * K + 1) = momentPolynomial K := by
      abel
    conv_lhs => rw [← hEq]
    rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X_pow]
  have hsplit : (c ⟨K, Nat.lt_succ_self K⟩).eval₂
        (MvPolynomial.C : ℚ →+* BiPoly) (MvPolynomial.X 0) *
      (momentPolynomial K).eval₂
        (MvPolynomial.C : ℚ →+* BiPoly) (MvPolynomial.X (1 : Fin 2)) -
      MvPolynomial.C (topCoefficient K) * (MvPolynomial.X (1 : Fin 2)) ^ (2 * K + 1) =
      MvPolynomial.C ((-1 : ℚ) ^ K / (Nat.factorial K : ℚ)) *
      (momentPolynomial K - Polynomial.C
          (1 / (((4 : ℚ) ^ K * ((2 * K + 1 : ℕ) : ℚ)))) *
        Polynomial.X ^ (2 * K + 1)).eval₂
        (MvPolynomial.C : ℚ →+* BiPoly) (MvPolynomial.X (1 : Fin 2)) := by
    rw [hlastTerm, hPsplit, mul_add, ← mul_assoc, ← MvPolynomial.C_mul, htopEq]
    abel
  -- 主分解
  rw [gridLift, Fin.sum_univ_castSucc, add_sub_assoc]
  rw [show (Fin.last K : Fin (K + 1)) = ⟨K, Nat.lt_succ_self K⟩ from rfl,
    show ((⟨K, Nat.lt_succ_self K⟩ : Fin (K + 1)).val) = K from rfl, hsplit]
  refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_)
  · refine MvPolynomial.totalDegree_finsetSum_le fun h _ => ?_
    have hmul : ((c (Fin.castSucc h)).eval₂ (MvPolynomial.C : ℚ →+* BiPoly)
        (MvPolynomial.X 0) *
      (momentPolynomial (Fin.castSucc h).val).eval₂ (MvPolynomial.C : ℚ →+* BiPoly)
        (MvPolynomial.X 1)).totalDegree ≤
      ((c (Fin.castSucc h)).eval₂ (MvPolynomial.C : ℚ →+* BiPoly)
        (MvPolynomial.X 0)).totalDegree +
      ((momentPolynomial (Fin.castSucc h).val).eval₂ (MvPolynomial.C : ℚ →+* BiPoly)
        (MvPolynomial.X 1)).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    have h1 := totalDegree_eval₂_le (c (Fin.castSucc h)) 0
    have h2 := totalDegree_eval₂_le (momentPolynomial (Fin.castSucc h).val) 1
    rw [momentPolynomial_natDegree] at h2
    have hh := hlow (Fin.castSucc h) (Fin.isLt h)
    have hv : (Fin.castSucc h).val = h.val := rfl
    omega
  · have hmul := MvPolynomial.totalDegree_mul
      (MvPolynomial.C ((-1 : ℚ) ^ K / (Nat.factorial K : ℚ)))
      ((momentPolynomial K - Polynomial.C
          (1 / (((4 : ℚ) ^ K * ((2 * K + 1 : ℕ) : ℚ)))) *
        Polynomial.X ^ (2 * K + 1)).eval₂
        (MvPolynomial.C : ℚ →+* BiPoly) (MvPolynomial.X 1))
    have hC : ((MvPolynomial.C ((-1 : ℚ) ^ K / (Nat.factorial K : ℚ)) : BiPoly)).totalDegree
        = 0 := MvPolynomial.totalDegree_C _
    have h1 := totalDegree_eval₂_le (momentPolynomial K - Polynomial.C
      (1 / (((4 : ℚ) ^ K * ((2 * K + 1 : ℕ) : ℚ)))) *
      Polynomial.X ^ (2 * K + 1)) 1
    omega

/-! ## 目标 10：a/b 反对称 -/

private theorem evalSD_reflectD (p : BiPoly) (s d : ℚ) :
    evalSD (reflectD p) s d = evalSD p s (-(d : ℚ)) := by
  have hcomp := MvPolynomial.comp_eval₂Hom
    (f := (MvPolynomial.C : ℚ →+* BiPoly))
    (g := fun k : Fin 2 => if k = 0 then MvPolynomial.X 0
      else -(MvPolynomial.X 1 : BiPoly))
    (φ := (MvPolynomial.eval (fun i : Fin 2 => if i = 0 then s else d) :
      BiPoly →+* ℚ))
  have hCid : ((MvPolynomial.eval (fun i : Fin 2 => if i = 0 then s else d) :
      BiPoly →+* ℚ).comp (MvPolynomial.C : ℚ →+* BiPoly)) = RingHom.id ℚ := by
    ext a; simp
  have hfun : (fun i => MvPolynomial.eval (fun i : Fin 2 => if i = 0 then s else d)
        (if i = 0 then MvPolynomial.X 0 else -(MvPolynomial.X 1 : BiPoly))) =
      (fun i : Fin 2 => if i = 0 then s else -(d : ℚ)) := by
    funext i
    by_cases hi : i = 0 <;> simp [hi]
  show MvPolynomial.eval (fun i : Fin 2 => if i = 0 then s else d)
      (MvPolynomial.eval₂Hom (MvPolynomial.C : ℚ →+* BiPoly)
        (fun k : Fin 2 => if k = 0 then MvPolynomial.X 0
          else -(MvPolynomial.X 1 : BiPoly)) p)
    = MvPolynomial.eval (fun i : Fin 2 => if i = 0 then s else -(d : ℚ)) p
  rw [← RingHom.comp_apply, hcomp, hCid, hfun]
  rfl

theorem gridLift_ab_swap (K : ℕ) (c : Fin (K + 1) → Polynomial ℚ) (a b : ℚ) :
    evalSD (gridLift K c) (b + a) (b - a) =
      -evalSD (gridLift K c) (a + b) (a - b) := by
  have h1 : evalSD (reflectD (gridLift K c)) (b + a) (a - b)
      = evalSD (gridLift K c) (b + a) (-(a - b)) := evalSD_reflectD _ _ _
  have hneg : evalSD (-(gridLift K c) : BiPoly) (b + a) (a - b)
      = -evalSD (gridLift K c) (b + a) (a - b) := by
    simp only [evalSD, map_neg]
  rw [gridLift_odd] at h1
  rw [hneg, show -((a : ℚ) - b) = b - a from by ring] at h1
  rw [show (b : ℚ) + a = a + b from by ring] at h1 ⊢
  exact h1.symm

end HardinianHandoff
