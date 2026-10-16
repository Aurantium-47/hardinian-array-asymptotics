import Hardinian.BinomialExponentialTop
import Hardinian.OrderedBinomialKernelExpansion
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Ring.Parity

namespace Hardinian

open Finset MvPolynomial

noncomputable def binomialExpExponent (r e : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single (0 : Fin 2) r + Finsupp.single (1 : Fin 2) e

noncomputable def binomialExpEvenCoeff (n : ℕ) (h : Fin (n + 1)) : Polynomial ℚ :=
  ∑ d ∈ (binomialExpCoeff n).support.filter (fun d => d 1 = 2 * h.val),
    Polynomial.monomial (d 0) (MvPolynomial.coeff d (binomialExpCoeff n))

theorem binomialExpExponent_apply (r e : ℕ) :
    binomialExpExponent r e 0 = r ∧ binomialExpExponent r e 1 = e := by
  simp [binomialExpExponent]

theorem binomialExpExponent_eta (d : Fin 2 →₀ ℕ) :
    binomialExpExponent (d 0) (d 1) = d := by
  ext i
  by_cases hi : i.val = 0
  · have hi0 : i = 0 := Fin.ext hi
    subst i
    simp [binomialExpExponent]
  · have hi1 : i = 1 := Fin.ext (by have := i.isLt; omega)
    subst i
    simp [binomialExpExponent]

theorem binomialExpExponent_weight (d : Fin 2 →₀ ℕ) :
    d.sum (fun _ e => e) = d 0 + d 1 := by
  simpa only [Fin.sum_univ_two] using
    Finsupp.sum_fintype d (fun _ e => e) (by intro i; rfl)

theorem binomialExpMonomial_factor (d : Fin 2 →₀ ℕ) (c : ℚ) :
    (monomial d c : MvPolynomial (Fin 2) ℚ) = C c * X 0 ^ (d 0) * X 1 ^ (d 1) := by
  rw [monomial_eq,
    Finsupp.prod_fintype d (fun i e => (X i : MvPolynomial (Fin 2) ℚ) ^ e)
      (by intro i; simp), Fin.prod_univ_two]
  ring

theorem binomialExpReflection_monomial (d : Fin 2 →₀ ℕ) (c : ℚ) :
    eval₂Hom C (fun i : Fin 2 => if i = 0 then X 0 else -X 1)
      (monomial d c : MvPolynomial (Fin 2) ℚ) = monomial d (((-1 : ℚ) ^ (d 1)) * c) := by
  rw [binomialExpMonomial_factor, binomialExpMonomial_factor]
  simp only [map_mul, map_pow, eval₂Hom_C, eval₂Hom_X',
    if_pos (rfl : (0 : Fin 2) = 0), if_pos True.intro,
    if_neg (by decide : (1 : Fin 2) ≠ 0)]
  rw [neg_pow]
  simp only [map_mul, map_pow, map_neg, map_one]
  ring

theorem binomialExpCoeff_reflect_coeff (n : ℕ) (d : Fin 2 →₀ ℕ) :
    coeff d (binomialExpCoeff n) = ((-1 : ℚ) ^ (d 1)) * coeff d (binomialExpCoeff n) := by
  classical
  have he : coeff d
      (eval₂Hom C (fun i : Fin 2 => if i = 0 then X 0 else -X 1) (binomialExpCoeff n)) =
      ((-1 : ℚ) ^ (d 1)) * coeff d (binomialExpCoeff n) := by
    rw [MvPolynomial.as_sum (binomialExpCoeff n), map_sum, coeff_sum]
    simp_rw [binomialExpReflection_monomial, coeff_monomial]
    rw [sum_eq_single d]
    · simp
    · intro e he hed
      simp [hed]
    · intro hd
      have hc : coeff d (binomialExpCoeff n) = 0 := by
        by_contra hc
        exact hd (MvPolynomial.mem_support_iff.mpr hc)
      simp [hc]
  rw [binomialExpCoeff_reflect] at he
  exact he

theorem binomialExpCoeff_support_even (n : ℕ) (d : Fin 2 →₀ ℕ)
    (hd : d ∈ (binomialExpCoeff n).support) : Even (d 1) := by
  have hc : coeff d (binomialExpCoeff n) ≠ 0 := MvPolynomial.mem_support_iff.mp hd
  have hp : (-1 : ℚ) ^ (d 1) = 1 := by
    apply mul_right_cancel₀ hc
    simpa only [one_mul] using (binomialExpCoeff_reflect_coeff n d).symm
  exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℚ) ≠ 1)).mp hp

theorem binomialExpCoeff_support_weight (n : ℕ) (d : Fin 2 →₀ ℕ)
    (hd : d ∈ (binomialExpCoeff n).support) : d 0 + d 1 ≤ 2 * n := by
  have hw := MvPolynomial.le_totalDegree hd
  rw [binomialExpExponent_weight] at hw
  exact hw.trans (binomialExpCoeff_totalDegree n)

theorem binomialExpCoeff_support_half_index (n : ℕ) (d : Fin 2 →₀ ℕ)
    (hd : d ∈ (binomialExpCoeff n).support) :
    ∃! h : Fin (n + 1), d 1 = 2 * h.val := by
  obtain ⟨h, hh⟩ := binomialExpCoeff_support_even n d hd
  have hh2 : d 1 = 2 * h := by omega
  have hw := binomialExpCoeff_support_weight n d hd
  have hb : h < n + 1 := by omega
  refine ⟨⟨h, hb⟩, hh2, ?_⟩
  intro z hz
  apply Fin.ext
  change z.val = h
  omega

theorem binomialExpEvenCoeff_coeff (n : ℕ) (h : Fin (n + 1)) (r : ℕ) :
    (binomialExpEvenCoeff n h).coeff r =
      coeff (binomialExpExponent r (2 * h.val)) (binomialExpCoeff n) := by
  classical
  let e := binomialExpExponent r (2 * h.val)
  unfold binomialExpEvenCoeff
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [sum_eq_single e]
  · simp [e, binomialExpExponent]
  · intro d hd hde
    have hd1 : d 1 = 2 * h.val := (mem_filter.mp hd).2
    have hd0 : d 0 ≠ r := by
      intro h0
      apply hde
      calc
        d = binomialExpExponent (d 0) (d 1) := (binomialExpExponent_eta d).symm
        _ = e := by rw [h0, hd1]
    simp [hd0]
  · intro he
    have hnot : e ∉ (binomialExpCoeff n).support := by
      intro hs
      apply he
      exact mem_filter.mpr ⟨hs, (binomialExpExponent_apply r (2 * h.val)).2⟩
    have hc : coeff e (binomialExpCoeff n) = 0 := by
      simpa only [MvPolynomial.mem_support_iff, not_not] using hnot
    simp [hc]

theorem binomialExpEvenCoeff_zero (h : Fin 1) : binomialExpEvenCoeff 0 h = 1 := by
  classical
  have hh : h.val = 0 := by have := h.isLt; omega
  ext r
  rw [binomialExpEvenCoeff_coeff, binomialExpCoeff_zero]
  by_cases hr : r = 0
  · subst r
    simp [binomialExpExponent, hh]
  · have he : (0 : Fin 2 →₀ ℕ) ≠ binomialExpExponent r (2 * h.val) := by
      intro he
      have hh0 := congrArg (fun d : Fin 2 →₀ ℕ => d 0) he
      have hr0 : r = 0 := by simpa [binomialExpExponent] using hh0.symm
      exact hr hr0
    simp only [MvPolynomial.coeff_one, if_neg he, Polynomial.coeff_one, if_neg hr]

theorem binomialExpCoeff_even_decomposition (n : ℕ) :
    binomialExpCoeff n = ∑ h : Fin (n + 1),
      (binomialExpEvenCoeff n h).eval₂
        (C : ℚ →+* MvPolynomial (Fin 2) ℚ) (X 0) * (X 1) ^ (2 * h.val) := by
  classical
  have hlift (h : Fin (n + 1)) :
      (binomialExpEvenCoeff n h).eval₂ (C : ℚ →+* MvPolynomial (Fin 2) ℚ) (X 0) *
        (X 1) ^ (2 * h.val) =
      ∑ d ∈ (binomialExpCoeff n).support.filter (fun d => d 1 = 2 * h.val),
        monomial d (coeff d (binomialExpCoeff n)) := by
    simp only [binomialExpEvenCoeff, Polynomial.eval₂_finset_sum,
      Polynomial.eval₂_monomial, sum_mul]
    apply sum_congr rfl
    intro d hd
    rw [binomialExpMonomial_factor, (mem_filter.mp hd).2]
  rw [MvPolynomial.as_sum (binomialExpCoeff n)]
  simp_rw [hlift, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro d hd
  obtain ⟨h, hh, hu⟩ := binomialExpCoeff_support_half_index n d hd
  rw [sum_eq_single h]
  · simp [hh]
  · intro i hi hih
    have hne : d 1 ≠ 2 * i.val := by
      intro he
      exact hih (hu i he)
    simp only [if_neg hne]
  · intro hn
    exact False.elim (hn (mem_univ h))

theorem binomialExpCoeff_even_eval_rat (n : ℕ) (s t : ℚ) :
    MvPolynomial.eval (fun i : Fin 2 => if i = 0 then s else t) (binomialExpCoeff n) =
      ∑ h : Fin (n + 1), (binomialExpEvenCoeff n h).eval s * t ^ (2 * h.val) := by
  classical
  have hlift (h : Fin (n + 1)) :
      MvPolynomial.eval (fun i : Fin 2 => if i = 0 then s else t)
        ((binomialExpEvenCoeff n h).eval₂ (C : ℚ →+* MvPolynomial (Fin 2) ℚ) (X 0)) =
      (binomialExpEvenCoeff n h).eval s := by
    simp [binomialExpEvenCoeff, Polynomial.eval₂_finset_sum, Polynomial.eval₂_monomial,
      Polynomial.eval_finset_sum, Polynomial.eval_monomial]
  rw [binomialExpCoeff_even_decomposition]
  simp only [map_sum, map_mul, map_pow, hlift, MvPolynomial.eval_X,
    if_neg (by decide : (1 : Fin 2) ≠ 0)]

theorem binomialExpCoeff_even_eval_real (n : ℕ) (s t : ℝ) :
    eval₂Hom (Rat.castHom ℝ) (fun i : Fin 2 => if i = 0 then s else t) (binomialExpCoeff n) =
      ∑ h : Fin (n + 1),
        (binomialExpEvenCoeff n h).eval₂ (Rat.castHom ℝ) s * t ^ (2 * h.val) := by
  classical
  have hlift (h : Fin (n + 1)) :
      eval₂Hom (Rat.castHom ℝ) (fun i : Fin 2 => if i = 0 then s else t)
        ((binomialExpEvenCoeff n h).eval₂ (C : ℚ →+* MvPolynomial (Fin 2) ℚ) (X 0)) =
      (binomialExpEvenCoeff n h).eval₂ (Rat.castHom ℝ) s := by
    simp [binomialExpEvenCoeff, Polynomial.eval₂_finset_sum, Polynomial.eval₂_monomial]
  rw [binomialExpCoeff_even_decomposition]
  simp only [map_sum, map_mul, map_pow, hlift, eval₂Hom_X',
    if_neg (by decide : (1 : Fin 2) ≠ 0)]

theorem binomialExpEvenCoeff_weighted_degree (n : ℕ) (h : Fin (n + 1)) :
    (binomialExpEvenCoeff n h).natDegree + 2 * h.val ≤ 2 * n := by
  classical
  by_cases hc : binomialExpEvenCoeff n h = 0
  · rw [hc, Polynomial.natDegree_zero, zero_add]
    have := h.isLt
    omega
  · have hnz : (binomialExpEvenCoeff n h).coeff (binomialExpEvenCoeff n h).natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hc
    have hd : binomialExpExponent (binomialExpEvenCoeff n h).natDegree (2 * h.val) ∈
        (binomialExpCoeff n).support := by
      apply MvPolynomial.mem_support_iff.mpr
      rwa [← binomialExpEvenCoeff_coeff]
    have hw := binomialExpCoeff_support_weight n _ hd
    simpa [binomialExpExponent] using hw

theorem binomialExpEvenCoeff_strict_low (n : ℕ) (h : Fin (n + 1)) (hh : h.val < n) :
    (binomialExpEvenCoeff n h).natDegree + 2 * h.val < 2 * n := by
  classical
  by_cases hc : binomialExpEvenCoeff n h = 0
  · rw [hc, Polynomial.natDegree_zero, zero_add]
    omega
  have hn : 1 ≤ n := by omega
  let d := binomialExpExponent (binomialExpEvenCoeff n h).natDegree (2 * h.val)
  have hnz : coeff d (binomialExpCoeff n) ≠ 0 := by
    change coeff (binomialExpExponent (binomialExpEvenCoeff n h).natDegree (2 * h.val)) _ ≠ 0
    rw [← binomialExpEvenCoeff_coeff, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hc
  have hne : Finsupp.single (1 : Fin 2) (2 * n) ≠ d := by
    intro he
    have he1 := congrArg (fun e : Fin 2 →₀ ℕ => e 1) he
    have hnum : 2 * n = 2 * h.val := by simpa [d, binomialExpExponent] using he1
    omega
  have hlead : coeff d
      (C (((-1 : ℚ) ^ n) / (n.factorial : ℚ)) * (X (1 : Fin 2)) ^ (2 * n)) = 0 := by
    rw [C_mul_X_pow_eq_monomial, coeff_monomial, if_neg hne]
  have hres : coeff d (binomialExpCoeff n -
      C (((-1 : ℚ) ^ n) / (n.factorial : ℚ)) * (X (1 : Fin 2)) ^ (2 * n)) ≠ 0 := by
    rw [MvPolynomial.coeff_sub, hlead, sub_zero]
    exact hnz
  have hw := (MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hres)).trans
    (binomialExpCoeff_top_remainder n hn)
  rw [binomialExpExponent_weight] at hw
  have hbound : (binomialExpEvenCoeff n h).natDegree + 2 * h.val ≤ 2 * n - 1 := by
    simpa [d, binomialExpExponent] using hw
  omega

theorem binomialExpEvenCoeff_last (n : ℕ) :
    binomialExpEvenCoeff n ⟨n, Nat.lt_succ_self n⟩ =
      Polynomial.C (((-1 : ℚ) ^ n) / (n.factorial : ℚ)) := by
  classical
  by_cases hn : n = 0
  · subst n
    simpa using binomialExpEvenCoeff_zero ⟨0, by decide⟩
  have hn1 : 1 ≤ n := by omega
  ext r
  rw [binomialExpEvenCoeff_coeff]
  let d := binomialExpExponent r (2 * n)
  change coeff d (binomialExpCoeff n) = _
  have hweight : (∑ i ∈ d.support, d i) = r + 2 * n := by
    change d.sum (fun _ e => e) = _
    rw [binomialExpExponent_weight]
    simp [d, binomialExpExponent]
  have hz : coeff d (binomialExpCoeff n -
      C (((-1 : ℚ) ^ n) / (n.factorial : ℚ)) * (X (1 : Fin 2)) ^ (2 * n)) = 0 := by
    apply coeff_eq_zero_of_totalDegree_lt
    exact (binomialExpCoeff_top_remainder n hn1).trans_lt (by rw [hweight]; omega)
  rw [MvPolynomial.coeff_sub] at hz
  have he := sub_eq_zero.mp hz
  rw [he, C_mul_X_pow_eq_monomial, coeff_monomial, Polynomial.coeff_C]
  by_cases hr : r = 0
  · subst r
    simp [d, binomialExpExponent]
  · have hne : Finsupp.single (1 : Fin 2) (2 * n) ≠ d := by
      intro heq
      have he0 := congrArg (fun e : Fin 2 →₀ ℕ => e 0) heq
      have hr0 : r = 0 := by simpa [d, binomialExpExponent] using he0.symm
      exact hr hr0
    rw [if_neg hne, if_neg hr]

theorem orderedBinomialKernelCoeff_even_sum (n a b : ℕ) :
    orderedBinomialKernelCoeff n a b =
      ∑ v ∈ range (a - b), ∑ h : Fin (n + 1),
        (binomialExpEvenCoeff n h).eval ((a : ℚ) + (b : ℚ)) *
          ((v : ℚ) - ((a - b : ℕ) : ℚ) / 2) ^ (2 * h.val) := by
  classical
  unfold orderedBinomialKernelCoeff
  apply sum_congr rfl
  intro v hv
  exact binomialExpCoeff_even_eval_rat n ((a : ℚ) + (b : ℚ))
    ((v : ℚ) - ((a - b : ℕ) : ℚ) / 2)

end Hardinian
