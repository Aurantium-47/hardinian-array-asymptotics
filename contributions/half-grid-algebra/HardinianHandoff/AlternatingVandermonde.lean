import HardinianHandoff.AlternatingDefinitions
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Basic

/-! # C 线：交错多项式与 Vandermonde 整除（TASKS.md 目标 11–16）

核心是"逐因子根除法"：交错 p 在对角替换 `X_i := X_j` 下为零，由此获得
`(X_i − X_j) ∣ p`；再对变量子集归纳，把每个线性因子真实地除进去。
变号性接固定库的 Vandermonde 行列式（方向差 `(-1)^C(r,2)`）。 -/

open scoped BigOperators

noncomputable section
namespace HardinianHandoff

variable {r : ℕ}

/-! ## 对角替换同态 -/

/-- 把变量 `X_i` 代换成 `X_j`（其余变量不动）的环同态。 -/
private def substEq (i j : Fin r) : AltPoly r →+* AltPoly r :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun k => if k = i then MvPolynomial.X j else MvPolynomial.X k)

private theorem substEq_X (i j k : Fin r) :
    substEq i j (MvPolynomial.X k) =
      if k = i then MvPolynomial.X j else MvPolynomial.X k := by
  simp [substEq]

private theorem substEq_rename_swap (i j : Fin r) (hij : i ≠ j) (p : AltPoly r) :
    substEq i j (MvPolynomial.rename (Equiv.swap i j) p) = substEq i j p := by
  have hvar : ∀ k : Fin r, substEq i j (MvPolynomial.X (Equiv.swap i j k))
      = substEq i j (MvPolynomial.X k) := by
    intro k
    by_cases hki : k = i
    · subst hki
      rw [Equiv.swap_apply_left, substEq_X, substEq_X, if_neg (Ne.symm hij), if_pos rfl]
    · by_cases hkj : k = j
      · subst hkj
        rw [Equiv.swap_apply_right, substEq_X, substEq_X, if_pos rfl,
          if_neg (fun h => hij h.symm)]
      · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    rw [map_add (MvPolynomial.rename (Equiv.swap i j)), map_add (substEq i j), hp, hq,
      map_add (substEq i j)]
  | mul_X p k hp =>
    rw [map_mul (MvPolynomial.rename (Equiv.swap i j)), map_mul (substEq i j),
      MvPolynomial.rename_X, hvar k, hp, map_mul (substEq i j)]

/-! ## 除以 `(X_i − X_j)` 的带余除法（余项是对角替换值） -/

private theorem exists_div_substEq (i j : Fin r) (hij : i ≠ j) (p : AltPoly r) :
    ∃ q : AltPoly r, p = (MvPolynomial.X i - MvPolynomial.X j) * q + substEq i j p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, ?_⟩
    simp [substEq]
  | add p q hp hq =>
    obtain ⟨wp, e1⟩ := hp
    obtain ⟨wq, e2⟩ := hq
    refine ⟨wp + wq, ?_⟩
    rw [map_add]
    linear_combination e1 + e2
  | mul_X p k hp =>
    obtain ⟨q, e⟩ := hp
    by_cases hki : k = i
    · subst hki
      refine ⟨q * MvPolynomial.X k + substEq k j p, ?_⟩
      rw [map_mul, substEq_X, if_pos rfl]
      linear_combination MvPolynomial.X k * e
    · refine ⟨q * MvPolynomial.X k, ?_⟩
      rw [map_mul, substEq_X, if_neg hki]
      linear_combination MvPolynomial.X k * e

private theorem substEq_zero_of_alternating {i j : Fin r} (hij : i ≠ j) {p : AltPoly r}
    (hp : MvPolynomial.rename (Equiv.swap i j) p = -p) : substEq i j p = 0 := by
  have h := substEq_rename_swap i j hij p
  rw [hp, map_neg] at h
  have hxx : substEq i j p + substEq i j p = 0 := by
    nth_rewrite 2 [h.symm]
    exact add_neg_cancel _
  have h3 : ((2 : ℕ) : AltPoly r) * substEq i j p = 0 := by
    have h2c : ((2 : ℕ) : AltPoly r) = 1 + 1 := by norm_num
    rw [h2c, add_mul, one_mul]
    exact hxx
  exact (mul_eq_zero.mp h3).resolve_left (Nat.cast_ne_zero.mpr (by norm_num))

/-! ## 目标 11：单个线性因子整除 -/

theorem pairFactor_dvd (r : ℕ) (p : AltPoly r) (hp : IsAlternating p)
    (i j : Fin r) (hij : i ≠ j) :
    (MvPolynomial.X i - MvPolynomial.X j) ∣ p := by
  obtain ⟨q, e⟩ := exists_div_substEq i j hij p
  rw [substEq_zero_of_alternating hij (hp i j hij), add_zero] at e
  exact ⟨q, e⟩

/-! ## 逐因子根除法：所有根 `(X_i − X_m)` 一起整除 -/

private theorem roots_dvd (m : Fin r) : ∀ (W : Finset (Fin r)) (p : AltPoly r),
    (∀ i ∈ W, substEq i m p = 0) → (∀ i ∈ W, i ≠ m) →
    (∏ i ∈ W, (MvPolynomial.X i - MvPolynomial.X m)) ∣ p := by
  classical
  intro W
  induction W using Finset.induction_on with
  | empty => intro p _ _; simpa using dvd_refl p
  | insert k W hk ih =>
    intro p hroot hne
    have hkm : k ≠ m := hne k (by simp)
    have hkroot : substEq k m p = 0 := hroot k (by simp)
    obtain ⟨q, e⟩ := exists_div_substEq k m hkm p
    rw [hkroot, add_zero] at e
    have hrootq : ∀ i ∈ W, substEq i m q = 0 := by
      intro i hi
      have him : i ≠ m := hne i (by simp [hi])
      have hik : i ≠ k := fun h => hk (h ▸ hi)
      have hi0 : substEq i m p = 0 := hroot i (by simp [hi])
      rw [e, map_mul, map_sub, substEq_X, substEq_X,
        if_neg (fun h => hik h.symm), if_neg (fun h => him h.symm)] at hi0
      rcases mul_eq_zero.mp hi0 with h1 | h2
      · exact absurd h1 (sub_ne_zero.2 fun hcon =>
          hkm (MvPolynomial.X_injective hcon))
      · exact h2
    obtain ⟨u, hu⟩ := ih q hrootq (fun i hi => hne i (by simp [hi]))
    refine ⟨u, ?_⟩
    rw [e, hu, Finset.prod_insert hk]
    ring

/-! ## 变量子集上的交错性与 Vandermonde 乘积 -/

private def IsAlternatingOn (r : ℕ) (V : Finset (Fin r)) (p : AltPoly r) : Prop :=
  ∀ i ∈ V, ∀ j ∈ V, i ≠ j → MvPolynomial.rename (Equiv.swap i j) p = -p

private def deltaOver (r : ℕ) (V : Finset (Fin r)) : AltPoly r :=
  ∏ i ∈ V, ∏ k ∈ V.filter (fun k => i < k), (MvPolynomial.X i - MvPolynomial.X k)

private theorem vandermondeOn_dvd :
    ∀ (n : ℕ) (r : ℕ) (V : Finset (Fin r)) (p : AltPoly r),
      V.card = n → IsAlternatingOn r V p → deltaOver r V ∣ p := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro r V p hcard hAlt
    by_cases h0 : V.card = 0
    · have hV : V = ∅ := by simpa using h0
      subst hV
      simpa [deltaOver] using dvd_refl p
    by_cases h1 : V.card = 1
    · obtain ⟨a, ha⟩ : ∃ a, V = {a} := by
        rcases Finset.card_eq_one.1 h1 with ⟨a, rfl⟩
        exact ⟨a, rfl⟩
      subst ha
      have hfilter : (({a} : Finset (Fin r)).filter (fun k => a < k)) = ∅ := by
        simp only [Finset.filter_singleton, if_neg (lt_irrefl a)]
      have hdelta1 : deltaOver r ({a} : Finset (Fin r)) = 1 := by
        rw [deltaOver, Finset.prod_singleton, hfilter, Finset.prod_empty]
      rw [hdelta1]
      exact one_dvd p
    -- 至少两个元素：取最大元归纳
    have hpos : 0 < V.card := by omega
    have hne0 : V.Nonempty := Finset.card_pos.1 hpos
    obtain ⟨m, hm, hmmax⟩ : ∃ m ∈ V, ∀ i ∈ V, i ≤ m := by
      use V.max' hne0
      exact ⟨Finset.max'_mem V hne0, fun i hi => Finset.le_max' V i hi⟩
    have hcardV' : (V.erase m).card = n - 1 := by
      rw [Finset.card_erase_of_mem hm]
      omega
    have him : ∀ i ∈ V.erase m, i < m := by
      intro i hi
      have h1' : i ≤ m := hmmax i (Finset.mem_of_mem_erase hi)
      have h2' : i ≠ m := (Finset.mem_erase.1 hi).1
      omega
    -- 1) 每个根 (X_i − X_m) 都除尽 p
    have hroots : ∀ i ∈ V.erase m, substEq i m p = 0 := by
      intro i hi
      exact substEq_zero_of_alternating ((him i hi).ne)
        (hAlt i (Finset.mem_of_mem_erase hi) m hm (fun hcon => (him i hi).ne hcon))
    obtain ⟨q, hq⟩ := roots_dvd m (V.erase m) p hroots
      (fun i hi => (Finset.mem_erase.1 hi).1)
    -- 2) 列乘积非零且在对换下不变，从而商在剩余变量上交错
    have hwne : (∏ i ∈ V.erase m, (MvPolynomial.X i - MvPolynomial.X m : AltPoly r)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun i hi =>
        sub_ne_zero.2 fun hcon => (him i hi).ne (MvPolynomial.X_injective hcon)
    have hqAlt : IsAlternatingOn r (V.erase m) q := by
      intro a ha b hb hab
      have ham : a ≠ m := (Finset.mem_erase.mp ha).1
      have hbm : b ≠ m := (Finset.mem_erase.mp hb).1
      have hswapmem : ∀ i ∈ V.erase m, Equiv.swap a b i ∈ V.erase m := by
        intro i hi
        refine Finset.mem_erase.2 ⟨?_, ?_⟩
        · by_cases hia : i = a
          · subst hia
            rw [Equiv.swap_apply_left]
            exact hbm
          · by_cases hib : i = b
            · subst hib
              rw [Equiv.swap_apply_right]
              exact ham
            · rw [Equiv.swap_apply_of_ne_of_ne hia hib]
              exact (Finset.mem_erase.1 hi).1
        · have hiV : i ∈ V := Finset.mem_of_mem_erase hi
          by_cases hia : i = a
          · subst hia
            rw [Equiv.swap_apply_left]
            exact Finset.mem_of_mem_erase hb
          · by_cases hib : i = b
            · subst hib
              rw [Equiv.swap_apply_right]
              exact Finset.mem_of_mem_erase ha
            · rw [Equiv.swap_apply_of_ne_of_ne hia hib]
              exact hiV
      have hswapfix : MvPolynomial.rename (Equiv.swap a b)
          (∏ i ∈ V.erase m, (MvPolynomial.X i - MvPolynomial.X m : AltPoly r))
          = ∏ i ∈ V.erase m, (MvPolynomial.X i - MvPolynomial.X m : AltPoly r) := by
        rw [map_prod (MvPolynomial.rename (Equiv.swap a b))]
        refine Finset.prod_nbij (fun i => Equiv.swap a b i) ?_ ?_ ?_ ?_
        · exact fun i hi => hswapmem i hi
        · intro x _ y _ h
          exact (Equiv.swap a b).injective h
        · intro y hy
          have hy' : y ∈ V.erase m := by simpa only [Finset.mem_coe] using hy
          exact ⟨Equiv.swap a b y, hswapmem y hy', by simp⟩
        · intro i hi
          have hmm : Equiv.swap a b m = m :=
            Equiv.swap_apply_of_ne_of_ne (Ne.symm ham) (Ne.symm hbm)
          rw [map_sub, MvPolynomial.rename_X, MvPolynomial.rename_X, hmm]
      have hp' : MvPolynomial.rename (Equiv.swap a b) p = -p :=
        hAlt a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb) hab
      have hkey : (∏ i ∈ V.erase m, (MvPolynomial.X i - MvPolynomial.X m : AltPoly r)) *
          MvPolynomial.rename (Equiv.swap a b) q
          = (∏ i ∈ V.erase m, (MvPolynomial.X i - MvPolynomial.X m : AltPoly r)) * (-q : AltPoly r) := by
        have h1 : (∏ i ∈ V.erase m, (MvPolynomial.X i - MvPolynomial.X m : AltPoly r)) *
            MvPolynomial.rename (Equiv.swap a b) q
            = MvPolynomial.rename (Equiv.swap a b)
              ((∏ i ∈ V.erase m, (MvPolynomial.X i - MvPolynomial.X m : AltPoly r)) * q) := by
          rw [map_mul, hswapfix]
        rw [h1, ← hq, hp', hq, ← mul_neg]
      exact mul_left_cancel₀ hwne hkey
    -- 3) deltaOver V = deltaOver V' × 列乘积
    have hinnerm : (∏ k ∈ V.filter (fun k => m < k),
        (MvPolynomial.X m - MvPolynomial.X k : AltPoly r)) = 1 := by
      have hfil0 : V.filter (fun k => m < k) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro k hk
        exact not_lt.2 (hmmax k hk)
      rw [hfil0, Finset.prod_empty]
    have hinnerSplit : ∀ i ∈ V.erase m,
        (∏ k ∈ V.filter (fun k => i < k), (MvPolynomial.X i - MvPolynomial.X k : AltPoly r)) =
        (∏ k ∈ (V.erase m).filter (fun k => i < k), (MvPolynomial.X i - MvPolynomial.X k : AltPoly r)) *
          (MvPolynomial.X i - MvPolynomial.X m : AltPoly r) := by
      intro i hi
      have hmnotfilt : m ∉ (V.erase m).filter (fun k => i < k) := fun h =>
        (Finset.mem_erase.mp (Finset.mem_filter.mp h).1).1 rfl
      have hfil : V.filter (fun k => i < k) =
          insert m ((V.erase m).filter (fun k => i < k)) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
        by_cases hkm : k = m
        · subst hkm
          constructor
          · exact fun _ => Or.inl rfl
          · rintro (_ | h2)
            · exact ⟨hm, him i hi⟩
            · exact ⟨h2.1.2, h2.2⟩
        · constructor
          · rintro ⟨hkV, hik⟩
            exact Or.inr ⟨⟨hkm, hkV⟩, hik⟩
          · rintro (rfl | ⟨⟨-, hkV⟩, hik⟩)
            · exact absurd rfl hkm
            · exact ⟨hkV, hik⟩
      rw [hfil, Finset.prod_insert hmnotfilt, mul_comm]
    have hdelta : deltaOver r V = deltaOver r (V.erase m) *
        (∏ i ∈ V.erase m, (MvPolynomial.X i - MvPolynomial.X m : AltPoly r)) := by
      have step1 : deltaOver r V = ∏ i ∈ V.erase m,
          (∏ k ∈ V.filter (fun k => i < k),
            (MvPolynomial.X i - MvPolynomial.X k : AltPoly r)) := by
        rw [deltaOver]
        exact (Finset.prod_erase (f := fun i => ∏ k ∈ V.filter (fun k => i < k),
          (MvPolynomial.X i - MvPolynomial.X k : AltPoly r)) V hinnerm).symm
      have step2 : (∏ i ∈ V.erase m,
            (∏ k ∈ V.filter (fun k => i < k),
              (MvPolynomial.X i - MvPolynomial.X k : AltPoly r))) =
          deltaOver r (V.erase m) *
            (∏ i ∈ V.erase m, (MvPolynomial.X i - MvPolynomial.X m : AltPoly r)) := by
        rw [Finset.prod_congr rfl fun i hi => hinnerSplit i hi,
          Finset.prod_mul_distrib, deltaOver]
      rw [step1, step2]
    -- 4) 归纳并组合
    obtain ⟨u, hu⟩ := ih (n - 1) (by omega) r (V.erase m) q hcardV' hqAlt
    refine ⟨u, ?_⟩
    rw [hq, hu, hdelta]
    ring

/-! ## 目标 12：整条 Vandermonde 乘积整除 -/

theorem vandermonde_dvd (r : ℕ) (p : AltPoly r) (hp : IsAlternating p) :
    vandermonde r ∣ p := by
  have h1 := vandermondeOn_dvd (Finset.univ.card) r (Finset.univ : Finset (Fin r)) p rfl
    (fun i _ j _ hij => hp i j hij)
  have h2 : deltaOver r (Finset.univ : Finset (Fin r)) = vandermonde r := by
    rw [deltaOver, vandermonde]
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr ?_ fun k _ => rfl
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (Finset.mem_Ioi).symm
  rwa [h2] at h1

/-! ## 目标 13：非零 -/

theorem vandermonde_ne_zero (r : ℕ) : vandermonde r ≠ 0 := by
  rw [vandermonde]
  refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun k hk => ?_
  exact sub_ne_zero.2 fun hcon =>
    (Finset.mem_Ioi.mp hk).ne (MvPolynomial.X_injective hcon)

private theorem prod_neg_alt {ι : Type*} (s : Finset ι) (f : ι → AltPoly r) :
    ∏ i ∈ s, -(f i) = (-1 : AltPoly r) ^ s.card * ∏ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ih,
      Finset.card_insert_of_not_mem ha, pow_succ]
    ring

private theorem sum_range_rev_sub (r : ℕ) :
    ∑ k ∈ Finset.range r, (r - 1 - k) = ∑ k ∈ Finset.range r, k := by
  refine Finset.sum_nbij (fun k => r - 1 - k) ?_ ?_ ?_ ?_
  · intro k hk
    have hk' : k < r := by simpa using hk
    show r - 1 - k ∈ Finset.range r
    exact Finset.mem_range.mpr (by omega)
  · intro a ha b hb hab
    have ha' : a < r := by simpa using ha
    have hb' : b < r := by simpa using hb
    have hab' : r - 1 - a = r - 1 - b := hab
    omega
  · intro b hb
    have hb' : b < r := by simpa using hb
    refine ⟨r - 1 - b, Finset.mem_range.mpr (by omega), ?_⟩
    show r - 1 - (r - 1 - b) = b
    omega
  · intro k _; rfl

private theorem sum_card_Ioi (r : ℕ) :
    ∑ i : Fin r, (Finset.Ioi i).card = Nat.choose r 2 := by
  have key : ∑ i : Fin r, (Finset.Ioi i).card = ∑ k ∈ Finset.range r, (r - 1 - k) := by
    rw [← Fin.sum_univ_eq_sum_range (f := fun k => r - 1 - k) r]
    exact Finset.sum_congr rfl fun i _ => Fin.card_Ioi i
  rw [key, sum_range_rev_sub, Finset.sum_range_id, Nat.choose_two_right]

/-! ## 目标 14：总次数 -/

/-- vandermonde 是 choose r 2 次齐次多项式（D 线复用）。 -/
theorem vandermonde_isHomogeneous (r : ℕ) :
    MvPolynomial.IsHomogeneous (vandermonde r) (Nat.choose r 2) := by
  have hinner : ∀ i : Fin r, MvPolynomial.IsHomogeneous
      (∏ k ∈ Finset.Ioi i, (MvPolynomial.X i - MvPolynomial.X k : AltPoly r))
      ((Finset.Ioi i).card) := by
    intro i
    have hf : ∀ k ∈ Finset.Ioi i, MvPolynomial.IsHomogeneous
        ((MvPolynomial.X i - MvPolynomial.X k : AltPoly r)) 1 := fun k _ =>
      MvPolynomial.IsHomogeneous.sub (MvPolynomial.isHomogeneous_X ℚ i)
        (MvPolynomial.isHomogeneous_X ℚ k)
    have h := MvPolynomial.IsHomogeneous.prod (Finset.Ioi i)
      (fun (k : Fin r) => (MvPolynomial.X i - MvPolynomial.X k : AltPoly r)) (fun _ => 1) hf
    rwa [show (∑ _x ∈ Finset.Ioi i, (1 : ℕ)) = (Finset.Ioi i).card from by simp] at h
  have houter : MvPolynomial.IsHomogeneous (vandermonde r)
      (∑ i : Fin r, (Finset.Ioi i).card) := by
    rw [vandermonde]
    exact MvPolynomial.IsHomogeneous.prod _ _ (fun i => (Finset.Ioi i).card)
      (fun i _ => hinner i)
  rw [← sum_card_Ioi]
  exact houter

theorem vandermonde_totalDegree (r : ℕ) : (vandermonde r).totalDegree = Nat.choose r 2 := by
  rw [MvPolynomial.IsHomogeneous.totalDegree (vandermonde_isHomogeneous r)
    (vandermonde_ne_zero r)]

/-! ## 目标 15：变号（行列式路线） -/

theorem vandermonde_isAlternating (r : ℕ) : IsAlternating (vandermonde r) := by
  intro i j hij
  have hneg : ∀ (w : Fin r → AltPoly r),
      (∏ a : Fin r, ∏ b ∈ Finset.Ioi a, (w b - w a)) =
      (-1 : AltPoly r) ^ (Nat.choose r 2) * (∏ a : Fin r, ∏ b ∈ Finset.Ioi a, (w a - w b)) := by
    intro w
    have hinner : ∀ a : Fin r, (∏ b ∈ Finset.Ioi a, (w b - w a)) =
        (-1 : AltPoly r) ^ (Finset.Ioi a).card * (∏ b ∈ Finset.Ioi a, (w a - w b)) := by
      intro a
      have h1 : ∏ b ∈ Finset.Ioi a, (w b - w a) = ∏ b ∈ Finset.Ioi a, -(w a - w b) :=
        Finset.prod_congr rfl fun b _ => (neg_sub (w a) (w b)).symm
      rw [h1, prod_neg_alt]
    rw [Finset.prod_congr rfl fun a _ => hinner a, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, sum_card_Ioi]
  have hsgn : ((Equiv.Perm.sign (Equiv.swap i j) : ℤ) : AltPoly r) = -1 := by
    rw [Equiv.Perm.sign_swap hij]
    simp
  have hA : (Matrix.vandermonde (fun k => MvPolynomial.X k : Fin r → AltPoly r)).det
      = (-1 : AltPoly r) ^ Nat.choose r 2 * vandermonde r := by
    rw [Matrix.det_vandermonde, hneg (fun k => MvPolynomial.X k)]
    rfl
  have hB : (Matrix.vandermonde (fun k => MvPolynomial.X (Equiv.swap i j k) :
      Fin r → AltPoly r)).det
      = (-1 : AltPoly r) ^ Nat.choose r 2 *
        MvPolynomial.rename (Equiv.swap i j) (vandermonde r) := by
    rw [Matrix.det_vandermonde, hneg (fun k => MvPolynomial.X (Equiv.swap i j k))]
    congr 1
    rw [vandermonde, map_prod (MvPolynomial.rename (Equiv.swap i j))]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [map_prod (MvPolynomial.rename (Equiv.swap i j))]
    exact Finset.prod_congr rfl fun b _ => by
      rw [map_sub, MvPolynomial.rename_X, MvPolynomial.rename_X]
  have hrowperm : (Matrix.vandermonde (fun k => MvPolynomial.X (Equiv.swap i j k) :
      Fin r → AltPoly r))
      = (Matrix.vandermonde (fun k => MvPolynomial.X k : Fin r → AltPoly r)).submatrix
          (Equiv.swap i j) id := by
    ext a b
    simp [Matrix.submatrix_apply]
  have hkey : ((-1 : AltPoly r) ^ Nat.choose r 2) *
      MvPolynomial.rename (Equiv.swap i j) (vandermonde r)
      = ((-1 : AltPoly r) ^ Nat.choose r 2) * (-(vandermonde r)) := by
    rw [← hB, hrowperm, Matrix.det_permute, hA, hsgn]
    ring
  exact mul_left_cancel₀ (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hkey

/-! ## 目标 16：r ≤ 1 时空积为 1 -/

theorem vandermonde_small (r : ℕ) (hr : r ≤ 1) : vandermonde r = 1 := by
  cases r with
  | zero => simp [vandermonde]
  | succ r =>
    have hr0 : r = 0 := by omega
    subst hr0
    have hIoi : (Finset.Ioi (0 : Fin 1)) = ∅ := by
      ext b
      fin_cases b
      simp
    rw [vandermonde]
    have hone : ∀ i : Fin 1,
        (∏ j ∈ Finset.Ioi i, (MvPolynomial.X i - MvPolynomial.X j : AltPoly 1)) = 1 := by
      intro i
      fin_cases i
      simp [hIoi]
    rw [Finset.prod_congr rfl fun i _ => hone i]
    simp

end HardinianHandoff
