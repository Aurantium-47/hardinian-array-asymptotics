import Hardinian.BinomialLogCoefficientPolynomials

namespace Hardinian

open Finset MvPolynomial

def binomialCompositionOrder {k n : ℕ} (v : Fin k → Fin n) : ℕ :=
  ∑ i : Fin k, ((v i).val + 1)

noncomputable def binomialPositiveCompositions (n k : ℕ) : Finset (Fin k → Fin n) := by
  classical
  exact univ.filter (fun v => binomialCompositionOrder v = n)

noncomputable def binomialExpCoeff (n : ℕ) : MvPolynomial (Fin 2) ℚ := by
  classical
  exact ∑ k ∈ range (n + 1),
    C ((1 : ℚ) / (k.factorial : ℚ)) *
      ∑ v ∈ binomialPositiveCompositions n k,
        ∏ i : Fin k, binomialLogCoeff ((v i).val + 1)

noncomputable def binomialExpDropped (K : ℕ) (s t w : ℝ) : ℝ := by
  classical
  exact ∑ k ∈ range (K + 1), (1 / (k.factorial : ℝ)) *
    ∑ v ∈ (univ : Finset (Fin k → Fin K)).filter
        (fun v => K < binomialCompositionOrder v),
      (∏ i : Fin k, eval₂Hom (Rat.castHom ℝ)
        (fun a : Fin 2 => if a = 0 then s else t)
        (binomialLogCoeff ((v i).val + 1))) * w ^ binomialCompositionOrder v

theorem binomialCompositionOrder_eq {k n : ℕ} (v : Fin k → Fin n) :
    binomialCompositionOrder v = (∑ i : Fin k, (v i).val) + k := by
  simp [binomialCompositionOrder, sum_add_distrib]

theorem binomialComposition_length_le {k n : ℕ} (v : Fin k → Fin n) :
    k ≤ binomialCompositionOrder v := by
  rw [binomialCompositionOrder_eq]
  omega

theorem binomialComposition_part_le {k n : ℕ} (v : Fin k → Fin n) (i : Fin k) :
    (v i).val + 1 ≤ binomialCompositionOrder v := by
  exact single_le_sum (fun j _ => Nat.zero_le ((v j).val + 1)) (mem_univ i)

theorem binomialPositiveCompositions_empty (n k : ℕ) (hnk : n < k) :
    binomialPositiveCompositions n k = ∅ := by
  classical
  apply eq_empty_iff_forall_not_mem.mpr
  intro v hv
  have ho := (mem_filter.mp hv).2
  have hl := binomialComposition_length_le v
  omega

theorem binomialPositiveCompositions_zero_zero :
    binomialPositiveCompositions 0 0 = {Fin.elim0} := by
  classical
  ext v
  simp only [binomialPositiveCompositions, mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · intro _
    funext i
    exact Fin.elim0 i
  · intro _
    simp [binomialCompositionOrder]

theorem binomialPositiveCompositions_zero_length (n : ℕ) (hn : 0 < n) :
    binomialPositiveCompositions n 0 = ∅ := by
  classical
  apply eq_empty_iff_forall_not_mem.mpr
  intro v hv
  have he : binomialCompositionOrder v = n := (mem_filter.mp hv).2
  have hz : binomialCompositionOrder v = 0 := by
    unfold binomialCompositionOrder
    apply sum_eq_zero
    intro i hi
    exact Fin.elim0 i
  omega

theorem binomialPositiveCompositions_diagonal (n : ℕ) (hn : 0 < n) :
    binomialPositiveCompositions n n = {fun _ => (⟨0, hn⟩ : Fin n)} := by
  classical
  ext v
  simp only [binomialPositiveCompositions, mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · intro hv
    have hs : (∑ i : Fin n, (v i).val) = 0 := by
      rw [binomialCompositionOrder_eq] at hv
      omega
    funext i
    apply Fin.ext
    have hi := single_le_sum (fun j _ => Nat.zero_le (v j).val) (mem_univ i)
    change (v i).val = 0
    omega
  · intro hv
    rw [hv]
    simp [binomialCompositionOrder]

theorem binomialExpCoeff_zero : binomialExpCoeff 0 = 1 := by
  classical
  simp [binomialExpCoeff, binomialPositiveCompositions_zero_zero]

theorem binomialExpCoeff_one : binomialExpCoeff 1 = binomialLogCoeff 1 := by
  classical
  simp [binomialExpCoeff, sum_range_succ,
    binomialPositiveCompositions_zero_length 1 (by omega),
    binomialPositiveCompositions_diagonal 1 (by omega)]

theorem binomialExpDropped_zero (s t w : ℝ) : binomialExpDropped 0 s t w = 0 := by
  classical
  simp [binomialExpDropped, binomialCompositionOrder]

theorem binomialExpCoeff_eval (n : ℕ) (s t : ℝ) :
    eval₂Hom (Rat.castHom ℝ) (fun a : Fin 2 => if a = 0 then s else t)
      (binomialExpCoeff n) =
    ∑ k ∈ range (n + 1), (1 / (k.factorial : ℝ)) *
      ∑ v ∈ binomialPositiveCompositions n k,
        ∏ i : Fin k, eval₂Hom (Rat.castHom ℝ)
          (fun a : Fin 2 => if a = 0 then s else t)
          (binomialLogCoeff ((v i).val + 1)) := by
  classical
  simp [binomialExpCoeff, map_sum, map_prod]

theorem binomial_composition_sum_transport (K n k : ℕ) (hn : n ≤ K) (F : ℕ → ℝ) :
    (∑ v ∈ (univ : Finset (Fin k → Fin K)).filter
        (fun v => binomialCompositionOrder v = n),
      ∏ i : Fin k, F ((v i).val + 1)) =
    ∑ v ∈ binomialPositiveCompositions n k, ∏ i : Fin k, F ((v i).val + 1) := by
  classical
  let S := (univ : Finset (Fin k → Fin K)).filter
    (fun v => binomialCompositionOrder v = n)
  let shrink : ∀ v ∈ S, Fin k → Fin n := fun v hv i =>
    ⟨(v i).val, by
      have hb := binomialComposition_part_le v i
      have he := (mem_filter.mp hv).2
      omega⟩
  let embed : (Fin k → Fin n) → (Fin k → Fin K) := fun v i =>
    ⟨(v i).val, lt_of_lt_of_le (v i).isLt hn⟩
  have hs : ∀ v hv, shrink v hv ∈ binomialPositiveCompositions n k := by
    intro v hv
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    change (∑ i : Fin k, ((v i).val + 1)) = n
    exact (mem_filter.mp hv).2
  have he : ∀ v ∈ binomialPositiveCompositions n k, embed v ∈ S := by
    intro v hv
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    change (∑ i : Fin k, ((v i).val + 1)) = n
    exact (mem_filter.mp hv).2
  refine sum_bij' shrink (fun v _ => embed v) hs he ?_ ?_ ?_
  · intro v hv
    funext i
    apply Fin.ext
    rfl
  · intro v hv
    funext i
    apply Fin.ext
    rfl
  · intro v hv
    apply prod_congr rfl
    intro i hi
    rfl

theorem binomial_composition_weight_transport (K n k : ℕ) (hn : n ≤ K)
    (F : ℕ → ℝ) (w : ℝ) :
    (∑ v ∈ (univ : Finset (Fin k → Fin K)).filter
        (fun v => binomialCompositionOrder v = n),
      (∏ i : Fin k, F ((v i).val + 1)) * w ^ binomialCompositionOrder v) =
    (∑ v ∈ binomialPositiveCompositions n k, ∏ i : Fin k, F ((v i).val + 1)) * w ^ n := by
  classical
  rw [← binomial_composition_sum_transport K n k hn F, sum_mul]
  apply sum_congr rfl
  intro v hv
  rw [(mem_filter.mp hv).2]

theorem binomial_low_composition_collection (K : ℕ) (F c : ℕ → ℝ) (w : ℝ) :
    (∑ k ∈ range (K + 1), c k *
      ∑ v ∈ (univ : Finset (Fin k → Fin K)).filter
          (fun v => binomialCompositionOrder v ≤ K),
        (∏ i : Fin k, F ((v i).val + 1)) * w ^ binomialCompositionOrder v) =
    ∑ n ∈ range (K + 1),
      (∑ k ∈ range (n + 1), c k *
        ∑ v ∈ binomialPositiveCompositions n k, ∏ i : Fin k, F ((v i).val + 1)) * w ^ n := by
  classical
  have hfiber (k : ℕ) :
      (∑ v ∈ (univ : Finset (Fin k → Fin K)).filter
          (fun v => binomialCompositionOrder v ≤ K),
        (∏ i : Fin k, F ((v i).val + 1)) * w ^ binomialCompositionOrder v) =
      ∑ n ∈ range (K + 1),
        ∑ v ∈ (univ : Finset (Fin k → Fin K)).filter
            (fun v => binomialCompositionOrder v = n),
          (∏ i : Fin k, F ((v i).val + 1)) * w ^ binomialCompositionOrder v := by
    symm
    simpa only [mem_range, Nat.lt_succ_iff] using
      sum_fiberwise_eq_sum_filter (univ : Finset (Fin k → Fin K)) (range (K + 1))
        binomialCompositionOrder
        (fun v => (∏ i : Fin k, F ((v i).val + 1)) * w ^ binomialCompositionOrder v)
  calc
    _ = ∑ k ∈ range (K + 1), ∑ n ∈ range (K + 1),
        c k * (∑ v ∈ binomialPositiveCompositions n k,
          ∏ i : Fin k, F ((v i).val + 1)) * w ^ n := by
      apply sum_congr rfl
      intro k hk
      rw [hfiber, mul_sum]
      apply sum_congr rfl
      intro n hn
      rw [binomial_composition_weight_transport K n k (by have := mem_range.mp hn; omega)]
      ring
    _ = ∑ n ∈ range (K + 1), ∑ k ∈ range (K + 1),
        c k * (∑ v ∈ binomialPositiveCompositions n k,
          ∏ i : Fin k, F ((v i).val + 1)) * w ^ n := by rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro n hn
      rw [← sum_mul]
      congr 1
      symm
      apply sum_subset
      · intro k hk
        simp only [mem_range] at hn hk ⊢
        omega
      · intro k hk hkn
        have hnk : n < k := by simp only [mem_range] at hkn; omega
        rw [binomialPositiveCompositions_empty n k hnk]
        simp

theorem binomialExp_finite_collection (K : ℕ) (s t w : ℝ) :
    (∑ k ∈ range (K + 1),
      (∑ i ∈ Icc 1 K, eval₂Hom (Rat.castHom ℝ)
        (fun a : Fin 2 => if a = 0 then s else t) (binomialLogCoeff i) * w ^ i) ^ k /
        (k.factorial : ℝ)) =
    (∑ n ∈ Icc 0 K, eval₂Hom (Rat.castHom ℝ)
      (fun a : Fin 2 => if a = 0 then s else t) (binomialExpCoeff n) * w ^ n)
      + binomialExpDropped K s t w := by
  classical
  let F : ℕ → ℝ := fun i => eval₂Hom (Rat.castHom ℝ)
    (fun a : Fin 2 => if a = 0 then s else t) (binomialLogCoeff i)
  have hbase : (∑ i ∈ Icc 1 K, F i * w ^ i) =
      ∑ i : Fin K, F (i.val + 1) * w ^ (i.val + 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => F (i + 1) * w ^ (i + 1)) K]
    exact (range_succ_sum_Icc K (fun i => F i * w ^ i)).symm
  have hpow (k : ℕ) :
      (∑ i ∈ Icc 1 K, F i * w ^ i) ^ k / (k.factorial : ℝ) =
      (1 / (k.factorial : ℝ)) *
        ((∑ v ∈ (univ : Finset (Fin k → Fin K)).filter
            (fun v => binomialCompositionOrder v ≤ K),
          (∏ i : Fin k, F ((v i).val + 1)) * w ^ binomialCompositionOrder v) +
         (∑ v ∈ (univ : Finset (Fin k → Fin K)).filter
            (fun v => K < binomialCompositionOrder v),
          (∏ i : Fin k, F ((v i).val + 1)) * w ^ binomialCompositionOrder v)) := by
    rw [hbase, Fintype.sum_pow]
    simp_rw [prod_mul_distrib, prod_pow_eq_pow_sum]
    change (∑ v : Fin k → Fin K,
      (∏ i : Fin k, F ((v i).val + 1)) * w ^ binomialCompositionOrder v) /
      (k.factorial : ℝ) = _
    have hsplit := sum_filter_add_sum_filter_not
      (univ : Finset (Fin k → Fin K)) (fun v => binomialCompositionOrder v ≤ K)
      (fun v => (∏ i : Fin k, F ((v i).val + 1)) * w ^ binomialCompositionOrder v)
    simp only [not_le] at hsplit
    rw [← hsplit]
    ring
  change (∑ k ∈ range (K + 1), (∑ i ∈ Icc 1 K, F i * w ^ i) ^ k /
    (k.factorial : ℝ)) = _
  simp_rw [hpow, mul_add]
  rw [sum_add_distrib, binomial_low_composition_collection]
  have hr : range (K + 1) = Icc 0 K := by
    ext n
    simp only [mem_range, mem_Icc]
    omega
  change (∑ n ∈ range (K + 1),
    (∑ k ∈ range (n + 1), (1 / (k.factorial : ℝ)) *
      ∑ v ∈ binomialPositiveCompositions n k, ∏ i : Fin k, F ((v i).val + 1)) * w ^ n)
      + binomialExpDropped K s t w = _
  congr 1
  rw [hr]
  apply sum_congr rfl
  intro n hn
  rw [binomialExpCoeff_eval]

theorem binomialExpCoeff_reflect (n : ℕ) :
    eval₂Hom C (fun i : Fin 2 => if i = 0 then X 0 else -X 1) (binomialExpCoeff n) =
      binomialExpCoeff n := by
  classical
  simp only [binomialExpCoeff, map_sum, map_mul, eval₂Hom_C, map_prod,
    binomialLogCoeff_reflect]

theorem binomialExpCoeff_totalDegree (n : ℕ) :
    (binomialExpCoeff n).totalDegree ≤ 2 * n := by
  classical
  unfold binomialExpCoeff
  apply totalDegree_finsetSum_le
  intro k hk
  have hkn : k ≤ n := by have := mem_range.mp hk; omega
  have hp :
      (∑ v ∈ binomialPositiveCompositions n k,
        ∏ i : Fin k, binomialLogCoeff ((v i).val + 1)).totalDegree ≤ n + k := by
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
  have hc := totalDegree_mul (C ((1 : ℚ) / (k.factorial : ℚ)))
    (∑ v ∈ binomialPositiveCompositions n k,
      ∏ i : Fin k, binomialLogCoeff ((v i).val + 1))
  rw [totalDegree_C, zero_add] at hc
  exact hc.trans (hp.trans (by omega))

end Hardinian
