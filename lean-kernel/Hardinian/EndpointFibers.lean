import Hardinian.SeparatedPathFamily
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Sigma.Basic
import Mathlib.Logic.Equiv.Defs

open scoped BigOperators

namespace Hardinian

abbrev EndpointIndex (k : ℕ) := Fin k ↪o Fin (k + 2)

abbrev EndpointSet (k : ℕ) := {S : Finset (Fin (k + 2)) // S.card = k}

def DisjointEndpointTuple {k : ℕ} (u v : EndpointIndex k) :=
  {P : ∀ i : Fin k, GridPath (u i).val (v i).val //
    ∀ i j : Fin k, i ≠ j → VertexDisjoint (P i) (P j)}

def IndexedEndpointFamily (k : ℕ) :=
  Σ u : EndpointIndex k, Σ v : EndpointIndex k, DisjointEndpointTuple u v

def familySourceIndex {k : ℕ} (F : OrderedPathFamily k) : EndpointIndex k :=
  OrderEmbedding.ofStrictMono (fun t => (F.1 t).1) F.2.1

def familySinkIndex {k : ℕ} (F : OrderedPathFamily k) : EndpointIndex k :=
  OrderEmbedding.ofStrictMono (fun t => (F.1 t).2.1) (family_sinks_strictMono k F)

def familyToEndpointIndex {k : ℕ} (F : OrderedPathFamily k) : IndexedEndpointFamily k :=
  ⟨familySourceIndex F, familySinkIndex F, ⟨fun t => (F.1 t).2.2, F.2.2⟩⟩

def endpointIndexToFamily {k : ℕ} (E : IndexedEndpointFamily k) : OrderedPathFamily k :=
  ⟨fun t => ⟨E.1 t, E.2.1 t, E.2.2.1 t⟩, E.1.strictMono, E.2.2.2⟩

theorem endpointIndexToFamily_familyToEndpointIndex {k : ℕ} (F : OrderedPathFamily k) :
    endpointIndexToFamily (familyToEndpointIndex F) = F := by
  apply Subtype.ext
  funext t
  change (⟨(F.1 t).1, (F.1 t).2.1, (F.1 t).2.2⟩ : BoundedGridPath k) = F.1 t
  simp only [Sigma.eta]

theorem familyToEndpointIndex_endpointIndexToFamily {k : ℕ} (E : IndexedEndpointFamily k) :
    familyToEndpointIndex (endpointIndexToFamily E) = E := by
  rcases E with ⟨u, v, P⟩
  rfl

def familyEndpointIndexEquiv (k : ℕ) : OrderedPathFamily k ≃ IndexedEndpointFamily k where
  toFun := familyToEndpointIndex
  invFun := endpointIndexToFamily
  left_inv := endpointIndexToFamily_familyToEndpointIndex
  right_inv := familyToEndpointIndex_endpointIndexToFamily

def disjointEndpointTupleCongr {k : ℕ} {u u' v v' : EndpointIndex k}
    (hu : u = u') (hv : v = v') : DisjointEndpointTuple u v ≃ DisjointEndpointTuple u' v' := by
  subst u'
  subst v'
  exact Equiv.refl _

noncomputable def endpointEnum {k : ℕ} (S : EndpointSet k) : EndpointIndex k :=
  S.1.orderEmbOfFin S.2

def endpointSetOfIndex {k : ℕ} (u : EndpointIndex k) : EndpointSet k :=
  ⟨Finset.univ.image u, by
    rw [Finset.card_image_of_injective _ u.injective, Finset.card_univ, Fintype.card_fin]⟩

theorem endpointEnum_image {k : ℕ} (u : EndpointIndex k) :
    endpointEnum (endpointSetOfIndex u) = u := by
  apply Eq.symm
  apply Finset.orderEmbOfFin_unique'
  intro t
  exact Finset.mem_image.mpr ⟨t, Finset.mem_univ t, rfl⟩

theorem endpointSetOfIndex_enum {k : ℕ} (S : EndpointSet k) :
    endpointSetOfIndex (endpointEnum S) = S := by
  apply Subtype.ext
  apply Finset.ext
  intro x
  change x ∈ Finset.univ.image (endpointEnum S) ↔ x ∈ S.1
  constructor
  · intro hx
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.orderEmbOfFin_mem S.1 S.2 t
  · intro hx
    obtain ⟨t, ht⟩ := (S.1.orderIsoOfFin S.2).surjective ⟨x, hx⟩
    exact Finset.mem_image.mpr ⟨t, Finset.mem_univ t, congrArg Subtype.val ht⟩

noncomputable def endpointIndexSetEquiv (k : ℕ) : EndpointIndex k ≃ EndpointSet k where
  toFun := endpointSetOfIndex
  invFun := endpointEnum
  left_inv := endpointEnum_image
  right_inv := endpointSetOfIndex_enum

noncomputable def EndpointPathFiber {k : ℕ} (S T : EndpointSet k) :=
  DisjointEndpointTuple (endpointEnum S) (endpointEnum T)

noncomputable def EndpointFiberFamily (k : ℕ) :=
  Σ S : EndpointSet k, Σ T : EndpointSet k, EndpointPathFiber S T

noncomputable def endpointIndexFiberSetEquiv (k : ℕ) :
    IndexedEndpointFamily k ≃ EndpointFiberFamily k :=
  Equiv.sigmaCongr (endpointIndexSetEquiv k) (fun u =>
    Equiv.sigmaCongr (endpointIndexSetEquiv k) (fun v =>
      disjointEndpointTupleCongr (endpointEnum_image u).symm (endpointEnum_image v).symm))

noncomputable def familyEndpointFiberEquiv (k : ℕ) :
    OrderedPathFamily k ≃ EndpointFiberFamily k :=
  (familyEndpointIndexEquiv k).trans (endpointIndexFiberSetEquiv k)

theorem endpointFiber_inverse_left (k : ℕ) (F : OrderedPathFamily k) :
    (familyEndpointFiberEquiv k).symm (familyEndpointFiberEquiv k F) = F :=
  (familyEndpointFiberEquiv k).symm_apply_apply F

theorem endpointFiber_inverse_right (k : ℕ) (E : EndpointFiberFamily k) :
    familyEndpointFiberEquiv k ((familyEndpointFiberEquiv k).symm E) = E :=
  (familyEndpointFiberEquiv k).apply_symm_apply E

theorem familyEndpointFiber_source (k : ℕ) (F : OrderedPathFamily k) :
    (familyEndpointFiberEquiv k F).1.1 = Finset.univ.image (fun t => (F.1 t).1) := rfl

theorem familyEndpointFiber_sink (k : ℕ) (F : OrderedPathFamily k) :
    (familyEndpointFiberEquiv k F).2.1.1 = Finset.univ.image (fun t => (F.1 t).2.1) := rfl

theorem endpointSet_finite (k : ℕ) : Finite (EndpointSet k) := by
  infer_instance

theorem endpointPathFiber_finite {k : ℕ} (S T : EndpointSet k) :
    Finite (EndpointPathFiber S T) := by
  letI := pathFamily_finite k
  apply Finite.of_injective (fun P : EndpointPathFiber S T =>
    (familyEndpointFiberEquiv k).symm ⟨S, T, P⟩)
  intro P Q h
  have hST := (familyEndpointFiberEquiv k).symm.injective h
  have hT := sigma_mk_injective
    (β := fun S : EndpointSet k => Σ T : EndpointSet k, EndpointPathFiber S T) (i := S) hST
  exact sigma_mk_injective (β := fun T : EndpointSet k => EndpointPathFiber S T) (i := T) hT

theorem family_card_eq_endpoint_fiber_sum (k : ℕ) :
    Nat.card (OrderedPathFamily k) =
      ∑ S : EndpointSet k, ∑ T : EndpointSet k, Nat.card (EndpointPathFiber S T) := by
  letI (S T : EndpointSet k) : Finite (EndpointPathFiber S T) := endpointPathFiber_finite S T
  letI (S T : EndpointSet k) : Fintype (EndpointPathFiber S T) := Fintype.ofFinite _
  calc
    Nat.card (OrderedPathFamily k) = Nat.card (EndpointFiberFamily k) :=
      Nat.card_congr (familyEndpointFiberEquiv k)
    _ = ∑ S : EndpointSet k, Nat.card (Σ T : EndpointSet k, EndpointPathFiber S T) :=
      Nat.card_sigma
    _ = ∑ S : EndpointSet k, ∑ T : EndpointSet k, Nat.card (EndpointPathFiber S T) := by
      apply Finset.sum_congr rfl
      intro S hS
      exact Nat.card_sigma

theorem endpointSet_zero_eq (S : EndpointSet 0) : S.1 = ∅ :=
  Finset.card_eq_zero.mp S.2

theorem endpointSet_zero_card : Nat.card (EndpointSet 0) = 1 := by
  apply Nat.card_eq_one_iff_unique.mpr
  constructor
  · constructor
    intro S T
    apply Subtype.ext
    exact (endpointSet_zero_eq S).trans (endpointSet_zero_eq T).symm
  · exact ⟨⟨∅, rfl⟩⟩

theorem endpointPathFiber_zero_card (S T : EndpointSet 0) :
    Nat.card (EndpointPathFiber S T) = 1 := by
  apply Nat.card_eq_one_iff_unique.mpr
  constructor
  · constructor
    intro P Q
    apply Subtype.ext
    funext t
    exact Fin.elim0 t
  · exact ⟨⟨fun t => Fin.elim0 t, fun i => Fin.elim0 i⟩⟩

theorem endpointFiberFamily_zero_card : Nat.card (EndpointFiberFamily 0) = 1 :=
  (Nat.card_congr (familyEndpointFiberEquiv 0)).symm.trans pathFamily_zero_card

end Hardinian
