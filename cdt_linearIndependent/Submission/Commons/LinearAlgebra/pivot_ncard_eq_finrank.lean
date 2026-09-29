import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.LinearAlgebra

open scoped BigOperators

section

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The set of pivot indices of a submodule `I ≤ (ι → K)`: the indices `i` such that some
element of `I` vanishes strictly before `i` and is nonzero at `i`. -/
def pivotSet (I : Submodule K (ι → K)) : Set ι :=
  {i | ∃ f ∈ I, f i ≠ 0 ∧ ∀ j, j < i → f j = 0}

/-- For a pivot index `i` of `I`, a chosen element of `I` witnessing that `i` is a pivot: it
vanishes at all `j < i` and is nonzero at `i`. -/
noncomputable def pivotVec (I : Submodule K (ι → K)) (i : pivotSet I) : I :=
  ⟨Classical.choose i.2, (Classical.choose_spec i.2).1⟩

omit [Fintype ι] in
lemma pivotVec_self (I : Submodule K (ι → K)) (i : pivotSet I) :
    (pivotVec I i).1 i.1 ≠ 0 :=
  (Classical.choose_spec i.2).2.1

omit [Fintype ι] in
lemma pivotVec_lt (I : Submodule K (ι → K)) (i : pivotSet I) {j : ι} (hj : j < i.1) :
    (pivotVec I i).1 j = 0 :=
  (Classical.choose_spec i.2).2.2 j hj

/-- The pivot vectors are linearly independent. -/
lemma pivotVec_linearIndependent (I : Submodule K (ι → K)) :
    LinearIndependent K (pivotVec I) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra h
  simp only [not_forall] at h
  obtain ⟨k, hk⟩ := h
  have hT : (Finset.univ.filter (fun k : pivotSet I => c k ≠ 0)).Nonempty :=
    ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩
  set i0 := (Finset.univ.filter (fun k : pivotSet I => c k ≠ 0)).min' hT with hi0
  have hi0mem : i0 ∈ Finset.univ.filter (fun k : pivotSet I => c k ≠ 0) :=
    Finset.min'_mem _ _
  have hi0ne : c i0 ≠ 0 := (Finset.mem_filter.mp hi0mem).2
  have hval : (∑ k, c k • (pivotVec I k).1) = 0 := by
    have := congrArg (Submodule.subtype I) hc
    simpa using this
  have hval2 : (∑ k, c k * (pivotVec I k).1 i0.1) = 0 := by
    have := congrFun hval i0.1
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
  have hsingle : (∑ k, c k * (pivotVec I k).1 i0.1)
      = c i0 * (pivotVec I i0).1 i0.1 := by
    refine Finset.sum_eq_single i0 ?_ ?_
    · intro k _ hkne
      by_cases hkT : k ∈ Finset.univ.filter (fun k : pivotSet I => c k ≠ 0)
      · have hle : i0 ≤ k := Finset.min'_le _ _ hkT
        have hlt : i0.1 < k.1 := lt_of_le_of_ne hle (fun heq => hkne (Subtype.ext heq.symm))
        rw [pivotVec_lt I k hlt, mul_zero]
      · have hck : c k = 0 := by
          by_contra hck
          exact hkT (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hck⟩)
        rw [hck, zero_mul]
    · intro hmem
      exact absurd (Finset.mem_univ i0) hmem
  rw [hsingle] at hval2
  exact hi0ne (mul_eq_zero.mp hval2 |>.resolve_right (pivotVec_self I i0))

/-- An element of `I` vanishing at all pivot indices is zero. -/
lemma eq_zero_of_forall_pivotSet (I : Submodule K (ι → K)) (f : I)
    (h : ∀ i : pivotSet I, f.1 i.1 = 0) : f = 0 := by
  classical
  apply Subtype.ext
  funext k
  by_contra hk
  have hT : (Finset.univ.filter (fun k => f.1 k ≠ 0)).Nonempty :=
    ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩
  set k0 := (Finset.univ.filter (fun k => f.1 k ≠ 0)).min' hT with hk0
  have hk0mem : k0 ∈ Finset.univ.filter (fun k => f.1 k ≠ 0) := Finset.min'_mem _ _
  have hk0ne : f.1 k0 ≠ 0 := (Finset.mem_filter.mp hk0mem).2
  have hk0piv : k0 ∈ pivotSet I :=
    ⟨f.1, f.2, hk0ne, fun j hj => by
      by_contra hjne
      have hjmem : j ∈ Finset.univ.filter (fun k => f.1 k ≠ 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjne⟩
      have hle : k0 ≤ j := Finset.min'_le _ _ hjmem
      exact absurd hj (not_lt.mpr hle)⟩
  exact hk0ne (h ⟨k0, hk0piv⟩)

/-- Restriction of an element of `I` to the pivot indices, as a linear map. -/
noncomputable def pivotRestrict (I : Submodule K (ι → K)) :
    I →ₗ[K] (pivotSet I → K) :=
  (LinearMap.funLeft K K (Subtype.val : pivotSet I → ι)).comp (Submodule.subtype I)

lemma pivotRestrict_injective (I : Submodule K (ι → K)) :
    Function.Injective (pivotRestrict I) := by
  intro f g h
  have hfg : f - g = 0 := by
    apply eq_zero_of_forall_pivotSet
    intro i
    have h1 : f.1 i.1 = g.1 i.1 := by
      have := congrFun h i
      simpa [pivotRestrict, LinearMap.funLeft_apply] using this
    rw [Submodule.coe_sub, Pi.sub_apply, h1, sub_self]
  exact sub_eq_zero.mp hfg

lemma pivot_ncard_le_finrank (I : Submodule K (ι → K)) :
    (pivotSet I).ncard ≤ Module.finrank K I := by
  classical
  have h := (pivotVec_linearIndependent I).fintype_card_le_finrank
  rw [Set.fintypeCard_eq_ncard] at h
  exact h

lemma finrank_le_pivot_ncard (I : Submodule K (ι → K)) :
    Module.finrank K I ≤ (pivotSet I).ncard := by
  classical
  have h := LinearMap.finrank_le_finrank_of_injective (pivotRestrict_injective I)
  rw [Module.finrank_fintype_fun_eq_card, Set.fintypeCard_eq_ncard] at h
  exact h

end

theorem pivot_ncard_eq_finrank {K : Type*} [Field K] {ι : Type*} [Fintype ι] [LinearOrder ι]
    (I : Submodule K (ι → K)) :
    (Set.ncard {i : ι | ∃ f ∈ I, f i ≠ 0 ∧ ∀ j, j < i → f j = 0}) = Module.finrank K I := by
  show (pivotSet I).ncard = Module.finrank K I
  exact le_antisymm (pivot_ncard_le_finrank I) (finrank_le_pivot_ncard I)

end Commons.LinearAlgebra