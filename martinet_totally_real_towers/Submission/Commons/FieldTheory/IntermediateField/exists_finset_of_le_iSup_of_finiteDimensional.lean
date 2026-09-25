import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Order.CompletePartialOrder

noncomputable section
open scoped BigOperators

namespace Commons.FieldTheory.IntermediateField

lemma exists_finset_of_le_iSup_of_finiteDimensional
    {F E : Type*} [Field F] [Field E] [Algebra F E] {ι : Type*} {f : ι → IntermediateField F E}
    {K : IntermediateField F E} [FiniteDimensional F ↥K] (hK : K ≤ ⨆ i, f i) :
    ∃ s : Finset ι, K ≤ ⨆ i ∈ s, f i := by
  classical
  -- K is a finitely generated module over F; pick a finite generating Finset.
  obtain ⟨S0, hS0⟩ := (Module.Finite.fg_top (R := F) (M := ↥K) : (⊤ : Submodule F ↥K).FG)
  -- For each element of K, membership in the join is witnessed by a finite sub-join.
  have mem_of (g : ↥K) : ∃ t : Finset ι, (g : E) ∈ ⨆ i ∈ t, f i := by
    exact IntermediateField.exists_finset_of_mem_iSup (f := f)
      ((SetLike.le_def.mp hK) g.2)
  choose t ht using mem_of
  let s : Finset ι := S0.biUnion t
  -- each generator lies in the finite join indexed by s
  have hgen (g : ↥K) (hg : g ∈ S0) : (g : E) ∈ ⨆ i ∈ s, f i := by
    have hsub : ((t g : Finset ι) : Set ι) ⊆ (s : Set ι) := by
      intro a ha
      exact Finset.mem_biUnion.mpr ⟨g, hg, ha⟩
    exact (SetLike.le_def.mp (iSup_le_iSup_of_subset (s := (t g : Set ι)) (t := (s : Set ι)) hsub)) (ht g)
  refine ⟨s, ?_⟩
  intro x hx
  let J : IntermediateField F E := ⨆ i ∈ s, f i
  let u : ↥K := ⟨x, hx⟩
  have hu' : u ∈ Submodule.span F (S0 : Set ↥K) := by
    rw [hS0]
    exact Submodule.mem_top
  obtain ⟨f, hfs, hc⟩ := (Submodule.mem_span_finset (R := F) (s := S0)).mp hu'
  -- push the linear-combination identity down to E
  have hce : (∑ a ∈ S0, f a • (K.val a)) = x := by
    have hmap := congrArg K.val hc
    rw [map_sum] at hmap
    simpa [u] using hmap
  -- x, written as a combination, lies in the finite join
  have hxL : (∑ a ∈ S0, f a • (K.val a)) ∈ J := by
    refine J.toSubfield.toAddSubgroup.sum_mem (t := S0) (f := fun a => f a • (K.val a)) ?_
    intro a ha
    rw [Algebra.smul_def]
    exact J.mul_mem (J.algebraMap_mem (f a)) (by simpa using hgen a ha)
  exact (hce ▸ hxL)

end Commons.FieldTheory.IntermediateField