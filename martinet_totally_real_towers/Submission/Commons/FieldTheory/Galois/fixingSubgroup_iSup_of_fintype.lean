import Mathlib.FieldTheory.Galois.Basic

namespace Commons.FieldTheory.Galois

/-- The fixing subgroup of a finite supremum of intermediate fields is the intersection
of their fixing subgroups. This is the order-reversing-Galois-correspondence fact that
`fixingSubgroup` turns the finite supremum on the left into the meet on the right. -/
lemma fixingSubgroup_iSup_of_fintype {F E : Type*} [Field F] [Field E] [Algebra F E]
    {ι : Type*} [Fintype ι] (t : ι → IntermediateField F E) :
    (⨆ i, t i).fixingSubgroup = ⨅ i, (t i).fixingSubgroup := by
  apply le_antisymm
  · -- the sup fixes everything: for each i, t i ≤ ⨆ t, and fixingSubgroup is antitone
    refine le_iInf ?_
    intro i
    exact IntermediateField.fixingSubgroup_antitone (le_iSup t i)
  · -- an automorphism fixing each t i fixes their sup
    rw [← IntermediateField.le_iff_le (H := ⨅ i, (t i).fixingSubgroup) (K := ⨆ i, t i)]
    refine iSup_le ?_
    intro i
    rw [IntermediateField.le_iff_le (H := ⨅ j, (t j).fixingSubgroup) (K := t i)]
    exact iInf_le (fun j => (t j).fixingSubgroup) i

end Commons.FieldTheory.Galois
