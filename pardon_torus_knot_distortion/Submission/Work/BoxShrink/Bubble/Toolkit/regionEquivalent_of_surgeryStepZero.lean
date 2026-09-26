import Mathlib
import Submission.Work.BoxShrink.Bubble.Basic
import Submission.Work.BoxShrink.Bubble.Toolkit.windingOf_eq_zero_of_span_bot
import Submission.Work.BoxShrink.Bubble.Toolkit.regionEquivalent_union_zeroSpan

namespace Work.BoxShrink.Bubble.Toolkit

open LeanEval.KnotTheory.PardonDistortion
open Set

/-- `RegionEquivalent` is symmetric: the definition is the conjunction of the two transport
conditions, so swapping the two regions just swaps the two components. -/
theorem regionEquivalent_symm
    {P : Work.CoreTopology.ParamTorus} {X Y : Set R3}
    (h : Work.SurgeryInvariance.RegionEquivalent P X Y) :
    Work.SurgeryInvariance.RegionEquivalent P Y X :=
  ⟨h.2, h.1⟩

/-- **A single `2`-surgery with vanishing winding content does not change the loops of a
region.**

A `SurgeryStepZero P A A'` writes one of the two regions as the other one together with a piece
`Z` which is open in the surface, disjoint from the other region, and contains no essential loop
(`WindingSpan P Z = ⊥`).  Adding such a piece does not change the closed curves with their winding
vectors (`regionEquivalent_union_zeroSpan`): a closed curve of the surface inside the union lies
either in the unchanged region or in `Z`, and in the second case its winding vanishes and it is
matched by a constant curve at a point of the unchanged region.  Hence `A` and `A'` are
`RegionEquivalent`. -/
theorem regionEquivalent_of_surgeryStepZero
    {P : Work.CoreTopology.ParamTorus}
    {A A' : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (h : Work.SurgeryInvariance.SurgeryStepZero P A A')
    (hAc : A ⊆ P.carrier) (hA'c : A' ⊆ P.carrier)
    (hne : A.Nonempty) (hne' : A'.Nonempty) :
    Work.SurgeryInvariance.RegionEquivalent P A A' := by
  obtain ⟨Z, hZspan, hAopen, hA'open, hZopen, hcase⟩ := h
  rcases hcase with ⟨hAsub, hdisj⟩ | ⟨hA'sub, hdisj⟩
  · -- `A = A' ∪ Z`: the unchanged region is `A'`.
    have ha : ∃ a : R3, a ∈ A' ∧ a ∈ P.carrier := by
      obtain ⟨a, ha⟩ := hne'
      exact ⟨a, ha, hA'c ha⟩
    have hstep := regionEquivalent_union_zeroSpan (P := P) (A := A') (Z := Z)
      hA'open hZopen hdisj hZspan ha
    rw [hAsub]
    exact hstep
  · -- `A' = A ∪ Z`: the unchanged region is `A`, and we swap the equivalence.
    have ha : ∃ a : R3, a ∈ A ∧ a ∈ P.carrier := by
      obtain ⟨a, ha⟩ := hne
      exact ⟨a, ha, hAc ha⟩
    have hstep := regionEquivalent_union_zeroSpan (P := P) (A := A) (Z := Z)
      hAopen hZopen hdisj hZspan ha
    rw [hA'sub]
    exact regionEquivalent_symm hstep

end Work.BoxShrink.Bubble.Toolkit
