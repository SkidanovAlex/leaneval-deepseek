import Submission.Work.PinchFamily.Defs
import Submission.Work.BoxShrink.Bubble.Toolkit.regionEquivalent_union_zeroSpan

/-!
# A `CountedStep` transports loops

Every one of the three local models of `Work.PinchCounted.CountedStep` matches the loops of the first
region by loops of the second with the same winding vector, **provided the second region meets the
surface** — that hypothesis is needed only to produce a constant loop matching the loops of a piece
of vanishing winding span, and it is not removable (with `A' = ∅` and `A = Z` of vanishing span the
conclusion is false).

* case 1 (`RegionEquivalent`) is the conclusion;
* cases 2 and 3 decompose `A` into the disjoint open pieces `A'` and `Z` with `WindingSpan P Z = ⊥`;
  a loop of `A` lies wholly in one of them (`Work.SurgeryInvariance.Span.curve_subset_of_union`),
  and if it lies in `Z` its winding vanishes (case 2 by Pardon's Lemma 2 at the intermediate sphere,
  `Work.PinchCounted.CountedSweep.windingSpan_eq_bot_of_loops_match`) so a constant loop of `A'`
  matches it.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.PinchFamily

noncomputable section

/-- **A `CountedStep` matches the loops of its first region by loops of its second**, with the same
winding vector, as soon as the second region meets the surface. -/
theorem matched_of_countedStep {P : Work.CoreTopology.ParamTorus}
    (β : Work.CoreTopology.ClosedCurve P)
    {A A' : Set R3}
    (h : Work.PinchCounted.CountedStep P β A A')
    (hx : (A' ∩ P.carrier).Nonempty) :
    ∀ γ : Work.CoreTopology.ClosedCurve P, (∀ t : ℝ, γ t ∈ A) →
      ∃ γ' : Work.CoreTopology.ClosedCurve P, (∀ t : ℝ, γ' t ∈ A') ∧
        Work.SurgeryInvariance.windingOf P γ' = Work.SurgeryInvariance.windingOf P γ := by
  obtain ⟨a, haA', hacar⟩ := hx
  have hx' : ∃ a : R3, a ∈ A' ∧ a ∈ P.carrier := ⟨a, haA', hacar⟩
  rcases h with h | ⟨Z, S, hZopen, hAopen, hA'open, hclean, hcount, hmatch, hcase⟩ | hstep
  · exact h.1
  · have hspan : Work.SurgeryInvariance.WindingSpan P Z = ⊥ :=
      Work.PinchCounted.CountedSweep.windingSpan_eq_bot_of_loops_match hclean hcount hmatch
    rcases hcase with ⟨hAeq, hdisj⟩ | ⟨hA'eq, hdisj⟩
    · rw [hAeq]
      exact (Work.BoxShrink.Bubble.Toolkit.regionEquivalent_union_zeroSpan hA'open hZopen hdisj
        hspan hx').1
    · intro γ hγ
      exact ⟨γ, fun t => by rw [hA'eq]; exact Or.inl (hγ t), rfl⟩
  · obtain ⟨Z, hspan, hAopen, hA'open, hZopen, hcase⟩ := hstep
    rcases hcase with ⟨hAeq, hdisj⟩ | ⟨hA'eq, hdisj⟩
    · rw [hAeq]
      exact (Work.BoxShrink.Bubble.Toolkit.regionEquivalent_union_zeroSpan hA'open hZopen hdisj
        hspan hx').1
    · intro γ hγ
      exact ⟨γ, fun t => by rw [hA'eq]; exact Or.inl (hγ t), rfl⟩

end

end Work.PinchFamily
