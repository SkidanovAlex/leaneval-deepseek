import Mathlib
import Submission.Work.BoxShrink.Bubble.Basic

namespace Work.BoxShrink.Bubble.Toolkit

open LeanEval.KnotTheory.PardonDistortion

/-!
# `RegionEquivalent` is exactly the equality of the realised winding sets

`Work.SurgeryInvariance.RegionEquivalent P X Y` says that every loop of the surface inside `X`
can be replaced by a loop inside `Y` with the same winding vector, and conversely;
`Work.BoxShrink.Bubble.RealizedWindings P X` is the set of winding vectors realised by loops
inside `X`.  The two are therefore interdefinable:

* if every loop of `X` transports to a loop of `Y` with the same winding, then the realised
  winding sets agree (both inclusions);
* conversely, if the realised winding sets agree, then a loop of `X` with winding `k` exhibits
  `k ∈ RealizedWindings P X = RealizedWindings P Y`, i.e. a loop of `Y` with winding `k`.

Nothing about the geometry of the regions is used: both notions are transcriptions of each other
through the map `γ ↦ windingOf P γ`.
-/

/-- The membership-level form of the inclusion of realised winding sets: it says exactly that
every loop of the surface inside `A` has a counterpart inside `B` with the same winding vector.
This is the shape in which the transport property of `RegionEquivalent` is used. -/
theorem subset_realizedWindings_iff
    {P : Work.CoreTopology.ParamTorus} {A B : Set R3} :
    RealizedWindings P A ⊆ RealizedWindings P B ↔
      ∀ γ : Work.CoreTopology.ClosedCurve P, (∀ t : ℝ, γ t ∈ A) →
        ∃ γ' : Work.CoreTopology.ClosedCurve P, (∀ t : ℝ, γ' t ∈ B) ∧
          Work.SurgeryInvariance.windingOf P γ' = Work.SurgeryInvariance.windingOf P γ := by
  constructor
  · intro h γ hγ
    exact h ⟨γ, hγ, rfl⟩
  · rintro h k ⟨γ, hγ, rfl⟩
    exact h γ hγ

theorem regionEquivalent_iff_realizedWindings
    (P : Work.CoreTopology.ParamTorus) (X Y : Set LeanEval.KnotTheory.PardonDistortion.R3) :
    Work.SurgeryInvariance.RegionEquivalent P X Y ↔
      Work.BoxShrink.Bubble.RealizedWindings P X =
        Work.BoxShrink.Bubble.RealizedWindings P Y := by
  constructor
  · intro h
    refine Set.Subset.antisymm ?_ ?_
    · rintro k ⟨γ, hγ, rfl⟩
      obtain ⟨γ', hγ', hw⟩ := h.1 γ hγ
      exact ⟨γ', hγ', hw⟩
    · rintro k ⟨γ, hγ, rfl⟩
      obtain ⟨γ', hγ', hw⟩ := h.2 γ hγ
      exact ⟨γ', hγ', hw⟩
  · intro h
    refine ⟨?_, ?_⟩
    · intro γ hγ
      have hm : Work.SurgeryInvariance.windingOf P γ ∈ RealizedWindings P X := ⟨γ, hγ, rfl⟩
      rw [h] at hm
      exact hm
    · intro γ hγ
      have hm : Work.SurgeryInvariance.windingOf P γ ∈ RealizedWindings P Y := ⟨γ, hγ, rfl⟩
      rw [← h] at hm
      exact hm

end Work.BoxShrink.Bubble.Toolkit
