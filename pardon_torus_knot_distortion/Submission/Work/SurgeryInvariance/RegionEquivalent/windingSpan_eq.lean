import Mathlib
import Submission.Work.SurgeryInvariance.Defs

namespace Work.SurgeryInvariance.RegionEquivalent

open Set

/-- **The realised winding vectors agree for `RegionEquivalent` regions.**

`RegionEquivalent P X Y` says that every closed curve of the torus contained in `X` is
matched, at the level of winding vectors, by a closed curve contained in `Y`, and conversely.
Hence the set of winding vectors realised in `X` and the set realised in `Y` coincide: this is
the precise sense in which the curve-level relation of `RegionEquivalent` captures "the same
`H₁`-information inside the region". -/
theorem windingVectors_eq {P : Work.CoreTopology.ParamTorus}
    {X Y : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (h : Work.SurgeryInvariance.RegionEquivalent P X Y) :
    Work.SurgeryInvariance.windingVectors P X = Work.SurgeryInvariance.windingVectors P Y := by
  ext v
  constructor
  · rintro ⟨γ, hγ, hv⟩
    obtain ⟨γ', hγ', hw⟩ := h.1 γ hγ
    exact ⟨γ', hγ', by rw [hw, hv]⟩
  · rintro ⟨γ, hγ, hv⟩
    obtain ⟨γ', hγ', hw⟩ := h.2 γ hγ
    exact ⟨γ', hγ', by rw [hw, hv]⟩

/-- **The winding span is an invariant of the region-equivalence relation.**

Immediate from `windingVectors_eq`: the two spans are the `ℚ`-spans of the same set of
winding vectors in `ℚ² = H₁(T²; ℚ)`.  This is the step that makes `WindingSpan P ·` constant
along the surgery-free part of a sweep, so that the only thing left to control is a single
`2`-surgery. -/
theorem windingSpan_eq {P : Work.CoreTopology.ParamTorus}
    {X Y : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (h : Work.SurgeryInvariance.RegionEquivalent P X Y) :
    Work.SurgeryInvariance.WindingSpan P X = Work.SurgeryInvariance.WindingSpan P Y := by
  rw [Work.SurgeryInvariance.WindingSpan, Work.SurgeryInvariance.WindingSpan,
    windingVectors_eq h]

end Work.SurgeryInvariance.RegionEquivalent
