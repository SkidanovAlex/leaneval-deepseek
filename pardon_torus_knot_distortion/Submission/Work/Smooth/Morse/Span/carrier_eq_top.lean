import Mathlib
import Submission.Work.Smooth.Morse.Defs
import Submission.Work.SurgeryInvariance.API

/-!
# The winding span of the whole torus is everything

The longitude and meridian circles of a parametrised torus are essential, with winding vectors
`(1, 0)` and `(0, 1)` (`Work.CoreTopology.longitudeLift_winding`,
`Work.CoreTopology.meridianLift_winding`, `…longitudeCurve_essential`, `…meridianCurve_essential`).
Consequently the winding span of the whole surface is the whole of `ℚ² = H₁(T²; ℚ)`:

`Work.Smooth.Morse.WindingSpan_carrier_eq_top : WindingSpan P P.carrier = ⊤`.

This is used to make explicit that the winding span of the sublevel regions of a function on the
torus takes both extreme values `⊥` (below the range) and `⊤` (above it), which is why the global
form of the sweep statements is unsatisfiable — see
`Work.Smooth.Morse.Application.not_global_crossing`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.Morse

noncomputable section

/-- **The winding span of the whole surface `F = P.carrier` is `⊤`.**

The longitude circle has winding vector `(1, 0)` and the meridian circle `(0, 1)`, so the span
contains the standard basis of `ℚ × ℚ`. -/
theorem WindingSpan_carrier_eq_top (P : Work.CoreTopology.ParamTorus) :
    Work.SurgeryInvariance.WindingSpan P P.carrier = ⊤ := by
  have hlong : ((((1 : ℤ) : ℚ), ((0 : ℤ) : ℚ)) : ℚ × ℚ) ∈
      Work.SurgeryInvariance.windingVectors P P.carrier := by
    refine ⟨Work.CoreTopology.longitudeCurve P 0, fun t => (Work.CoreTopology.longitudeCurve P 0).mem t, ?_⟩
    rw [Work.SurgeryInvariance.windingOf_eq P _ (Work.CoreTopology.longitudeLift P 0),
      Work.CoreTopology.longitudeLift_winding]
  have hmer : ((((0 : ℤ) : ℚ), ((1 : ℤ) : ℚ)) : ℚ × ℚ) ∈
      Work.SurgeryInvariance.windingVectors P P.carrier := by
    refine ⟨Work.CoreTopology.meridianCurve P 0, fun t => (Work.CoreTopology.meridianCurve P 0).mem t, ?_⟩
    rw [Work.SurgeryInvariance.windingOf_eq P _ (Work.CoreTopology.meridianLift P 0),
      Work.CoreTopology.meridianLift_winding]
  have htop : (⊤ : Submodule ℚ (ℚ × ℚ)) ≤
      Submodule.span ℚ ({(((1 : ℚ), (0 : ℚ)) : ℚ × ℚ), ((0 : ℚ), (1 : ℚ))} : Set (ℚ × ℚ)) := by
    intro v _
    have hv : v = v.1 • ((((1 : ℚ), (0 : ℚ)) : ℚ × ℚ)) + v.2 • ((((0 : ℚ), (1 : ℚ)) : ℚ × ℚ)) := by
      ext <;> simp
    rw [hv]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ v.1 (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ v.2 (Submodule.subset_span (by simp)))
  have hsub : ({(((1 : ℚ), (0 : ℚ)) : ℚ × ℚ), ((0 : ℚ), (1 : ℚ))} : Set (ℚ × ℚ)) ⊆
      Work.SurgeryInvariance.windingVectors P P.carrier := by
    intro v hv
    rcases hv with rfl | rfl
    · simpa using hlong
    · simpa using hmer
  refine le_antisymm le_top ?_
  exact htop.trans (Submodule.span_mono hsub)

end

end Work.Smooth.Morse
