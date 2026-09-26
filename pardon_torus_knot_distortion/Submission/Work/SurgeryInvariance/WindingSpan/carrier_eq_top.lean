import Mathlib
import Submission.Work.SurgeryInvariance.Defs

/-!
# The winding span of the whole torus is everything

The winding span `WindingSpan P X` of a region `X ⊆ ℝ³` is the `ℚ`-span in `ℚ² = H₁(T²; ℚ)` of
the winding vectors of the closed curves of `F = P.carrier` whose image lies in `X`.  Every closed
curve of `F` lies in `F`, so the winding span of the full carrier is the span of the winding
vectors of *all* closed curves of the torus.

The two basic curves of the torus already exhibit the two generators of `H₁(T²; ℚ)`:
`longitudeCurve P 0` has winding vector `(1, 0)` and `meridianCurve P 0` has winding vector
`(0, 1)`.  Their span is therefore all of `ℚ²`, which is the statement below.
-/

open LeanEval.KnotTheory.PardonDistortion

namespace Work.SurgeryInvariance.WindingSpan

theorem carrier_eq_top (P : Work.CoreTopology.ParamTorus) :
    Work.SurgeryInvariance.WindingSpan P P.carrier = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro v
  -- the longitude circle has winding vector `(1, 0)`
  have hL : ((((1 : ℤ) : ℚ), ((0 : ℤ) : ℚ)) : ℚ × ℚ) ∈
      Work.SurgeryInvariance.WindingSpan P P.carrier := by
    apply Submodule.subset_span
    refine ⟨Work.CoreTopology.longitudeCurve P 0,
      fun t => (Work.CoreTopology.longitudeCurve P 0).mem t, ?_⟩
    have h := (Work.SurgeryInvariance.windingOf_eq P (Work.CoreTopology.longitudeCurve P 0)
      (Work.CoreTopology.longitudeLift P 0)).trans (Work.CoreTopology.longitudeLift_winding P 0)
    rw [h]
  -- the meridian circle has winding vector `(0, 1)`
  have hM : ((((0 : ℤ) : ℚ), ((1 : ℤ) : ℚ)) : ℚ × ℚ) ∈
      Work.SurgeryInvariance.WindingSpan P P.carrier := by
    apply Submodule.subset_span
    refine ⟨Work.CoreTopology.meridianCurve P 0,
      fun t => (Work.CoreTopology.meridianCurve P 0).mem t, ?_⟩
    have h := (Work.SurgeryInvariance.windingOf_eq P (Work.CoreTopology.meridianCurve P 0)
      (Work.CoreTopology.meridianLift P 0)).trans (Work.CoreTopology.meridianLift_winding P 0)
    rw [h]
  -- every vector of `ℚ²` is a combination of the two
  have hv : v = v.1 • ((((1 : ℤ) : ℚ), ((0 : ℤ) : ℚ)) : ℚ × ℚ) +
      v.2 • ((((0 : ℤ) : ℚ), ((1 : ℤ) : ℚ)) : ℚ × ℚ) := by
    ext <;> simp
  rw [hv]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ hL) (Submodule.smul_mem _ _ hM)

end Work.SurgeryInvariance.WindingSpan
