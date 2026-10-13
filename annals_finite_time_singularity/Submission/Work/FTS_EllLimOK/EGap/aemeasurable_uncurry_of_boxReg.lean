import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_EllLimOK.BoxReg
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.EGap

/-- `BoxReg δ` knows `δ` is jointly `C²` on every closed box `[a,b] × [0,π/2]` with `0 < a ≤ b`;
these boxes cover the region `(0,∞) × [0,π/2]` *locally* (a neighbourhood of any of its points
meets the region only inside one box), so `δ` is continuous on the region.  Hence it is Borel
measurable viewed as a function on the subtype, and `AEMeasurable` for the measure
`volume|_{(0,∞)} ⊗ volume|_{[0,π/2]}`, which is `(volume ⊗ volume)` restricted to the region. -/
theorem aemeasurable_uncurry_of_boxReg {δ : ℝ → ℝ → ℝ} (hbox : Work.FTS_EllLimOK.BoxReg δ) :
    AEMeasurable (Function.uncurry δ)
      ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hms : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ Work.Spaces.Iθ) :=
    measurableSet_Ioi.prod measurableSet_Icc
  rw [MeasureTheory.Measure.prod_restrict]
  refine aemeasurable_restrict_of_measurable_subtype hms ?_
  -- `δ` is `C²` (hence continuous) on the region `s = (0,∞) × [0,π/2]`.
  have hcd : ContDiffOn ℝ 2 (Function.uncurry δ) (Set.Ioi (0 : ℝ) ×ˢ Work.Spaces.Iθ) := by
    apply contDiffOn_of_locally_contDiffOn
    rintro ⟨z, θ⟩ ⟨hz, hθ⟩
    change 0 < z at hz
    -- the open set `(z/2, 2z) × (-1, π/2+1)` meets `s` inside the closed box `[z/2, 2z] × [0,π/2]`
    refine ⟨Set.Ioo (z / 2) (2 * z) ×ˢ Set.Ioo (-1) (π / 2 + 1), ?_, ?_, ?_⟩
    · exact isOpen_Ioo.prod isOpen_Ioo
    · exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith [hθ.1], by linarith [hθ.2]⟩⟩
    · refine (hbox (z / 2) (2 * z) (by linarith) (by linarith)).mono ?_
      rintro ⟨p, q⟩ ⟨⟨hpz, hpq⟩, hu⟩
      exact ⟨⟨le_of_lt hu.1.1, le_of_lt hu.1.2⟩, hpq⟩
  have hcont : ContinuousOn (Function.uncurry δ) (Set.Ioi (0 : ℝ) ×ˢ Work.Spaces.Iθ) :=
    ContDiffOn.continuousOn hcd
  have : Continuous
      (fun x : (Set.Ioi (0 : ℝ) ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ)) => Function.uncurry δ x) :=
    continuousOn_iff_continuous_domRestrict.mp hcont
  exact this.measurable

end Work.FTS_EllLimOK.EGap
