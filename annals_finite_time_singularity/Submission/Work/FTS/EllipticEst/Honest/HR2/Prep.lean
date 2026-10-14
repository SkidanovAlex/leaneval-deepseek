import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.Honest.HonSliceFinite
import Submission.Work.FTS.EllipticEst.Honest.honYcBound
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.Stability.ZcutSmoothCompact

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest.HR2

theorem restrict_Iz_eq_restrict_Ioi :
    (volume.restrict Work.Spaces.Iz) = (volume.restrict (Set.Ioi (0 : ℝ))) := by
  rw [Work.Spaces.Iz]
  exact MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ))).symm

/-- A `C²` function on `(0,b)` with vanishing endpoint limits is continuous on `[0,b]`. -/
theorem continuousOn_Icc_of_limits {u : ℝ → ℝ} {b : ℝ} (hb : 0 < b)
    (hsm : ContDiffOn ℝ 2 u (Set.Ioo 0 b))
    (h0 : u 0 = 0) (hbb : u b = 0)
    (hl0 : Filter.Tendsto u (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hlb : Filter.Tendsto u (nhdsWithin b (Set.Iio b)) (nhds 0)) :
    ContinuousOn u (Set.Icc 0 b) := by
  have hcio : ContinuousWithinAt u (Set.Iio b) b := by
    show Filter.Tendsto u (nhdsWithin b (Set.Iio b)) (nhds (u b))
    rw [hbb]; exact hlb
  have hrigo : ContinuousWithinAt u (Set.Ioi 0) 0 := by
    show Filter.Tendsto u (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (u 0))
    rw [h0]; exact hl0
  intro x hx
  rcases lt_or_eq_of_le hx.1 with hx0 | hx0
  · rcases lt_or_eq_of_le hx.2 with hxb | hxb
    · have hmem : Set.Ioo 0 b ∈ nhds x := isOpen_Ioo.mem_nhds ⟨hx0, hxb⟩
      have hca : ContinuousAt u x :=
        (continuousWithinAt_iff_continuousAt hmem).mp
          (hsm.continuousOn.continuousWithinAt ⟨hx0, hxb⟩)
      exact hca.continuousWithinAt
    · subst hxb
      show Filter.Tendsto u (nhdsWithin x (Set.Icc 0 x)) (nhds (u x))
      rw [nhdsWithin_Icc_eq_nhdsLE hb]
      exact continuousWithinAt_Iio_iff_Iic.mp hcio
  · subst hx0
    show Filter.Tendsto u (nhdsWithin 0 (Set.Icc 0 b)) (nhds (u 0))
    rw [nhdsWithin_Icc_eq_nhdsGE hb]
    exact continuousWithinAt_Ioi_iff_Ici.mp hrigo


end Work.FTS.EllipticEst.Honest.HR2
