import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.sliceK_integrableOn_of_continuousOn
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_integrableOn_of_continuousOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.STC

theorem L12_sub_C4 {α : ℝ} {a b : ℝ → ℝ → ℝ}
    (ha : ContDiffOn ℝ 4 (Function.uncurry a) Work.FTS.EllipticEst.Q0)
    (hb : ContDiffOn ℝ 4 (Function.uncurry b) Work.FTS.EllipticEst.Q0)
    (hma : Work.Spaces.HkMem α 4 a) (hmb : Work.Spaces.HkMem α 4 b) :
    ∀ z ∈ Work.Spaces.Iz, Work.Construction.L12 (fun z θ => a z θ - b z θ) z
      = Work.Construction.L12 a z - Work.Construction.L12 b z := by
  intro z hz
  -- `z ∈ Iz = [0,∞)`, so `0 ≤ z`
  have hz0 : 0 ≤ z := hz
  -- `C^4` on `Q0` gives continuity there: this is the only input the integrability
  -- certificates need, no derivative of `a` or of `b` is used
  have hconta : ContinuousOn (Function.uncurry a) Work.FTS.EllipticEst.Q0 := ha.continuousOn
  have hcontb : ContinuousOn (Function.uncurry b) Work.FTS.EllipticEst.Q0 := hb.continuousOn
  -- the four integrability certificates of `L12_sub_of_integrable`
  refine Work.FTS.StrongEps.EComparison.L12_sub_of_integrable (z := z) ?_ ?_ ?_ ?_
  · -- angular slice of `a`: `s > z ≥ 0` gives `s > 0`
    intro s hs
    exact Work.FTS.MeridianDyn.Bridge.Pieces.sliceK_integrableOn_of_continuousOn
      hconta hma s (lt_of_le_of_lt hz0 hs)
  · intro s hs
    exact Work.FTS.MeridianDyn.Bridge.Pieces.sliceK_integrableOn_of_continuousOn
      hcontb hmb s (lt_of_le_of_lt hz0 hs)
  · -- density of `a`: integrable on `(0,∞)`, hence on `(z,∞) ⊆ (0,∞)`
    exact (Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_integrableOn_of_continuousOn
      hconta hma).mono_set (Set.Ioi_subset_Ioi hz0)
  · exact (Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_integrableOn_of_continuousOn
      hcontb hmb).mono_set (Set.Ioi_subset_Ioi hz0)

end Work.FTS_RegExport.RXT.STC
