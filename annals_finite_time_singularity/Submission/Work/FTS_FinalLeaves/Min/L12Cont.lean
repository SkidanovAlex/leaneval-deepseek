import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FM.Defs
import Submission.Work.FM.Core
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.CoercivityFix.Coer1T.HardyAlt.l12dens_continuousAt
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_integrableOn_of_continuousOn
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.sliceK_integrableOn_of_continuousOn
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.moment_relation_of_contDiffOn_four
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.pzSqSeta_box_integrable_of_contDiffOn_four
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.slice_sinCos2_integrable_of_contDiffOn_four
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.pzMoment_le_sqrt_of_contDiffOn_four
import Submission.Work.FTS_FinalLeaves.Min.FstarFacts
import Submission.Work.FTS_FinalLeaves.Min.ChainCont

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_FinalLeaves.Min

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-!
# The `L₁₂`-facts of the open-quadrant finite-order class

This module assembles, for a datum `f` which is `ContDiffOn ℝ 4` on the open quadrant and lies
in `ℋ⁴`: integrability of the `L₁₂`-density on `(0,∞)`, integrability of the angular slice
`θ ↦ K θ f z θ / z` on `Iθ` for `z > 0`, and continuity of the `L₁₂`-density at every `z > 0`.

The last one is the only non-trivial part: `L12dens K f s = 3·F_*(f)(s)/s`
(`HardyAlt.L12dens_eq_three_Fstar`), so it suffices to prove the continuity of the angular moment
`F_*(f)`.  The latter is `Fstar_continuousAt_of_chain`, applied to the four analytic inputs of
the sibling `Pieces` modules: the chain relation `Pieces.moment_relation_of_contDiffOn_four`, the
box integrability `Pieces.pzSqSeta_box_integrable_of_contDiffOn_four`, the slice integrability
`Pieces.slice_sinCos2_integrable_of_contDiffOn_four` and the moment bound
`Pieces.pzMoment_le_sqrt_of_contDiffOn_four`.
-/

/-- Integrability of the `L₁₂`-density of a continuous datum of `ℋ⁴`. -/
theorem L12dens_integrableOn_of_continuousOn {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hC : ContinuousOn (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) :
    MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K f) (Set.Ioi 0) :=
  Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_integrableOn_of_continuousOn hC hmem

/-- Integrability of the angular slice `θ ↦ K θ f z θ / z` of a continuous datum of `ℋ⁴`. -/
theorem sliceK_integrableOn_of_continuousOn {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hC : ContinuousOn (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) :
    ∀ s : ℝ, 0 < s → MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * f s θ / s) Work.Spaces.Iθ :=
  Work.FTS.MeridianDyn.Bridge.Pieces.sliceK_integrableOn_of_continuousOn hC hmem

/-- Continuity of the `L₁₂`-density of a `C⁴`-datum of `ℋ⁴`. -/
theorem L12dens_continuousAt_of_contDiffOn_four (α : ℝ) {f : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hC : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) :
    ContinuousAt (Work.FM.L12dens Work.Spaces.K f) z := by
  have hbox := Work.FTS.MeridianDyn.Bridge.Pieces.pzSqSeta_box_integrable_of_contDiffOn_four
    α hC hmem
  have hsl := Work.FTS.MeridianDyn.Bridge.Pieces.slice_sinCos2_integrable_of_contDiffOn_four
    hC hmem
  have hmom := Work.FTS.MeridianDyn.Bridge.Pieces.pzMoment_le_sqrt_of_contDiffOn_four
    α hC hmem
  have hchain : ∀ a b : ℝ, 0 < a → a < b →
      Work.Elliptic.Fstar f b = Work.Elliptic.Fstar f a
        + ∫ s in Set.Icc a b, (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.pz f s θ * Work.Elliptic.sinCos2 θ) :=
    fun a b ha hab =>
      Work.FTS.MeridianDyn.Bridge.Pieces.moment_relation_of_contDiffOn_four f hC hbox hsl ha hab
  have hF : ContinuousAt (Work.Elliptic.Fstar f) z :=
    Fstar_continuousAt_of_chain α hz hchain hsl hmem.2 hmom
  have hdiv : ContinuousAt (fun s : ℝ => 3 * Work.Elliptic.Fstar f s / s) z :=
    (hF.const_mul 3).div continuousAt_id (ne_of_gt hz)
  exact hdiv.congr (Filter.Eventually.of_forall fun s =>
    (Work.FTS.CoercivityFix.Coer1T.HardyAlt.L12dens_eq_three_Fstar f s).symm)

end Work.FTS_FinalLeaves.Min
