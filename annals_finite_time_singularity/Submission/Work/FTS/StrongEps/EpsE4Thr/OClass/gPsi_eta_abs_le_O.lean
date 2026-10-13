import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.CoercivityFix.Coer1T.gPsi_eta_abs_le_Q
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.OClass

/-- **The `η`-slot of the projector correction in the open class `SmoothOpen`.**

This is the open-class (`SmoothOpen`, i.e. genuine `C^∞` on the *open* quadrant
`(0,∞) × (0,π/2)`, the class carried by `RegQo`) twin of
`Work.FTS.CoercivityFix.Coer1T.gPsi_eta_abs_le_Q`, which is stated for the interior class
`Work.FTS.LocData.SmoothQuad`.

Nothing in that proof uses the strip `z > -1` beyond the a.e. strong measurability of `f` on
`Iz ×ˢ Iθ`, which `SmoothOpen` supplies by `Work.Spaces.aesm_of_continuousOn_Qd` (the closed
quadrant differs from the open one by a null set).  The two analytic ingredients
(`etaW_gPsi_integrable_Q` for the joint integrability of the pairing density and
`wip_gPsi_eta_le_aux` for the Cauchy–Schwarz bound with constant `220`) are already stated for
the interior class with `haesm` as an explicit hypothesis, so the port is immediate. -/
theorem gPsi_eta_abs_le_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f)
    (hF : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => f z θ * f z θ * Work.Spaces.w z ^ 2
        * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
        (Function.uncurry (fun z θ => Work.Coercivity.T4fun α f z θ * f z θ
          * Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)))
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      ∧ |Work.Coercivity.wip
            (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
            (Work.Coercivity.T4fun α f) f|
          ≤ 220 * |Work.Coercivity.C0 f| * Real.sqrt (Work.Coercivity.EfEta f) := by
  have haesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd (Function.uncurry f) hso.continuousOn
  have haesm' : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 p.2)
      (MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
    rw [Work.Coercivity.volume_restrict_prod]; exact haesm
  refine ⟨?_, ?_⟩
  · have hg := Work.FTS.CoercivityFix.Coer1T.etaW_gPsi_integrable_Q α hα hα1 f haesm' hF
    refine IntegrableOn.congr_fun (Integrable.const_mul hg (Work.Coercivity.C0 f)) ?_
      (measurableSet_Ici.prod measurableSet_Icc)
    intro p hp
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry_apply_pair, Work.Coercivity.T4fun]
    ring
  · rw [show Work.Coercivity.T4fun α f
        = fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)
            * Work.Coercivity.C0 f from rfl]
    exact Work.FTS.CoercivityFix.Coer1T.wip_gPsi_eta_le_aux α hα hα1 f
      (Work.Coercivity.C0 f) haesm hF

end Work.FTS.StrongEps.EpsE4Thr.OClass
