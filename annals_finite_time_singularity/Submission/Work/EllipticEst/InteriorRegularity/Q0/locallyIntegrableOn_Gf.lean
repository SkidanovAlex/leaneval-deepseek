import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.EllipticEst.InteriorRegularity.Q0.smoothOn_Gf

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.InteriorRegularity.Q0

theorem locallyIntegrableOn_Gf {α : ℝ} (hα : 0 < α) {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) :
    MeasureTheory.LocallyIntegrableOn
      (fun x : Work.EllipticEst.InteriorRegularity.E2 =>
        (Work.EllipticEst.InteriorRegularity.Q0.Gf α F x : ℂ))
      Work.EllipticEst.InteriorRegularity.stripE := by
  -- The strip is open (and hence measurable): it is the preimage of `(0, π/2)` under `x ↦ x 1`.
  have hmeas : MeasurableSet Work.EllipticEst.InteriorRegularity.stripE := by
    rw [Work.EllipticEst.InteriorRegularity.stripE]
    exact measurableSet_Ioo.preimage
      (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) (1 : Fin 2)).measurable
  -- `Gf α F` is `C^∞` on the strip, in particular continuous there; a function continuous on a
  -- measurable set is locally integrable on it.
  exact ((smoothOn_Gf hα hF 0).continuousOn).locallyIntegrableOn hmeas

end Work.EllipticEst.InteriorRegularity.Q0
