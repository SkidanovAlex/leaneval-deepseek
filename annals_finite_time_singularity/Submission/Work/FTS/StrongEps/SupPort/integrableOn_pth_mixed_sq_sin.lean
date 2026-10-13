import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.H2.LinfQ
import Submission.Work.FTS.H2.SupMixedLeH4
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.SupPort

theorem integrableOn_pth_mixed_sq_sin {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (b a : ℕ) (hab : a + b ≤ 2) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun σ => (Work.Spaces.pth (Work.Spaces.mixed b a f) z σ) ^ 2
      * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ :=
  Work.FTS.TransportS.T2SupB2.integrableOn_pth_sq_rpow hF hmem b a (by omega) hz

end Work.FTS.StrongEps.SupPort
