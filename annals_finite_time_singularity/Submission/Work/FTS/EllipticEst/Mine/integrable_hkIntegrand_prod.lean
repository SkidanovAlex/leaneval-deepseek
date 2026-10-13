import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.integrable_prod_of_iterated

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Mine

theorem integrable_hkIntegrand_prod {α : ℝ} {k : ℕ} {Z : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (Function.uncurry (fun s θ => Work.Spaces.HkIntegrand α k Z s θ))
      Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α k Z) :
    MeasureTheory.Integrable
      (Function.uncurry (fun s θ => Work.Spaces.HkIntegrand α k Z s θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  -- `HkIntegrand` is a sum of squares, so Tonelli's criterion in its iterated form applies:
  -- the integrand is continuous on the open quadrant (hence a.e. strongly measurable for
  -- `(dz)|_{Iz} ⊗ (dθ)|_{Iθ}`), its angular slices are integrable and the outer integral is
  -- integrable -- the last two are the two halves of `HkMem`.
  refine (Work.Spaces.integrable_prod_of_iterated
    (fun a b => Work.Spaces.HkIntegrand_nonneg α k Z a b)
    (Work.Spaces.aesm_of_continuousOn_Qd _ hcont) ?_ ?_).1
  · filter_upwards [MeasureTheory.ae_restrict_mem
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)] with z hz
    exact hmem.1 z hz
  · exact hmem.2

end Work.FTS.EllipticEst.Mine
