import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Stability.Defs
import Submission.Work.Construction.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Stability

/-- The `z`-derivative of the singular part at the slice `F = F_* + g`:
`z∂_zΘ = -(1/(4α))sin(2θ)(F,K)_{L²_θ}(z)`.  This is the Construction area's
`Work.Construction.Dz_Theta_eq` transported to the family `Ftot`, with its analytic hypotheses
(integrability of the `L₁₂`-density, its continuity at `z`, and `0 < z`). -/
theorem ThetaPzFtot (α : ℝ) (hα : 0 < α) (g : F3) (z θ s : ℝ)
    (hint : MeasureTheory.IntegrableOn (Work.Construction.L12dens (Ftot α g s)) (Set.Ioi 0))
    (hcont : ContinuousAt (Work.Construction.L12dens (Ftot α g s)) z) (hz : 0 < z) :
    z * Work.Spaces.pz (Work.Construction.Theta α (Ftot α g s)) z θ
      = -(1 / (4 * α)) * Work.Construction.s2 θ * Work.Construction.FK (Ftot α g s) z := by
  have h := Work.Construction.Dz_Theta_eq (α := α) (z := z) (θ := θ)
    (F := Ftot α g s) hα hint hcont hz
  simpa only [Work.Spaces.Dz] using h

end Work.Stability
