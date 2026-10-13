import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.R1G.Defs
import Submission.Work.Coercivity.L12dens_integrableOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G

/-- **Integrability of the `L₁₂`-density of the perturbation `P.g` on `(z,∞)` for `z ≥ 0`.**

`Work.Construction.L12dens P.g` is the fundamental-model density `Work.FM.L12dens Work.Spaces.K P.g`,
and `Work.Coercivity.L12dens_integrableOn` gives its integrability on `(0,∞)` from the `St1`-class
data carried by `ProfileData`: smoothness on a neighbourhood of the closed quadrant (`P.hsmooth`)
and membership in `ℋ²` (`P.hmem`).  For `z ≥ 0` the half-line `(z,∞)` is contained in `(0,∞)`, so
`IntegrableOn.mono_set` transfers the conclusion. -/
theorem L12dens_g_integrableOn {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    {z : ℝ} (hz : 0 ≤ z) :
    MeasureTheory.IntegrableOn (Work.Construction.L12dens P.g) (Set.Ioi z) := by
  have h0 : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K P.g) (Set.Ioi 0) :=
    Work.Coercivity.L12dens_integrableOn (Work.ConstructionInstance.profExp α) 2 P.g
      P.hsmooth P.hmem
  exact h0.mono_set (Set.Ioi_subset_Ioi hz)

end Work.R1G
