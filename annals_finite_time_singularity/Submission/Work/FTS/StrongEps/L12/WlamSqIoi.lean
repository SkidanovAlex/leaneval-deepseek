import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.GalBasis.cc.Defs
import Submission.Work.FTS.StrongEps.L12.L12_z_lipschitz

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.L12

open scoped Real Topology
open MeasureTheory Set Filter

/-- namespace `Work.FTS.StrongEps.L12`, declaration name `WlamSqIoi`.
The far part of the squared radial weight: `(Wlam s)² = s²/(1+s)⁴ ≤ 1/(1+s)²` for `s ≥ 0`
(`Work.FTS.StrongEps.L12.Wlam_sq_le_inv_sq`), and `∫_{s > R} 1/(1+s)² = 1/(1+R)` for `R ≥ 0`
(`Work.FTS.StrongEps.L12.integral_Ioi_one_add_sq_inv`, with integrability
`Work.FTS.StrongEps.L12.integrableOn_Ioi_one_add_sq_inv`); monotonicity of the set integral gives
`∫_{s > R} (Wlam s)² ≤ 1/(1+R)`. -/
theorem WlamSqIoi (R : ℝ) (hR : 0 ≤ R) :
    ∫ s in Set.Ioi R, Work.FTS.GalBasis.cc.Wlam s ^ 2 ≤ 1 / (1 + R) := by
  -- the squared weight is square-integrable on the far interval `(R,∞) ⊆ (0,∞)`
  have hInt : IntegrableOn (fun s => Work.FTS.GalBasis.cc.Wlam s ^ 2) (Set.Ioi R) := by
    simpa only [Work.FTS.GalBasis.cc.Wlam] using
      Work.Elliptic.psi_sq_integrable_aux.mono_set (fun x hx => by
        simp only [Set.mem_Ioi] at hx ⊢
        linarith)
  -- dominate pointwise by the integrable profile `1/(1+s)²`
  have h1 : ∫ s in Set.Ioi R, Work.FTS.GalBasis.cc.Wlam s ^ 2
      ≤ ∫ s in Set.Ioi R, 1 / (1 + s) ^ 2 :=
    setIntegral_mono_on hInt (integrableOn_Ioi_one_add_sq_inv R hR) measurableSet_Ioi
      (fun s hs => Wlam_sq_le_inv_sq s (le_of_lt (lt_of_le_of_lt hR hs)))
  -- evaluate the tail integral
  rwa [integral_Ioi_one_add_sq_inv R hR] at h1

end Work.FTS.StrongEps.L12
