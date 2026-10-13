import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.CoreResiduals.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Matrix
open MeasureTheory

namespace Work.CoreResiduals.BiotSavart

/-- The cross product is linear in its first argument (it is Mathlib's bilinear
`Matrix.crossProduct` on `Fin 3 → ℝ`). -/
theorem crossProduct_smul_left (c : ℝ) (v w : Fin 3 → ℝ) : (c • v) ⨯₃ w = c • (v ⨯₃ w) := by
  show crossProduct (c • v) w = c • (crossProduct v w)
  rw [LinearMap.map_smul, LinearMap.smul_apply]

/-- The Biot–Savart operator is homogeneous: `BS(c·ω) = c·BS(ω)`. -/
theorem biotSavart_smul (c : ℝ) {ω : Work.LWP.R3 → Work.LWP.R3} {R M : ℝ}
    (hω : ∀ a, ‖ω a‖ ≤ M) (hs : ∀ a, ω a ≠ 0 → a ∈ Metric.closedBall 0 R)
    (hm : MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume) (x : Work.LWP.R3) :
    Work.LWP.biotSavart (fun a => c • ω a) x = c • Work.LWP.biotSavart ω x := by
  -- `biotSavart` is `(4π)⁻¹ • ∫ y, ‖x - y‖⁻³ • (ω y × (x - y))`: it is enough to pull `c`
  -- out of the integrand, which uses only the bilinearity of the cross product and the
  -- linearity of the Bochner integral (unconditional in Mathlib).
  unfold Work.LWP.biotSavart
  have hg : (fun y : Work.LWP.R3 =>
        WithLp.toLp 2 ((‖x - y‖ ^ (3 : ℕ))⁻¹ •
          crossProduct ((fun a => c • ω a) y).ofLp (x.ofLp - y.ofLp)))
      = fun y : Work.LWP.R3 =>
        c • WithLp.toLp 2 ((‖x - y‖ ^ (3 : ℕ))⁻¹ •
          crossProduct (ω y).ofLp (x.ofLp - y.ofLp)) := by
    funext y
    rw [WithLp.ofLp_smul, crossProduct_smul_left c (ω y).ofLp (x.ofLp - y.ofLp), smul_comm,
      WithLp.toLp_smul]
  rw [hg, MeasureTheory.integral_smul, smul_comm]

end Work.CoreResiduals.BiotSavart
