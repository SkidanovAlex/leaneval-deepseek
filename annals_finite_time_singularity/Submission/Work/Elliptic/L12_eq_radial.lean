import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

/-- The angular density of `L₁₂` is `3/r` times the angular moment `F_*`:
`∫_0^{π/2} K(θ) F(r,θ)/r dθ = 3/r ∫_0^{π/2} F(r,θ) sin θ cos²θ dθ`, because
`K(θ) = 3 sin θ cos²θ`.  No integrability is needed (the Bochner integral is total). -/
lemma L12dens_eq_three_Fstar_div (F : ℝ → ℝ → ℝ) (r : ℝ) :
    L12dens F r = 3 * (Fstar F r / r) := by
  rw [L12dens, Fstar]
  have h1 : (fun θ => Ktheta θ * F r θ / r)
      = fun θ => 3 * (F r θ * sinCos2 θ / r) := by
    funext θ; simp only [Ktheta, sinCos2]; ring
  rw [h1, MeasureTheory.integral_const_mul, MeasureTheory.integral_div]

theorem L12_eq_radial (F : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Elliptic.L12 F z = 3 * Work.Elliptic.L12rad F z := by
  rw [L12, L12rad]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun r _ => L12dens_eq_three_Fstar_div F r)]
  rw [MeasureTheory.integral_const_mul]

end Work.Elliptic
