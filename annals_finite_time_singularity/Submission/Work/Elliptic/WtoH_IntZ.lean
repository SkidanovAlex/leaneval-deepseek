import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.Elliptic.WtoHAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

open MeasureTheory Filter
open scoped Real Topology

/-- The derivative of `z ↦ -(1+z)⁻¹` is the integrand `z ↦ 1/(1+z)²`, which is
nonnegative, so `1/(1+z)²` is integrable on `Iz = [0,∞)` and its integral is `1 ≤ 2`. -/
theorem WtoH_IntZ :
    MeasureTheory.IntegrableOn (fun z : ℝ => 1 / (1 + z) ^ 2) Work.Spaces.Iz ∧
      ∫ z in Work.Spaces.Iz, 1 / (1 + z) ^ 2 ≤ 2 := by
  have hderiv : ∀ x ∈ Set.Ici (0:ℝ),
      HasDerivAt (fun x : ℝ => -((1 + x)⁻¹)) (1/(1+x)^2 : ℝ) x := by
    intro x hx
    have h1 : HasDerivAt (fun x : ℝ => 1 + x) 1 x := by
      simpa using (hasDerivAt_id x).const_add 1
    have hx0 : (1 + x) ≠ 0 := by have : (0:ℝ) ≤ x := hx; linarith
    have h2 := (h1.inv hx0).neg
    convert h2 using 1
    ring
  have hpos : ∀ x ∈ Set.Ioi (0:ℝ), 0 ≤ (1/(1+x)^2 : ℝ) := by
    intro x hx
    apply div_nonneg (by norm_num)
    positivity
  have htend : Tendsto (fun x : ℝ => -((1 + x)⁻¹)) atTop (𝓝 0) := by
    have h : Tendsto (fun x : ℝ => 1 + x) atTop atTop :=
      tendsto_atTop_add_const_left _ (1:ℝ) tendsto_id
    simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp h |>.neg
  have hIntIoi : IntegrableOn (fun x : ℝ => 1/(1+x)^2) (Set.Ioi (0:ℝ)) :=
    integrableOn_Ioi_deriv_of_nonneg' hderiv hpos htend
  have hValIoi : ∫ x in Set.Ioi (0:ℝ), (1/(1+x)^2 : ℝ) = 1 := by
    have := integral_Ioi_of_hasDerivAt_of_nonneg' (a := (0:ℝ)) hderiv hpos htend
    simpa using this
  constructor
  · rw [Work.Spaces.Iz]
    exact (integrableOn_Ici_iff_integrableOn_Ioi
      (f := fun z : ℝ => 1/(1+z)^2) (b := (0:ℝ))).mpr hIntIoi
  · rw [Work.Spaces.Iz, integral_Ici_eq_integral_Ioi, hValIoi]
    norm_num

end Work.Elliptic
