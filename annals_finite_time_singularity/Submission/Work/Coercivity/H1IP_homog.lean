/-
# Homogeneity of the `ℋ¹` inner product `H1IP` in its first argument

`Work.Coercivity.H1IP` is a sum of four weighted `L²` pairings
`wip ρ A B = ∫ z in [0,∞), ∫ θ in [0,π/2], A z θ * B z θ * ρ z θ`, applied to the two
profiles and to their `D_z`/`D_θ` derivatives.  The Bochner integral is *total* (it is
defined for every function, and carries no integrability hypothesis), and scalar
multiplication commutes with it (`MeasureTheory.integral_const_mul`); likewise `deriv`
commutes with scalar multiplication unconditionally, because when the derivative fails
to exist both sides are `0`.  Consequently `H1IP α (c·f) g = c * H1IP α f g` holds for
*every* pair of profiles, with no measurability or integrability hypothesis at all.

This is the homogeneity clause `IP (fun z θ => c * f z θ) g = c * IP f g` of the paper's
specification `Work.Coercivity.IsHkIP` (there localized to `HkMem`-members); here it is
proved unconditionally.
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

noncomputable section

open scoped Real Topology
open MeasureTheory

/-! ## Elementary algebra of `deriv` and of the weighted pairing -/

/-- `deriv` is scalar homogeneous **unconditionally**: unlike `deriv_const_mul` there is
no differentiability hypothesis, because if `d` is not differentiable at `x` then neither
is `c * d` (for `c ≠ 0`), so both sides vanish. -/
theorem deriv_const_mul_uncond (c : ℝ) (d : ℝ → ℝ) (x : ℝ) :
    deriv (fun y => c * d y) x = c * deriv d x := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · by_cases hd : DifferentiableAt ℝ d x
    · exact deriv_const_mul c hd
    · have hcd : ¬ DifferentiableAt ℝ (fun y => c * d y) x := by
        intro h
        have h2 : DifferentiableAt ℝ (fun y => c⁻¹ * (c * d y)) x := h.const_mul c⁻¹
        refine hd ?_
        refine h2.congr_of_eventuallyEq ?_
        filter_upwards with y
        simp [hc]
      rw [deriv_zero_of_not_differentiableAt hcd, deriv_zero_of_not_differentiableAt hd,
        mul_zero]

/-- Scalar homogeneity of the weighted `L²` pairing in its first argument.  No
integrability or measurability hypothesis is needed: the identity is pointwise in the
integrand, and the total Bochner integral is homogeneous under scalar multiplication. -/
theorem wip_smul_left {ρ A B : ℝ → ℝ → ℝ} {c : ℝ} :
    wip ρ (fun z θ => c * A z θ) B = c * wip ρ A B := by
  rw [wip, wip]
  have h : (fun z => ∫ θ in Spaces.Iθ, (c * A z θ) * B z θ * ρ z θ)
      = fun z => c * ∫ θ in Spaces.Iθ, A z θ * B z θ * ρ z θ := by
    funext z
    rw [← MeasureTheory.integral_const_mul]
    congr 1 with θ
    ring
  simp only [h]
  rw [MeasureTheory.integral_const_mul]

/-- The radial derivative `D_z` is scalar homogeneous. -/
theorem Dz_smul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Spaces.Dz (fun z θ => c * f z θ) = fun z θ => c * Spaces.Dz f z θ := by
  funext z θ
  simp only [Spaces.Dz, Spaces.pz]
  rw [deriv_const_mul_uncond]
  ring

/-- The angular derivative `D_θ` is scalar homogeneous. -/
theorem Dth_smul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Spaces.Dth (fun z θ => c * f z θ) = fun z θ => c * Spaces.Dth f z θ := by
  funext z θ
  simp only [Spaces.Dth, Spaces.pth]
  rw [deriv_const_mul_uncond]
  ring

/-! ## Homogeneity of `H1IP` -/

theorem H1IP_homog (α : ℝ) (c : ℝ) (f g : ℝ → ℝ → ℝ) :
    Work.Coercivity.H1IP α (fun z θ => c * f z θ) g = c * Work.Coercivity.H1IP α f g := by
  rw [H1IP, H1IP, Dz_smul, Dth_smul, wip_smul_left, wip_smul_left, wip_smul_left,
    wip_smul_left]
  ring

end

end Work.Coercivity
