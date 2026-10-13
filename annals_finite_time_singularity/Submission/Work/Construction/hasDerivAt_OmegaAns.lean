import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Construction.Defs
import Submission.Work.Construction.hasDerivAt_zvar

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.Construction

/-- The self-similar ansatz `Ω(R,θ,t) = (1-(1+μ)t)^{-1} F(R/(1-(1+μ)t)^{1+lam}, θ)` is
differentiable in `t`, with derivative
`(1+μ)(1-(1+μ)t)^{-2} (F(z) + (1+lam) z ∂_zF(z))` at `z = zvar μ lam R t`.

The hypotheses are `hu : 0 < 1-(1+μ)t` (so that the power function underlying `zvar` is
differentiable there) and `hF : HasDerivAt (fun z' => F z' θ) (pz F z θ) z` at `z = zvar`. -/
theorem hasDerivAt_OmegaAns {μ lam : ℝ} {F : ℝ → ℝ → ℝ} {R θ t : ℝ}
    (hu : 0 < 1 - (1 + μ) * t)
    (hF : HasDerivAt (fun z' => F z' θ) (Work.Spaces.pz F (Work.Construction.zvar μ lam R t) θ)
      (Work.Construction.zvar μ lam R t)) :
    HasDerivAt (fun s : ℝ => Work.Construction.OmegaAns μ lam F R θ s)
      ((1 + μ) * (1 - (1 + μ) * t) ^ (-2 : ℝ) *
        (F (Work.Construction.zvar μ lam R t) θ
          + (1 + lam) * Work.Spaces.Dz F (Work.Construction.zvar μ lam R t) θ)) t := by
  have hne : 1 - (1 + μ) * t ≠ 0 := ne_of_gt hu
  -- the affine function underlying the scale factor
  have hlin : HasDerivAt (fun s : ℝ => 1 - (1 + μ) * s) (-(1 + μ)) t := by
    have h1 : HasDerivAt (fun s : ℝ => (1 + μ) * s) (1 + μ) t := by
      simpa using (hasDerivAt_id t).const_mul (1 + μ)
    convert (hasDerivAt_const t (1 : ℝ)).sub h1 using 1
    ring
  -- derivative of the scale factor `scalefac μ s = (1-(1+μ)s)^{-1}`
  have hsc : HasDerivAt (fun s : ℝ => (1 - (1 + μ) * s)⁻¹)
      ((1 + μ) * (1 - (1 + μ) * t) ^ (-2 : ℝ)) t := by
    have h := hlin.inv hne
    convert h using 1
    rw [div_eq_mul_inv, show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hu.le,
      Real.rpow_two]
    ring
  -- derivative of `s ↦ F (zvar μ lam R s) θ` by the chain rule
  have hz : HasDerivAt (fun s : ℝ => zvar μ lam R s)
      ((1 + lam) * (1 + μ) * (zvar μ lam R t / (1 - (1 + μ) * t))) t :=
    hasDerivAt_zvar hu
  have hcomp : HasDerivAt (fun s : ℝ => F (zvar μ lam R s) θ)
      (Work.Spaces.pz F (zvar μ lam R t) θ *
        ((1 + lam) * (1 + μ) * (zvar μ lam R t / (1 - (1 + μ) * t)))) t :=
    hF.comp t hz
  -- product rule
  have hprod := hsc.mul hcomp
  -- identify the derivative value
  have hb2 : (1 - (1 + μ) * t) ^ (-2 : ℝ)
      = (1 - (1 + μ) * t)⁻¹ * (1 - (1 + μ) * t)⁻¹ := by
    rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hu.le, Real.rpow_two,
      ← inv_pow]
    ring
  have hval : ((1 + μ) * (1 - (1 + μ) * t) ^ (-2 : ℝ)) * F (zvar μ lam R t) θ
      + (1 - (1 + μ) * t)⁻¹ * (Work.Spaces.pz F (zvar μ lam R t) θ *
          ((1 + lam) * (1 + μ) * (zvar μ lam R t / (1 - (1 + μ) * t))))
      = (1 + μ) * (1 - (1 + μ) * t) ^ (-2 : ℝ) *
          (F (zvar μ lam R t) θ
            + (1 + lam) * Work.Spaces.Dz F (zvar μ lam R t) θ) := by
    rw [Work.Spaces.Dz, hb2]
    ring
  refine (hprod.congr_deriv hval).congr_of_eventuallyEq ?_
  simp only [OmegaAns, scalefac]
  filter_upwards with s
  simp

end Work.Construction
