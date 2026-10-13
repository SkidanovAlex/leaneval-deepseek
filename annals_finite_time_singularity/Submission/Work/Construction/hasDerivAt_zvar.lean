import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Construction

/-- The self-similar variable `zvar μ lam R t = R/(1-(1+μ)t)^{1+lam}` as a function of `t`,
with the constants `μ, lam, R` fixed. -/
theorem hasDerivAt_zvar {μ lam R t : ℝ} (h : 0 < 1 - (1 + μ) * t) :
    HasDerivAt (fun s : ℝ => Work.Construction.zvar μ lam R s)
      ((1 + lam) * (1 + μ) * (Work.Construction.zvar μ lam R t / (1 - (1 + μ) * t))) t := by
  have hu : (0 : ℝ) < 1 - (1 + μ) * t := h
  have hne : (1 - (1 + μ) * t) ≠ 0 := ne_of_gt hu
  -- the inner affine function `s ↦ 1 - (1+μ)s`
  have hderiv_u : HasDerivAt (fun s : ℝ => 1 - (1 + μ) * s) (-(1 + μ)) t := by
    have h1 : HasDerivAt (fun s : ℝ => (1 + μ) * s) (1 + μ) t := by
      simpa using (hasDerivAt_id t).const_mul (1 + μ)
    convert (hasDerivAt_const t (1 : ℝ)).sub h1 using 1
    ring
  -- differentiate the power `(1-(1+μ)s)^{-(1+lam)}`
  have hpow : HasDerivAt (fun s : ℝ => (1 - (1 + μ) * s) ^ (-(1 + lam)))
      ((-(1 + lam)) * (1 - (1 + μ) * t) ^ (-(1 + lam) - 1) * (-(1 + μ))) t := by
    exact (Real.hasDerivAt_rpow_const (p := -(1 + lam)) (Or.inl hne)).comp t hderiv_u
  have hR : HasDerivAt (fun s : ℝ => R * (1 - (1 + μ) * s) ^ (-(1 + lam)))
      (R * ((-(1 + lam)) * (1 - (1 + μ) * t) ^ (-(1 + lam) - 1) * (-(1 + μ)))) t := by
    simpa using hpow.const_mul R
  -- `zvar` coincides with `R * (1-(1+μ)·)^{-(1+lam)}` near `t` (where the base is positive)
  have hz : Work.Construction.zvar μ lam R t = R * (1 - (1 + μ) * t) ^ (-(1 + lam)) := by
    rw [Work.Construction.zvar, Real.rpow_neg hu.le, div_eq_mul_inv]
  have hz2 : Work.Construction.zvar μ lam R t / (1 - (1 + μ) * t)
      = R * (1 - (1 + μ) * t) ^ (-(1 + lam) - 1) := by
    rw [hz, mul_div_assoc, ← Real.rpow_sub_one hne (-(1 + lam))]
  have hval : R * ((-(1 + lam)) * (1 - (1 + μ) * t) ^ (-(1 + lam) - 1) * (-(1 + μ)))
      = (1 + lam) * (1 + μ)
        * (Work.Construction.zvar μ lam R t / (1 - (1 + μ) * t)) := by
    rw [hz2]; ring
  have hev : (fun s : ℝ => Work.Construction.zvar μ lam R s)
      =ᶠ[nhds t] (fun s : ℝ => R * (1 - (1 + μ) * s) ^ (-(1 + lam))) := by
    have hcont : Continuous fun s : ℝ => 1 - (1 + μ) * s := by fun_prop
    have hopen : IsOpen {s : ℝ | 0 < 1 - (1 + μ) * s} := isOpen_lt continuous_const hcont
    filter_upwards [hopen.mem_nhds h] with s hs
    rw [Work.Construction.zvar, Real.rpow_neg hs.le, div_eq_mul_inv]
  exact (hR.congr_of_eventuallyEq hev).congr_deriv hval

end Work.Construction
