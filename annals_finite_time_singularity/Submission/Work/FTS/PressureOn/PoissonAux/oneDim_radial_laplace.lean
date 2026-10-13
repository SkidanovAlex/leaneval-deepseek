import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The one-dimensional radial Laplace identity

For a `C²` function `h` and `ρ > 0` we compute, with `f(r) = h(r)/(4π r)`,

`f'(r) = h'(r)/(4π r) - h(r)/(4π r²)`,   `f''(r) = h''(r)/(4π r) - 2h'(r)/(4π r²) + 2h(r)/(4π r³)`,

so that `f''(ρ) + 2 f'(ρ)/ρ = h''(ρ)/(4π ρ)`.  This is the radial part of the Laplacian
applied to `h(|x|)/(4π|x|)`; it is the identity used to evaluate the Poisson kernel on
radially symmetric data.
-/

namespace Work.FTS.PressureOn.PoissonAux

/-- Derivative of `r ↦ f r / (c * r)` at a point `ρ ≠ 0` (with `c ≠ 0`). -/
private lemma hasDerivAt_div_mul_id {f : ℝ → ℝ} {f' c ρ : ℝ} (hc : c ≠ 0) (hρ : ρ ≠ 0)
    (hf : HasDerivAt f f' ρ) :
    HasDerivAt (fun r : ℝ => f r / (c * r)) (f' / (c * ρ) - f ρ / (c * ρ ^ 2)) ρ := by
  have hg : HasDerivAt (fun r : ℝ => c * r) c ρ := by
    simpa using (hasDerivAt_id ρ).const_mul c
  have h := hf.div hg (mul_ne_zero hc hρ)
  convert h using 1
  field_simp

/-- Derivative of `r ↦ f r / (c * r ^ 2)` at a point `ρ ≠ 0` (with `c ≠ 0`). -/
private lemma hasDerivAt_div_mul_sq {f : ℝ → ℝ} {f' c ρ : ℝ} (hc : c ≠ 0) (hρ : ρ ≠ 0)
    (hf : HasDerivAt f f' ρ) :
    HasDerivAt (fun r : ℝ => f r / (c * r ^ 2)) (f' / (c * ρ ^ 2) - 2 * f ρ / (c * ρ ^ 3)) ρ := by
  have hg : HasDerivAt (fun r : ℝ => c * r ^ 2) (c * (2 * ρ)) ρ := by
    simpa using (hasDerivAt_pow 2 ρ).const_mul c
  have h := hf.div hg (by positivity)
  convert h using 1
  field_simp

theorem oneDim_radial_laplace (h : ℝ → ℝ) (hh : ContDiff ℝ 2 h) {ρ : ℝ} (hρ : 0 < ρ) :
    deriv (deriv (fun r : ℝ => h r / (4 * Real.pi * r))) ρ
        + 2 * deriv (fun r : ℝ => h r / (4 * Real.pi * r)) ρ / ρ
      = deriv (deriv h) ρ / (4 * Real.pi * ρ) := by
  have hρne : ρ ≠ 0 := ne_of_gt hρ
  have hc : (4 * Real.pi) ≠ 0 := by positivity
  have hd : Differentiable ℝ h := hh.differentiable (by norm_num)
  have hd1 : Differentiable ℝ (deriv h) := hh.differentiable_deriv_two
  -- first derivative of `r ↦ h r / (4 π r)`
  have hF1 : HasDerivAt (fun r : ℝ => h r / (4 * Real.pi * r))
      (deriv h ρ / (4 * Real.pi * ρ) - h ρ / (4 * Real.pi * ρ ^ 2)) ρ :=
    hasDerivAt_div_mul_id hc hρne (hd.differentiableAt.hasDerivAt)
  -- the two summands of the derivative function, differentiated at `ρ`
  have hG1 : HasDerivAt (fun r : ℝ => deriv h r / (4 * Real.pi * r))
      (deriv (deriv h) ρ / (4 * Real.pi * ρ) - deriv h ρ / (4 * Real.pi * ρ ^ 2)) ρ :=
    hasDerivAt_div_mul_id hc hρne (hd1.differentiableAt.hasDerivAt)
  have hG2 : HasDerivAt (fun r : ℝ => h r / (4 * Real.pi * r ^ 2))
      (deriv h ρ / (4 * Real.pi * ρ ^ 2) - 2 * h ρ / (4 * Real.pi * ρ ^ 3)) ρ :=
    hasDerivAt_div_mul_sq hc hρne (hd.differentiableAt.hasDerivAt)
  have hG : HasDerivAt (fun r : ℝ => deriv h r / (4 * Real.pi * r) - h r / (4 * Real.pi * r ^ 2))
      ((deriv (deriv h) ρ / (4 * Real.pi * ρ) - deriv h ρ / (4 * Real.pi * ρ ^ 2))
        - (deriv h ρ / (4 * Real.pi * ρ ^ 2) - 2 * h ρ / (4 * Real.pi * ρ ^ 3))) ρ :=
    hG1.sub hG2
  -- `deriv (fun r => h r / (4π r))` agrees near `ρ` with the explicit formula
  have hEv : (fun r : ℝ => deriv h r / (4 * Real.pi * r) - h r / (4 * Real.pi * r ^ 2))
      =ᶠ[nhds ρ] deriv (fun r : ℝ => h r / (4 * Real.pi * r)) := by
    filter_upwards [(isOpen_ne (x := (0 : ℝ))).mem_nhds hρne] with r hr
    exact (hasDerivAt_div_mul_id hc hr (hd.differentiableAt.hasDerivAt)).deriv.symm
  have h2 : deriv (deriv (fun r : ℝ => h r / (4 * Real.pi * r))) ρ
      = (deriv (deriv h) ρ / (4 * Real.pi * ρ) - deriv h ρ / (4 * Real.pi * ρ ^ 2))
        - (deriv h ρ / (4 * Real.pi * ρ ^ 2) - 2 * h ρ / (4 * Real.pi * ρ ^ 3)) := by
    rw [← hEv.deriv_eq, hG.deriv]
  have h1 : deriv (fun r : ℝ => h r / (4 * Real.pi * r)) ρ
      = deriv h ρ / (4 * Real.pi * ρ) - h ρ / (4 * Real.pi * ρ ^ 2) := hF1.deriv
  rw [h2, h1]
  field_simp
  ring

end Work.FTS.PressureOn.PoissonAux
