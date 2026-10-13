import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- `π` is the notation for `Real.pi`; it is a *scoped* notation (`open scoped Real`).
open scoped Real

namespace Work.FTS.EllipticEst

/-- **Pointwise antiderivative identity for the self-pairing of `L₀`.**  For `f : ℝ → ℝ` which is
`C²` at `θ ∈ (0, π/2)`, the function `F(θ) = -f'(θ)·f(θ) + (1/2)·tan θ·f(θ)²` has derivative
`L₀(f)(θ)·f(θ) - f'(θ)² - (1/2)(f(θ)/cos θ)² + 6f(θ)²`, where `L₀` is `Work.Elliptic.Lzero`
applied to the `θ`-slice `fun _ θ' => f θ'` (so `L₀(f)(θ) = -f''(θ) + (tan θ · f(θ))' - 6f(θ)`).
The hypothesis `θ ∈ (0, π/2)` is what makes `tan` differentiable at `θ`. -/
theorem hasDerivAt_self_antideriv (f : ℝ → ℝ) (θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2))
    (h2 : ContDiffAt ℝ 2 f θ) :
    HasDerivAt (fun s => -(deriv f s) * f s + (1 / 2) * Real.tan s * (f s) ^ 2)
      (Work.Elliptic.Lzero (fun _ s => f s) 0 θ * f θ
        - (deriv f θ) ^ 2 - (1 / 2) * (f θ / Real.cos θ) ^ 2 + 6 * (f θ) ^ 2) θ := by
  -- `cos θ ≠ 0` on `(0, π/2)`, so that `tan` is differentiable at `θ`.
  have hcos : Real.cos θ ≠ 0 := by
    refine ne_of_gt (Real.cos_pos_of_mem_Ioo (x := θ) ⟨?_, hθ.2⟩)
    linarith [hθ.1, Real.pi_pos]
  -- first and second derivative of `f` at `θ`, from `C²`-regularity.
  have h1 : HasDerivAt f (deriv f θ) θ := (h2.hasStrictDerivAt (by norm_num)).hasDerivAt
  have h2' : HasDerivAt (deriv f) (deriv (deriv f) θ) θ :=
    ((h2.derivWithin (m := 1) (by norm_num)).hasStrictDerivAt (by norm_num)).hasDerivAt
  have htan : HasDerivAt Real.tan (1 / Real.cos θ ^ 2) θ := Real.hasDerivAt_tan hcos
  -- unfold `L₀` on the `θ`-slice `fun _ s => f s`.
  have hL : Work.Elliptic.Lzero (fun _ s => f s) 0 θ
      = -(deriv (deriv f) θ) + deriv (fun s => Real.tan s * f s) θ - 6 * f θ := by
    simp only [Work.Elliptic.Lzero, Work.Spaces.pth, Work.Spaces.pthIter]
  rw [hL]
  have htanf : deriv (fun s => Real.tan s * f s) θ
      = (1 / Real.cos θ ^ 2) * f θ + Real.tan θ * deriv f θ := (htan.mul h1).deriv
  rw [htanf]
  -- the derivative of `F`, computed with the product rule.
  have hderiv : HasDerivAt (fun s => -(deriv f s) * f s + (1 / 2) * Real.tan s * (f s) ^ 2)
      (-(deriv (deriv f) θ * f θ + deriv f θ * deriv f θ)
        + (1 / 2) * ((1 / Real.cos θ ^ 2) * (f θ) ^ 2
            + Real.tan θ * (2 * (f θ) * deriv f θ))) θ := by
    have hsq : HasDerivAt (fun s => (f s) ^ 2) (2 * (f θ) * deriv f θ) θ := by
      convert h1.pow 2 using 1; ring_nf
    have hA : HasDerivAt (fun s => -(deriv f s) * f s)
        (-(deriv (deriv f) θ * f θ + deriv f θ * deriv f θ)) θ := by
      convert (h2'.mul h1).neg using 1;
        (funext s; simp only [Pi.neg_apply, Pi.mul_apply]; ring_nf)
    have hB : HasDerivAt (fun s => (1 / 2) * Real.tan s * (f s) ^ 2)
        ((1 / 2) * ((1 / Real.cos θ ^ 2) * (f θ) ^ 2
            + Real.tan θ * (2 * (f θ) * deriv f θ))) θ := by
      convert (htan.mul hsq).const_mul (1 / 2) using 1;
        (funext s; simp only [Pi.mul_apply]; ring_nf)
    exact hA.add hB
  exact hderiv.congr_deriv (by ring_nf)

end Work.FTS.EllipticEst
