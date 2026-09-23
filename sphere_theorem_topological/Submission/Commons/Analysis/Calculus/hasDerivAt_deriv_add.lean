import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology

namespace Commons.Analysis.Calculus

/-- **The derivative of a sum of derivatives.** If `f` and `g` are (eventually near `0`)
differentiable and their derivative functions have derivatives `a` and `b` at `0`, then the derivative
function of `σ ↦ f σ + g σ` has derivative `a + b` at `0`. -/
theorem hasDerivAt_deriv_add {f g : ℝ → ℝ} {a b : ℝ}
    (hf : HasDerivAt (deriv f) a 0) (hg : HasDerivAt (deriv g) b 0)
    (hdf : ∀ᶠ σ in nhds (0 : ℝ), DifferentiableAt ℝ f σ)
    (hdg : ∀ᶠ σ in nhds (0 : ℝ), DifferentiableAt ℝ g σ) :
    HasDerivAt (deriv (fun σ : ℝ => f σ + g σ)) (a + b) 0 := by
  have h : deriv (fun σ : ℝ => f σ + g σ) =ᶠ[nhds (0 : ℝ)] deriv f + deriv g := by
    filter_upwards [hdf, hdg] with σ hf' hg'
    exact deriv_add hf' hg'
  exact (hf.add hg).congr_of_eventuallyEq h

end Commons.Analysis.Calculus