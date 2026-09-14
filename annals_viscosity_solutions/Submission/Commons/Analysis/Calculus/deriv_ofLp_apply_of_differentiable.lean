import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Commons.Analysis.Calculus

/-- The `i`-th coordinate of the derivative of a curve is the derivative of the `i`-th
coordinate. -/
theorem deriv_ofLp_apply_of_differentiable {ι : Type*} [Fintype ι] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → EuclideanSpace E ι) (t : ℝ) (i : ι)
    (hg : DifferentiableAt ℝ g t) :
    deriv (fun s => (g s).ofLp i) t = (deriv g t).ofLp i := by
  let L : EuclideanSpace E ι →L[ℝ] E := PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => E) i
  have h1 : (fun s => (g s).ofLp i) = (⇑L) ∘ g := by
    funext s
    exact (PiLp.proj_apply 2 (fun _ : ι => E) i (g s)).symm
  rw [h1, fderiv_comp_deriv t L.differentiableAt hg, ContinuousLinearMap.fderiv]
  exact PiLp.proj_apply 2 (fun _ : ι => E) i (deriv g t)

end Commons.Analysis.Calculus