import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Derivative of an inner product that vanishes identically

If two differentiable functions `f g : G → E` (into a real inner product
space `E`) satisfy `⟪f y, g y⟫ = 0` for all `y` in a neighborhood of `x`,
then their derivatives are "adjoint-orthogonal" at `x`:

`⟪fderiv f x v, g x⟫ + ⟪f x, fderiv g x v⟫ = 0` for every `v`.

This is the Weingarten-type product-rule identity used when the unit normal
is orthogonal to a tangent field.  It follows from `fderiv_inner_apply`
(`Mathlib/Analysis/InnerProductSpace/Calculus.lean`) together with the fact
that a function which is eventually zero has zero derivative.
-/

noncomputable section
open Filter
open scoped Topology
namespace Commons.Analysis.InnerProductSpace

/-- Product-rule identity for an inner product that is identically zero on a
neighborhood of `x`. -/
theorem fderiv_inner_zero_of_eventually {E G : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f g : G → E} {x : G}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hzero : (fun y : G => inner ℝ (f y) (g y)) =ᶠ[𝓝 x] (fun _ : G => (0 : ℝ))) :
    ∀ v : G, inner ℝ (fderiv ℝ f x v) (g x) + inner ℝ (f x) (fderiv ℝ g x v) = 0 := by
  intro v
  -- The derivative of an eventually-zero function vanishes at `x`.
  have hzeroder : fderiv ℝ (fun y : G => inner ℝ (f y) (g y)) x = 0 := by
    rw [hzero.fderiv_eq]
    simp
  -- Product rule for the inner product (`fderiv_inner_apply`).
  have hmain := fderiv_inner_apply ℝ hf hg v
  rw [hzeroder] at hmain
  simp at hmain
  -- hmain : 0 = inner ℝ (f x) (fderiv ℝ g x v) + inner ℝ (fderiv ℝ f x v) (g x)
  rw [add_comm] at hmain
  exact hmain.symm

end Commons.Analysis.InnerProductSpace