import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.InnerProductSpace.Dual

namespace Commons.Analysis.Calculus.FDeriv

open scoped Pointwise in
theorem hessianOp_comp_add_left {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (c x : E) (s : Set E) :
    InnerProductSpace.continuousLinearMapOfBilin
        (fderivWithin ℝ (fderivWithin ℝ (fun y : E => f (c + y)) s) s x)
      = InnerProductSpace.continuousLinearMapOfBilin
        (fderivWithin ℝ (fderivWithin ℝ f (c +ᵥ s)) (c +ᵥ s) (c + x)) := by
  have h1 : fderivWithin ℝ (fun y : E => f (c + y)) s
      = fun y : E => fderivWithin ℝ f (c +ᵥ s) (c + y) := by
    funext y
    exact fderivWithin_comp_add_left c
  have h2 : fderivWithin ℝ (fderivWithin ℝ (fun y : E => f (c + y)) s) s x
      = fderivWithin ℝ (fderivWithin ℝ f (c +ᵥ s)) (c +ᵥ s) (c + x) := by
    rw [h1]
    exact fderivWithin_comp_add_left c
  exact congrArg InnerProductSpace.continuousLinearMapOfBilin h2

end Commons.Analysis.Calculus.FDeriv