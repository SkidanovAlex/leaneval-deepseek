import Mathlib.Analysis.Calculus.FDeriv.Add
import Submission.Commons.Analysis.Calculus.FDeriv.hessianWithin_eq_hessian

namespace Commons.Analysis.Calculus.FDeriv

open scoped Topology

/-- `InnerProductSpace.continuousLinearMapOfBilin` is compatible with negation: it is the
composition `L ∘SL ·` with the fixed continuous linear map `L = (toDual ℝ E).symm`, hence
linear. -/
lemma continuousLinearMapOfBilin_neg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (A : E →L⋆[ℝ] E →L[ℝ] ℝ) :
    InnerProductSpace.continuousLinearMapOfBilin (-A)
      = - InnerProductSpace.continuousLinearMapOfBilin A := by
  show ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap) ∘SL
      (-A) = _
  rw [ContinuousLinearMap.comp_neg]
  rfl

theorem hessianWithin_neg_of_mem_nhds
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {φ : E → ℝ} {s : Set E} {x : E} (hx : s ∈ nhds x) :
    InnerProductSpace.continuousLinearMapOfBilin (fderivWithin ℝ (fderivWithin ℝ (fun y => -φ y) s) s x)
      = - InnerProductSpace.continuousLinearMapOfBilin (fderivWithin ℝ (fderivWithin ℝ φ s) s x) := by
  -- On a neighbourhood of `x`, within-derivatives coincide with ordinary derivatives.
  rw [hessianWithin_eq_hessian (E := E) (u := fun y => -φ y) hx,
      hessianWithin_eq_hessian (E := E) (u := φ) hx]
  -- The second derivative is compatible with negation.
  have hfe : fderiv ℝ (fderiv ℝ (fun y => -φ y)) x = - fderiv ℝ (fderiv ℝ φ) x := by
    have h1 : fderiv ℝ (fun y => -φ y) = fun y => - fderiv ℝ φ y := by
      funext y
      exact fderiv_fun_neg
    rw [h1, fderiv_fun_neg]
  rw [hfe, continuousLinearMapOfBilin_neg]

end Commons.Analysis.Calculus.FDeriv