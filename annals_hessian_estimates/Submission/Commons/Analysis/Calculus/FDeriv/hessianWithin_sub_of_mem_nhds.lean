import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Analysis.Calculus.FDeriv.hessianWithin_eq_hessian

/-!
# The Hessian operator is additive under subtraction

We prove that the second derivative operator (viewed as a map `E →L[ℝ] E` through the
Fréchet–Riesz representation theorem, i.e. `InnerProductSpace.continuousLinearMapOfBilin`)
is compatible with subtraction of functions:

`Hess(φ - ψ) = Hess(φ) - Hess(ψ)`

at a point `x` at which `φ` and `ψ` are `C²` (in the sense of `ContDiffWithinAt` on a set that
is a neighbourhood of `x`).

The proof splits into three independent facts:

* `hessianWithin_eq_hessian`: on a set that is a neighbourhood of `x`, the second derivative
  taken within the set coincides with the ordinary second derivative;
* `fderiv_fderiv_sub_of_contDiffAt`: the second Fréchet derivative is additive under
  subtraction (the `fderiv` analogue of `fderiv_fderiv_add_of_contDiffAt`);
* `continuousLinearMapOfBilin_sub`: `InnerProductSpace.continuousLinearMapOfBilin` is additive,
  being the composition `L ∘SL ·` with the fixed continuous linear map
  `L = (toDual ℝ E).symm`.
-/

namespace Commons.Analysis.Calculus.FDeriv

open scoped Topology
open Filter

/-- `InnerProductSpace.continuousLinearMapOfBilin` is additive: it is the composition
`L ∘SL ·` with the fixed continuous linear map `L = (toDual ℝ E).symm`. -/
lemma continuousLinearMapOfBilin_sub {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {A B : E →L⋆[ℝ] E →L[ℝ] ℝ} :
    InnerProductSpace.continuousLinearMapOfBilin (A - B)
      = InnerProductSpace.continuousLinearMapOfBilin A
        - InnerProductSpace.continuousLinearMapOfBilin B := by
  show ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap) ∘SL
      (A - B) = _
  rw [ContinuousLinearMap.comp_sub]
  rfl

/-- The second Fréchet derivative is additive with respect to subtraction of functions. -/
theorem fderiv_fderiv_sub_of_contDiffAt {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {φ ψ : E → ℝ} {x : E}
    (hφ : ContDiffAt ℝ 2 φ x) (hψ : ContDiffAt ℝ 2 ψ x) :
    fderiv ℝ (fderiv ℝ (φ - ψ)) x
      = fderiv ℝ (fderiv ℝ φ) x - fderiv ℝ (fderiv ℝ ψ) x := by
  have hφ_ev : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ φ y :=
    (hφ.eventually (by norm_num)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hψ_ev : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ ψ y :=
    (hψ.eventually (by norm_num)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hd : fderiv ℝ (φ - ψ) =ᶠ[𝓝 x] fun y => fderiv ℝ φ y - fderiv ℝ ψ y := by
    filter_upwards [hφ_ev, hψ_ev] with y h1 h2
    exact fderiv_fun_sub h1 h2
  have h1 : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have h2 : DifferentiableAt ℝ (fderiv ℝ ψ) x :=
    (hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  rw [hd.fderiv_eq, fderiv_fun_sub h1 h2]

theorem hessianWithin_sub_of_mem_nhds
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {φ ψ : E → ℝ} {s : Set E} {x : E} (hs : s ∈ nhds x)
    (hφ : ContDiffWithinAt ℝ 2 φ s x) (hψ : ContDiffWithinAt ℝ 2 ψ s x) :
    InnerProductSpace.continuousLinearMapOfBilin (fderivWithin ℝ (fderivWithin ℝ (φ - ψ) s) s x)
      = InnerProductSpace.continuousLinearMapOfBilin (fderivWithin ℝ (fderivWithin ℝ φ s) s x)
        - InnerProductSpace.continuousLinearMapOfBilin (fderivWithin ℝ (fderivWithin ℝ ψ s) s x) := by
  -- `s` is a neighbourhood of `x`, so `ContDiffWithinAt` upgrades to `ContDiffAt`.
  have hφ_at : ContDiffAt ℝ 2 φ x := hφ.contDiffAt hs
  have hψ_at : ContDiffAt ℝ 2 ψ x := hψ.contDiffAt hs
  -- Replace every within-derivative by the ordinary derivative, using `hs`.
  rw [hessianWithin_eq_hessian (E := E) (u := φ - ψ) hs,
      hessianWithin_eq_hessian (E := E) (u := φ) hs,
      hessianWithin_eq_hessian (E := E) (u := ψ) hs]
  -- Additivity of the second derivative under subtraction.
  rw [fderiv_fderiv_sub_of_contDiffAt hφ_at hψ_at]
  -- Additivity of `continuousLinearMapOfBilin`.
  exact continuousLinearMapOfBilin_sub

end Commons.Analysis.Calculus.FDeriv