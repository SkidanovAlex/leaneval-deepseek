import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PressureOn.Auxiliary.HeatKernel

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `laplaceTrace` is invariant under the reflection `y' ↦ x - y'`

The Laplace trace `laplaceTrace φ x = ∑ᵢ ∂ᵢ∂ᵢ φ(x)` of a function on `ℝ³` is unchanged by
precomposing `φ` with the reflection `y' ↦ x - y'`:

`laplaceTrace (fun y' => φ (x - y')) y = laplaceTrace φ (x - y)`.

This is the second-derivative chain rule for the affine substitution `y' ↦ x - y'` (whose Fréchet
derivative is the constant `-1` and whose second derivative vanishes), applied twice: the first
derivative of `φ (x - ·)` at `w` is `-(fderiv ℝ φ (x - w))`, and differentiating once more the two
signs cancel against the sign produced by evaluating the reflection at `eᵢ`.

The pointwise inputs are the Mathlib chain rule `fderiv_comp` and the fact that
`fderiv ℝ (fun y' => x - y') w = -1`.
-/

set_option autoImplicit false

namespace Work.FTS.PressureOn.Auxiliary

open scoped Topology

/-- The Fréchet derivative of the reflection `y' ↦ x - y'` is the constant `-1`. -/
private lemma fderiv_sub_const_id (x w : R3) :
    fderiv ℝ (fun y' : R3 => x - y') w = -(1 : R3 →L[ℝ] R3) := by
  have hid : HasFDerivAt (fun y : R3 => y) (1 : R3 →L[ℝ] R3) w := hasFDerivAt_id w
  simpa using (hid.const_sub x).fderiv

/-- First-order chain rule for the substitution `y' ↦ x - y'`: the derivative of `f (x - ·)` at
`w` is `-(fderiv ℝ f (x - w))`. -/
private lemma fderiv_comp_sub_left (f : R3 → ℝ) (hf : Differentiable ℝ f) (x w : R3) :
    fderiv ℝ (fun y' : R3 => f (x - y')) w = -(fderiv ℝ f (x - w)) := by
  have hTdiff : DifferentiableAt ℝ (fun y' : R3 => x - y') w :=
    (differentiableAt_const x).sub differentiableAt_id
  have hcomp := fderiv_comp (𝕜 := ℝ) (x := w) (f := fun y' : R3 => x - y') (g := f)
    (hf (x - w)) hTdiff
  change fderiv ℝ (f ∘ (fun y' : R3 => x - y')) w = -(fderiv ℝ f (x - w))
  rw [hcomp, fderiv_sub_const_id x w]
  rw [show (-(1 : R3 →L[ℝ] R3)) = -(ContinuousLinearMap.id ℝ R3) from rfl,
    ContinuousLinearMap.comp_neg, ContinuousLinearMap.comp_id]

/-- Second-order chain rule for the substitution `y' ↦ x - y'`, one coordinate at a time: the
second derivative of `f (x - ·)` in the direction `eᵢ`, at `y`, equals the second derivative of `f`
at `x - y`. -/
private lemma fderiv_fderiv_comp_sub_left (f : R3 → ℝ) (hf : ContDiff ℝ 2 f) (x y : R3)
    (i : Fin 3) :
    fderiv ℝ (fun w : R3 => fderiv ℝ (fun y' : R3 => f (x - y')) w
        (FiniteTimeSingularity.e i)) y (FiniteTimeSingularity.e i)
      = fderiv ℝ (fun w : R3 => fderiv ℝ f w (FiniteTimeSingularity.e i)) (x - y)
        (FiniteTimeSingularity.e i) := by
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  set G : R3 → ℝ := fun t => fderiv ℝ f t (FiniteTimeSingularity.e i) with hG
  have hC1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (m := 1) (by norm_num)
  have hgd : Differentiable ℝ G := by
    have h := (((ContinuousLinearMap.apply ℝ ℝ) (FiniteTimeSingularity.e i)).differentiable.comp
      (hC1.differentiable (by norm_num)))
    simpa [hG, Function.comp_def, ContinuousLinearMap.apply_apply] using h
  have h1 : (fun w : R3 => fderiv ℝ (fun y' : R3 => f (x - y')) w
        (FiniteTimeSingularity.e i))
      = fun w : R3 => - G (x - w) := by
    funext w
    rw [fderiv_comp_sub_left f hfd x w]
    rfl
  rw [h1, fderiv_fun_neg, fderiv_comp_sub_left G hgd x y]
  simp

theorem laplaceTrace_comp_sub (f : Work.FTS.PressureOn.R3 → ℝ) (hf : ContDiff ℝ 2 f)
    (x y : Work.FTS.PressureOn.R3) :
    Work.FTS.PressureOn.laplaceTrace (fun y' : Work.FTS.PressureOn.R3 => f (x - y')) y
      = Work.FTS.PressureOn.laplaceTrace f (x - y) := by
  rw [laplaceTrace, laplaceTrace]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact fderiv_fderiv_comp_sub_left f hf x y i

end Work.FTS.PressureOn.Auxiliary
