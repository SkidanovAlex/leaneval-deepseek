/-
# Integration by parts in a single coordinate direction

From `Work.FTS.PressureOn.integral_inner_gradient_mul_eq_neg` (the vector-field integration by
parts, proved in `PoissonAux/Ibp.lean`) we obtain the coordinate forms:

* `integral_fderiv_mul_eq_zero` — `∫ x, ∂ᵢ(g · h) x = 0` for `h` of compact support;
* `integral_fderiv_mul_eq_neg` — `∫ x, ∂ᵢg x * h x = -∫ x, g x * ∂ᵢh x`.

Here `∂ᵢg x = fderiv ℝ g x (e i)` with `e i = WithLp.toLp 2 (Pi.single i 1)`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.integral_div_eq_zero_of_hasFDerivAt
import Submission.Work.FTS.PressureOn.PoissonAux.Defs
import Submission.Work.FTS.PressureOn.PoissonAux.Ibp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory Metric Gradient
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn

/-- The partial derivatives of a `C²` function are `C¹`. -/
lemma contDiff_fderiv_apply_e {u : R3 → ℝ} (hu : ContDiff ℝ 2 u) (i : Fin 3) :
    ContDiff ℝ 1 (fun x : R3 => fderiv ℝ u x (e i)) := by
  have h : ContDiff ℝ 1 (fun p : R3 × R3 => fderiv ℝ u p.1 p.2) :=
    ContDiff.contDiff_fderiv_apply hu (by norm_num)
  have h2 : ContDiff ℝ 1 (fun x : R3 => (x, e i)) := by
    have h3 : ContDiff ℝ 1 (fun x : R3 => ((x, (0 : R3)) : R3 × R3)) :=
      (ContinuousLinearMap.inl ℝ R3 R3).contDiff
    simpa using h3.add (contDiff_const (c := ((0 : R3), e i)))
  exact h.comp h2

/-- The partial derivatives of a compactly supported function have compact support. -/
lemma hasCompactSupport_fderiv_apply_e {v : R3 → ℝ} (hvcs : HasCompactSupport v) (i : Fin 3) :
    HasCompactSupport (fun x : R3 => fderiv ℝ v x (e i)) := by
  refine hvcs.mono' ?_
  intro x hx
  by_contra hxt
  rw [Function.mem_support] at hx
  exact hx (by
    rw [fderiv_eq_zero_of_notMem_tsupport hxt]
    simp)

/-- **The product form.**  For `C¹` functions `g`, `h` with `h` of compact support,
`∫ x, ∂ᵢ(g · h) x = 0`. -/
theorem integral_fderiv_mul_eq_zero {g h : R3 → ℝ} (hg : ContDiff ℝ 1 g) (hh : ContDiff ℝ 1 h)
    (hcs : HasCompactSupport h) (i : Fin 3) :
    ∫ x, fderiv ℝ (g * h) x (e i) = 0 := by
  have hsm : ContDiff ℝ 1 (fun x : R3 => (g * h) x • e i) := (hg.mul hh).smul contDiff_const
  have hcsm : HasCompactSupport (fun x : R3 => (g * h) x • e i) := hcs.mono' (by
    intro x hx
    by_contra hxt
    rw [Function.mem_support] at hx
    exact hx (by simp [image_eq_zero_of_notMem_tsupport hxt]))
  have hdiv : div (fun x : R3 => (g * h) x • e i) = fun x => fderiv ℝ (g * h) x (e i) := by
    funext x
    show div (fun y : R3 => (g y * h y) • e i) x = fderiv ℝ (fun y : R3 => g y * h y) x (e i)
    rw [div_smul (hg.mul hh) contDiff_const x, div_const, mul_zero, zero_add,
      inner_gradient_left]
  have h0 : ∫ x, div (fun y : R3 => (g * h) y • e i) x = 0 :=
    integral_div_eq_zero_of_hasFDerivAt _ hcsm hsm.continuous
      (fun x => (hsm.differentiable_one x).hasFDerivAt)
      (integrable_div_of_contDiff hsm hcsm)
  rwa [hdiv] at h0

/-- **Integration by parts in one coordinate direction.**  For `C¹` functions `g`, `h` with `h` of
compact support, `∫ x, ∂ᵢg x * h x = -∫ x, g x * ∂ᵢh x`. -/
theorem integral_fderiv_mul_eq_neg {g h : R3 → ℝ} (hg : ContDiff ℝ 1 g) (hh : ContDiff ℝ 1 h)
    (hcs : HasCompactSupport h) (i : Fin 3) :
    ∫ x, fderiv ℝ g x (e i) * h x = -∫ x, g x * fderiv ℝ h x (e i) := by
  have h0 := integral_fderiv_mul_eq_zero hg hh hcs i
  have hfun : (fun x => fderiv ℝ (g * h) x (e i))
      = fun x => fderiv ℝ g x (e i) * h x + g x * fderiv ℝ h x (e i) := by
    funext x
    rw [((hg.differentiable_one x).hasFDerivAt.mul
      (hh.differentiable_one x).hasFDerivAt).fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  rw [hfun] at h0
  have hcontA : Continuous fun x : R3 => fderiv ℝ g x (e i) * h x :=
    ((hg.continuous_fderiv_apply one_ne_zero).comp
      (continuous_id.prodMk continuous_const)).mul hh.continuous
  have hIntA : Integrable fun x : R3 => fderiv ℝ g x (e i) * h x := by
    refine Continuous.integrable_of_hasCompactSupport hcontA (hcs.mono' ?_)
    intro x hx
    by_contra hxt
    rw [Function.mem_support] at hx
    exact hx (by simp [image_eq_zero_of_notMem_tsupport hxt])
  have hcontB : Continuous fun x : R3 => g x * fderiv ℝ h x (e i) :=
    hg.continuous.mul ((hh.continuous_fderiv_apply one_ne_zero).comp
      (continuous_id.prodMk continuous_const))
  have hIntB : Integrable fun x : R3 => g x * fderiv ℝ h x (e i) := by
    refine Continuous.integrable_of_hasCompactSupport hcontB
      ((hasCompactSupport_fderiv_apply_e hcs i).mono' ?_)
    intro x hx
    by_contra hxt
    rw [Function.mem_support] at hx
    exact hx (by simp [image_eq_zero_of_notMem_tsupport hxt])
  rw [integral_add hIntA hIntB] at h0
  linarith

end Work.FTS.PressureOn
