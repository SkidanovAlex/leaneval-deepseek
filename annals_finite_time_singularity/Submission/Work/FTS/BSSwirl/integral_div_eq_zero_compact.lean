/-
# `∫ div G = 0` for a compactly supported `C¹` field on `ℝ³`

This module proves item (K) of the `BSSwirl` area:

  `∫ x, div G x = 0`  for every `G : ℝ³ → ℝ³` of class `C¹` with compact support,

which is the divergence theorem in its "no boundary term" form: a compactly supported
`C¹` field vanishes on the boundary of any large enough region, so the flux through that
boundary vanishes.  It is what lets the physical reconstruction discard the (weak) divergence
of the Biot–Savart potential without an integration-by-parts hypothesis.

## The argument

`div G x` is the trace of `fderiv ℝ G x`, and for an orthonormal basis `b` of `ℝ³`
(`LinearMap.trace_eq_sum_inner`)

  `trace (fderiv ℝ G x) = ∑ i, ⟪b i, (fderiv ℝ G x) (b i)⟫`.

Each term is, by `fderiv_inner_apply`, the directional derivative at `x` in direction `b i`
of the scalar function `y ↦ ⟪b i, G y⟫`:

  `⟪b i, (fderiv ℝ G x) (b i)⟫ = (fderiv ℝ (y ↦ ⟪b i, G y⟫) x) (b i)`.

So `∫ div G = ∑ i, ∫ (fderiv ℝ hᵢ x) (b i)`, and each summand vanishes by the
**integration by parts** for Fréchet derivatives
`integral_bilinear_fderiv_right_eq_neg_left_of_integrable`
(`Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean`) applied with the constant
function `1`: `∫ h · (fderiv 1) = - ∫ (fderiv h) · 1` gives `0 = - ∫ fderiv h`, since the
left-hand side is the integral of the zero function.  No boundary terms appear: the
integrability hypotheses are met because a compactly supported `C¹` function has a
compactly supported, continuous Fréchet derivative (`HasCompactSupport.fderiv_apply`,
`ContDiff.continuous_fderiv_apply`).

## Contents

* `integrable_fderiv_apply` — the directional derivative of a compactly supported `C¹`
  function is integrable;
* `integral_fderiv_apply_eq_zero` — **its integral vanishes** (the one-dimensional
  divergence theorem, via integration by parts against `1`);
* `integral_div_eq_zero_compact` — the target.
-/
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.Trace
import Submission.Work.FTS.BSSwirl.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set

namespace Work.FTS.BSSwirl

/-- The directional derivative of a compactly supported `C¹` function is integrable: it is
continuous (`ContDiff.continuous_fderiv_apply`) and has compact support
(`HasCompactSupport.fderiv_apply`). -/
lemma integrable_fderiv_apply {h : R3 → ℝ} (hh : ContDiff ℝ 1 h) (hcs : HasCompactSupport h)
    (v : R3) : Integrable (fun x => (fderiv ℝ h x) v) := by
  have hcont : Continuous (fun x : R3 => (fderiv ℝ h x) v) :=
    (hh.continuous_fderiv_apply one_ne_zero).comp (continuous_id.prodMk continuous_const)
  exact hcont.integrable_of_hasCompactSupport (hcs.fderiv_apply ℝ v)

/-- **The directional derivative of a compactly supported `C¹` function integrates to zero.**
This is the divergence theorem with no boundary term in one direction, obtained from the
integration-by-parts identity `∫ h · (fderiv 1) = - ∫ (fderiv h) · 1` with the constant
function `1`. -/
lemma integral_fderiv_apply_eq_zero {h : R3 → ℝ} (hh : ContDiff ℝ 1 h)
    (hcs : HasCompactSupport h) (v : R3) : ∫ x, (fderiv ℝ h x) v = 0 := by
  -- Integrability of the three products occurring in the integration-by-parts identity.
  have hint : Integrable (fun x : R3 => (fderiv ℝ h x) v * (1:ℝ)) := by
    simpa using integrable_fderiv_apply hh hcs v
  have hzero : Integrable (fun x : R3 => h x * (fderiv ℝ (fun _ : R3 => (1:ℝ)) x) v) := by
    have h1 : (fun x : R3 => h x * (fderiv ℝ (fun _ : R3 => (1:ℝ)) x) v) = fun _ => (0:ℝ) := by
      funext x
      simp
    rw [h1]
    exact integrable_zero _ _ _
  have hhint : Integrable (fun x : R3 => h x * (1:ℝ)) := by
    simpa using hh.continuous.integrable_of_hasCompactSupport hcs
  -- Integration by parts for Fréchet derivatives, with the second function constant `1`.
  have key := integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (E := R3) (F := ℝ) (G := ℝ) (W := ℝ) (f := h) (g := fun _ : R3 => (1:ℝ)) (v := v)
    (B := ContinuousLinearMap.mul ℝ ℝ) hint hzero hhint
    (fun x _ => (hh.differentiable one_ne_zero).differentiableAt)
    (fun x _ => differentiableAt_const (1:ℝ))
  have hL : ∫ x, (ContinuousLinearMap.mul ℝ ℝ) (h x) ((fderiv ℝ (fun _ : R3 => (1:ℝ)) x) v)
      = 0 := by
    simp
  rw [hL] at key
  simpa using key

/-- **The divergence of a compactly supported `C¹` vector field on `ℝ³` has zero integral.**

`div G x` is the trace of `fderiv ℝ G x`; expanded in the standard orthonormal basis it is the
sum of the directional derivatives of the scalar functions `y ↦ ⟪b i, G y⟫`, each of which
integrates to zero (`integral_fderiv_apply_eq_zero`). -/
theorem integral_div_eq_zero_compact {G : Work.FTS.BSSwirl.R3 → Work.FTS.BSSwirl.R3}
    (hG : ContDiff ℝ 1 G) (hcs : HasCompactSupport G) :
    ∫ x, FiniteTimeSingularity.div G x = 0 := by
  set b := EuclideanSpace.basisFun (Fin 3) ℝ with hb
  -- The trace of the derivative, expanded in the orthonormal basis `b`.
  have hderiv : ∀ x, FiniteTimeSingularity.div G x
      = ∑ i, (fderiv ℝ (fun y => inner ℝ (b i) (G y)) x) (b i) := by
    intro x
    rw [show FiniteTimeSingularity.div G x = (fderiv ℝ G x).trace ℝ R3 from rfl]
    rw [show (fderiv ℝ G x).trace ℝ R3
        = LinearMap.trace ℝ R3 (fderiv ℝ G x).toLinearMap from rfl]
    rw [LinearMap.trace_eq_sum_inner _ b]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [fderiv_inner_apply ℝ (differentiableAt_const (b i))
        ((hG.differentiable one_ne_zero) x) (b i)]
    simp
  -- The scalar functions `y ↦ ⟪b i, G y⟫` are again `C¹` with compact support.
  have hcont : ∀ i, ContDiff ℝ 1 (fun y => inner ℝ (b i) (G y)) := fun i => by
    have h : ContDiff ℝ 1 (fun y => ((innerSL ℝ) (b i)) (G y)) :=
      ((innerSL ℝ (b i) : R3 →L[ℝ] ℝ).contDiff).comp hG
    simpa only [innerSL_apply_apply] using h
  have hsupp : ∀ i, HasCompactSupport (fun y => inner ℝ (b i) (G y)) := fun i => by
    have h := hcs.comp_left (g := (innerSL ℝ (b i) : R3 →L[ℝ] ℝ)) (by simp)
    simpa only [Function.comp_def, innerSL_apply_apply] using h
  calc ∫ x, FiniteTimeSingularity.div G x
      = ∫ x, ∑ i, (fderiv ℝ (fun y => inner ℝ (b i) (G y)) x) (b i) := by
        refine integral_congr_ae ?_
        filter_upwards with x
        rw [hderiv x]
    _ = ∑ i, ∫ x, (fderiv ℝ (fun y => inner ℝ (b i) (G y)) x) (b i) := by
        rw [integral_finsetSum]
        intro i _
        exact integrable_fderiv_apply (hcont i) (hsupp i) (b i)
    _ = 0 := by
        refine Finset.sum_eq_zero (fun i _ => ?_)
        exact integral_fderiv_apply_eq_zero (hcont i) (hsupp i) (b i)

end Work.FTS.BSSwirl
