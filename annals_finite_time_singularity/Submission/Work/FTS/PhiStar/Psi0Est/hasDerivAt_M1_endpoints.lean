import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.PhiStar.Psi0Est.Defs
import Submission.Work.FTS.PhiStar.Psi0Ode

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Psi0Est

open scoped Real Topology ContDiff
open MeasureTheory Set Filter
open Asymptotics

/-! ## The two elementary derivative lemmas the endpoint argument needs

The proof of `hasDerivAt_M1_endpoints` splits `M1 α` into the sum of

* `A θ = 2cos(2θ)(Kc α + wZer α θ)`, whose derivative at an endpoint is governed by the
  fundamental theorem of calculus applied to `wZer = ∫_0^θ qfun α`; and
* `B θ = sin(2θ)·qfun α θ`, which vanishes at the endpoint and whose difference quotient is
  `O(θ-θ₀)·o(1) = o(θ-θ₀)`.

The second ingredient is the general lemma `hasDerivAt_mul_zero_tendsto` (differentiable
factor vanishing at the point, times a factor tending to `0`). -/

/-- If `f` is differentiable at `x` with `f x = 0` and `g → 0` at `x`, then `f·g` has
derivative `0` at `x`: the factor `f · - f x = f` is `O(· - x)` while `g` is `o(1)`. -/
theorem hasDerivAt_mul_zero_tendsto {f g : ℝ → ℝ} {x c : ℝ}
    (hf : HasDerivAt f c x) (hfx : f x = 0) (hg : Tendsto g (nhds x) (nhds 0)) :
    HasDerivAt (fun y => f y * g y) 0 x := by
  have hO : (fun y => f y - f x) =O[𝓝 x] (fun y => y - x) := hf.isBigO_sub
  have hL : (fun y => g y) =o[𝓝 x] (fun _ => (1 : ℝ)) := (isLittleO_one_iff ℝ).2 hg
  have hprod := hO.mul_isLittleO hL
  rw [hasDerivAt_iff_isLittleO]
  refine hprod.congr ?_ ?_
  · intro y
    simp only [hfx, zero_mul, sub_zero, smul_eq_mul, mul_zero]
  · intro y; ring

/-- `qfun α = Pfun α / sin²` is measurable. -/
lemma measurable_qfun' (α : ℝ) (hα : 0 ≤ α) : Measurable (qfun α) := by
  rw [show qfun α = fun θ : ℝ => Pfun α θ / Real.sin θ ^ 2 from rfl]
  exact (measurable_Pfun α hα).div (by fun_prop)

/-- **The endpoint derivatives of `M1`**: at a point `θ₀` where `sin(2θ₀) = 0`,
`qfun α θ₀ = 0`, the integrand `qfun α` is continuous at `θ₀` (hypothesis `hlim`) and
integrates on `[0,θ₀]`, the model `M1 α` has derivative `0`.

This is the common core of the two conjuncts: `wZer` is differentiated at the endpoint by the
fundamental theorem of calculus, `A` by the product rule (its derivative is a multiple of
`sin(2θ₀) = 0` plus `qfun α θ₀ = 0`), and `B` by `hasDerivAt_mul_zero_tendsto`. -/
private lemma hasDerivAt_M1_at (α : ℝ) (hα : 0 < α) {θ₀ : ℝ}
    (hsin : Real.sin (2 * θ₀) = 0) (hq0v : qfun α θ₀ = 0)
    (hlim : Tendsto (qfun α) (nhds θ₀) (nhds 0))
    (hint : IntervalIntegrable (qfun α) volume 0 θ₀) :
    HasDerivAt (M1 α) 0 θ₀ := by
  have hmeas : Measurable (qfun α) := measurable_qfun' α (le_of_lt hα)
  -- the derivative of `wZer` at the endpoint, from the FTC and continuity of the integrand
  have hw : HasDerivAt (wZer α) 0 θ₀ := by
    have hcont : ContinuousAt (qfun α) θ₀ := by
      show Tendsto (qfun α) (nhds θ₀) (nhds (qfun α θ₀))
      rw [hq0v]; exact hlim
    have hsm : StronglyMeasurableAtFilter (qfun α) (nhds θ₀) volume :=
      hmeas.aestronglyMeasurable.stronglyMeasurableAtFilter
    have h := intervalIntegral.integral_hasDerivAt_right (a := (0 : ℝ)) (b := θ₀)
      (f := qfun α) hint hsm hcont
    have h' : HasDerivAt (wZer α) (qfun α θ₀) θ₀ := by
      rw [← show wZer α = fun u => ∫ x in (0 : ℝ)..u, qfun α x from rfl] at h
      exact h
    rw [hq0v] at h'
    exact h'
  -- the derivative of `A θ = 2cos(2θ)(Kc α + wZer α θ)` is zero at the endpoint
  have hv1 : HasDerivAt (fun θ : ℝ => 2 * Real.cos (2 * θ)) (-4 * Real.sin (2 * θ₀)) θ₀ := by
    have h1 : HasDerivAt (fun θ : ℝ => (2 : ℝ) * θ) 2 θ₀ := by
      simpa using (hasDerivAt_id θ₀).const_mul (2 : ℝ)
    have h2 : HasDerivAt (fun θ : ℝ => Real.cos (2 * θ)) (-Real.sin (2 * θ₀) * 2) θ₀ := h1.cos
    have h3 := h2.const_mul (2 : ℝ)
    convert h3 using 1
    ring
  have hv2 : HasDerivAt (fun θ : ℝ => Kc α + wZer α θ) (qfun α θ₀) θ₀ := by
    rw [hq0v]; exact hw.const_add (Kc α)
  have hA : HasDerivAt (fun θ : ℝ => 2 * Real.cos (2 * θ) * (Kc α + wZer α θ)) 0 θ₀ :=
    (hv1.mul hv2).congr_deriv (by rw [hsin, hq0v]; ring)
  -- the derivative of `B θ = sin(2θ)·qfun α θ` is zero at the endpoint
  have hs : HasDerivAt (fun θ : ℝ => Real.sin (2 * θ)) (2 * Real.cos (2 * θ₀)) θ₀ := by
    have h1 : HasDerivAt (fun θ : ℝ => (2 : ℝ) * θ) 2 θ₀ := by
      simpa using (hasDerivAt_id θ₀).const_mul (2 : ℝ)
    have h2 := h1.sin
    convert h2 using 1
    ring
  have hB : HasDerivAt (fun θ : ℝ => Real.sin (2 * θ) * qfun α θ) 0 θ₀ :=
    hasDerivAt_mul_zero_tendsto hs hsin hlim
  have hM : (fun θ : ℝ => 2 * Real.cos (2 * θ) * (Kc α + wZer α θ)
      + Real.sin (2 * θ) * qfun α θ) = M1 α := rfl
  rw [← hM]
  refine (hA.add hB).congr_deriv ?_
  norm_num

/-- The model `M1 α` for `ψ'` is flat at the two endpoints: `HasDerivAt (M1 α) 0 θ` for
`θ = 0` and `θ = π/2`.

Write `M1 α θ = A θ + B θ` with `A θ = 2cos(2θ)(Kc α + wZer α θ)` and
`B θ = sin(2θ)·qfun α θ`.

The product rule together with `HasDerivAt wZer (qfun α θ) θ` (FTC plus continuity at the
endpoint, from the hypothesis) gives
`A' θ = 2(-2sin(2θ)(Kc + wZer θ) + cos(2θ)·qfun α θ)`, which is `0` at `θ = 0`
(`sin 0 = 0` and `qfun α 0 = Pfun α 0/0 = 0`) and at `θ = π/2` (`sin π = 0`, `cos π = -1`,
`qfun α (π/2) = Pfun α (π/2)/1 = Gzero α (π/2)/(2cos³(π/2)) = 0`).

The function `B` vanishes at both endpoints since `sin(2θ₀) = 0`, and
`(B θ - B θ₀)/(θ - θ₀) = (sin(2θ)/(θ-θ₀))·qfun α θ → 2cos(2θ₀)·0 = 0` by the hypothesis
`qfun α → 0` at the endpoint and `deriv (sin ∘ (2·)) θ₀ = 2cos(2θ₀)`, so
`HasDerivAt B 0 θ₀`.  Hence `HasDerivAt (M1 α) (0+0) θ₀`. -/
theorem hasDerivAt_M1_endpoints (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hq0 : Filter.Tendsto (Work.FTS.PhiStar.Psi0Est.qfun α) (nhds 0) (nhds 0))
    (hqπ : Filter.Tendsto (Work.FTS.PhiStar.Psi0Est.qfun α) (nhds (Real.pi / 2)) (nhds 0)) :
    HasDerivAt (Work.FTS.PhiStar.Psi0Est.M1 α) 0 0 ∧
      HasDerivAt (Work.FTS.PhiStar.Psi0Est.M1 α) 0 (Real.pi / 2) := by
  constructor
  · refine hasDerivAt_M1_at α hα (by simp) (by simp [qfun]) hq0 ?_
    refine ⟨?_, ?_⟩ <;> (rw [Set.Ioc_self]; exact integrableOn_empty)
  · refine hasDerivAt_M1_at α hα ?_ ?_ hqπ ?_
    · rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
    · simp [qfun, Pfun, Gzero]
    · have h := integrableOn_Pfun_div α hα hα1
      rw [intervalIntegrable_iff, Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
      rw [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)] at h
      exact h.mono_set Set.Ioc_subset_Icc_self

end Work.FTS.PhiStar.Psi0Est
