/-
Copyright: work module for the Elgindi finite-time singularity project.

# Angular integration by parts in the `∂_θ`-form, with the relaxed exponent range

The "hard" (order-five) terms of the pairing `(f ∂_θ g, g)_{ℋ⁴}` of Elgindi's Proposition
`SpecialTransport` (§`H2`, tex 1126) have the shape

  `∫_θ f(z,θ)·∂_θ v(z,θ)·v(z,θ)·sin(2θ)^{-q} dθ`

with `v = D_z^j D_θ^i g` an `g`-block and `q = η` (the `D_z`-slot) or `q = γ` (the mixed
slots).  The identity proved here is the one obtained from the primitive

  `F(θ) = (1/2)·sin(2θ)^{-q}·f(z,θ)·v(z,θ)²`,

whose derivative on the open interval is
`sin(2θ)^{-q}·(f·∂_θv·v - q·cos(2θ)·sin(2θ)^{-1}·f·v² + v²·∂_θf/2)`;  the fundamental theorem
of calculus (the boundary terms vanishing because `sin(2θ)^{-q}·f(z,θ)·v(z,θ)² → 0`) gives

  `∫_θ f ∂_θv·v·sin(2θ)^{-q}
     = ∫_θ (q·cos(2θ)·sin(2θ)^{-q-1}·f - (1/2)·sin(2θ)^{-q}·∂_θf)·v²`.

Compared with `Work.FTS.H2.IBPWeight.ibp_hard` this version

* uses `∂_θv` (not `D_θv`) and therefore needs the *failing* exponent range `q < 3` rather
  than `q < 2` — which is what the mixed slots require, since `h = f/sin(2θ)` turns
  `h·D_θv` into `f·∂_θv`;
* only asks for interior differentiability of the `θ`-slices of `f` (which is what
  `Spaces.SmoothInt` provides), so it applies to `f` itself rather than to the multiplier
  `h = f/sin(2θ)` (which is *not* smooth on a neighbourhood of the closed quadrant).

The exponent hypotheses `0 < q`, `q < 2` of `ibp_hard` are in any case unused by its proof,
so no exponent restriction is imposed here at all.
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.H2.STBounds2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Derivative of the primitive `θ ↦ (1/2)·sin(2θ)^{-q}·f(z,θ)·v(z,θ)²` at an interior point,
in raw product-rule form. -/
theorem ibp_prim_hasDerivAt' (q : ℝ) (f v : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hf : HasDerivAt (fun θ' => f z θ') (Spaces.pth f z θ) θ)
    (hv : HasDerivAt (fun θ' => v z θ') (Spaces.pth v z θ) θ)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun t => (1 / 2) * (Real.sin (2 * t)) ^ (-q) * f z t * (v z t) ^ 2)
      ((1 / 2) * ((2 * Real.cos (2 * θ) * (-q) * (Real.sin (2 * θ)) ^ (-q - 1))
            * f z θ * (v z θ) ^ 2
          + (Real.sin (2 * θ)) ^ (-q) * Spaces.pth f z θ * (v z θ) ^ 2
          + (Real.sin (2 * θ)) ^ (-q) * f z θ * (2 * v z θ * Spaces.pth v z θ))) θ := by
  have hsin : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ (-q))
      (2 * Real.cos (2 * θ) * (-q) * (Real.sin (2 * θ)) ^ (-q - 1)) θ :=
    hasDerivAt_sin_rpow_neg q θ hθ
  have hv2 : HasDerivAt (fun t : ℝ => (v z t) ^ 2) (2 * v z θ * Spaces.pth v z θ) θ := by
    have h : HasDerivAt (fun t : ℝ => v z t * v z t)
        (Spaces.pth v z θ * v z θ + v z θ * Spaces.pth v z θ) θ := hv.mul hv
    convert h using 1
    · funext t; ring
    · ring
  have h1 : HasDerivAt (fun t => (1 / 2) * (Real.sin (2 * t)) ^ (-q))
      ((1 / 2) * (2 * Real.cos (2 * θ) * (-q) * (Real.sin (2 * θ)) ^ (-q - 1))) θ :=
    hsin.const_mul (1 / 2)
  have h2 : HasDerivAt (fun t => (1 / 2) * (Real.sin (2 * t)) ^ (-q) * f z t)
      ((1 / 2) * (2 * Real.cos (2 * θ) * (-q) * (Real.sin (2 * θ)) ^ (-q - 1)) * f z θ
        + (1 / 2) * (Real.sin (2 * θ)) ^ (-q) * Spaces.pth f z θ) θ := h1.mul hf
  have h3 : HasDerivAt
      (fun t => (1 / 2) * (Real.sin (2 * t)) ^ (-q) * f z t * (v z t) ^ 2)
      (((1 / 2) * (2 * Real.cos (2 * θ) * (-q) * (Real.sin (2 * θ)) ^ (-q - 1)) * f z θ
          + (1 / 2) * (Real.sin (2 * θ)) ^ (-q) * Spaces.pth f z θ) * (v z θ) ^ 2
        + ((1 / 2) * (Real.sin (2 * θ)) ^ (-q) * f z θ)
            * (2 * v z θ * Spaces.pth v z θ)) θ := h2.mul hv2
  convert h3 using 1
  ring

/-- **Angular integration by parts in the `∂_θ`-form**, with the weight `sin(2θ)^{-q}` and no
restriction on `q`. -/
theorem ibp_partial (q : ℝ) (f v : ℝ → ℝ → ℝ) {z : ℝ}
    (hf : ∀ θ ∈ Set.Ioo 0 (π / 2), HasDerivAt (fun θ' => f z θ') (Spaces.pth f z θ) θ)
    (hv : ∀ θ ∈ Set.Ioo 0 (π / 2), HasDerivAt (fun θ' => v z θ') (Spaces.pth v z θ) θ)
    (hvan : Tendsto (fun θ => (Real.sin (2 * θ)) ^ (-q) * f z θ * (v z θ) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hvan2 : Tendsto (fun θ => (Real.sin (2 * θ)) ^ (-q) * f z θ * (v z θ) ^ 2)
      (𝓝[<] (π / 2)) (𝓝 0))
    (hint : IntervalIntegrable (fun θ => (Real.sin (2 * θ)) ^ (-q) * f z θ
        * Spaces.pth v z θ * v z θ
      - q * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q - 1) * f z θ * (v z θ) ^ 2
      + (1 / 2) * (Real.sin (2 * θ)) ^ (-q) * Spaces.pth f z θ * (v z θ) ^ 2)
      volume 0 (π / 2))
    (hint1 : IntervalIntegrable (fun θ => (Real.sin (2 * θ)) ^ (-q) * f z θ
        * Spaces.pth v z θ * v z θ) volume 0 (π / 2))
    (hint2 : IntervalIntegrable (fun θ => (1 / 2) * (Real.sin (2 * θ)) ^ (-q)
        * Spaces.pth f z θ * (v z θ) ^ 2) volume 0 (π / 2))
    (hint3 : IntervalIntegrable (fun θ => q * Real.cos (2 * θ)
        * (Real.sin (2 * θ)) ^ (-q - 1) * f z θ * (v z θ) ^ 2) volume 0 (π / 2)) :
    ∫ θ in Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q) * f z θ * Spaces.pth v z θ * v z θ
      = ∫ θ in Spaces.Iθ, (q * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q - 1) * f z θ
          - (1 / 2) * (Real.sin (2 * θ)) ^ (-q) * Spaces.pth f z θ) * (v z θ) ^ 2 := by
  have hpi : (0 : ℝ) < π / 2 := by positivity
  have hIcc : ∀ u : ℝ → ℝ, ∫ θ in Spaces.Iθ, u θ = ∫ θ in (0 : ℝ)..(π / 2), u θ := by
    intro u
    rw [show Spaces.Iθ = Set.Icc 0 (π / 2) from rfl,
      MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hpi.le]
  set A : ℝ → ℝ := fun θ => (Real.sin (2 * θ)) ^ (-q) * f z θ * Spaces.pth v z θ * v z θ
    with hA
  set B : ℝ → ℝ := fun θ => q * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q - 1)
    * f z θ * (v z θ) ^ 2 with hB
  set C : ℝ → ℝ := fun θ => (1 / 2) * (Real.sin (2 * θ)) ^ (-q) * Spaces.pth f z θ
    * (v z θ) ^ 2 with hC
  have hderiv' : ∀ t ∈ Set.Ioo (0 : ℝ) (π / 2),
      HasDerivAt (fun θ => (1 / 2) * (Real.sin (2 * θ)) ^ (-q) * f z θ * (v z θ) ^ 2)
        (A t - B t + C t) t := by
    intro t ht
    have h := ibp_prim_hasDerivAt' q f v (hf t ht) (hv t ht) ht
    convert h using 1
    simp only [hA, hB, hC]
    ring
  have hFTC : (∫ t in (0 : ℝ)..(π / 2), (A t - B t + C t)) = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hpi hderiv' hint
      (by simpa only [mul_assoc] using hvan.const_mul (1 / 2))
      (by simpa only [mul_assoc] using hvan2.const_mul (1 / 2))
    simpa using h
  have hsplit : (∫ t in (0 : ℝ)..(π / 2), (A t - B t + C t))
      = (∫ t in (0 : ℝ)..(π / 2), A t) - (∫ t in (0 : ℝ)..(π / 2), B t)
        + (∫ t in (0 : ℝ)..(π / 2), C t) := by
    rw [intervalIntegral.integral_add (hint1.sub hint3) hint2,
      intervalIntegral.integral_sub hint1 hint3]
  have hAeq : (∫ t in (0 : ℝ)..(π / 2), A t)
      = (∫ t in (0 : ℝ)..(π / 2), B t) - (∫ t in (0 : ℝ)..(π / 2), C t) := by
    linarith [hFTC, hsplit]
  have hbc : (∫ t in (0 : ℝ)..(π / 2),
        (fun θ => (q * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q - 1) * f z θ
          - (1 / 2) * (Real.sin (2 * θ)) ^ (-q) * Spaces.pth f z θ) * (v z θ) ^ 2) t)
      = (∫ t in (0 : ℝ)..(π / 2), B t) - (∫ t in (0 : ℝ)..(π / 2), C t) := by
    have hfun : (fun θ => (q * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q - 1) * f z θ
          - (1 / 2) * (Real.sin (2 * θ)) ^ (-q) * Spaces.pth f z θ) * (v z θ) ^ 2)
        = fun θ => B θ - C θ := by
      funext θ
      simp only [hB, hC]
      ring
    rw [hfun, intervalIntegral.integral_sub hint3 hint2]
  rw [hIcc, hIcc, hbc, hAeq]

end Work.FTS.H2
