/-
Copyright: work module for the Elgindi finite-time singularity project.

# Angular integration by parts with a general smooth weight

The "hard" (order-five) terms of the pairing `(f D_θ g, g)_{ℋ⁴}` of Elgindi's Lemma
`Transport1` have the shape

  `∫_θ f(z,θ)·D_θ(v)(z,θ)·v(z,θ)·sin(2θ)^{-q} dθ`

with `v = D_z^j D_θ^i g` an order-four `g`-block, `q = η` (the `D_z`-slot) or `q = γ`
(the mixed slots) and an extra factor `f` which is *not* differentiated.  The available
`Work.Coercivity.slice_ibp_gen` only covers the case `f ≡ 1`.

The identity is obtained from the primitive

  `F(θ) = (1/2)·sin(2θ)^{1-q}·f(z,θ)·v(z,θ)²`,

whose derivative is `sin(2θ)^{-q}·(f·D_θv·v + v²·(D_θf/2 + (1-q)cos(2θ)f))` on the open
interval; the fundamental theorem of calculus (with the boundary terms vanishing because
`1 - q > 0`) gives

  `∫_θ f D_θv·v·sin(2θ)^{-q} = -∫_θ v²·(D_θf/2 + (1-q)cos(2θ)f)·sin(2θ)^{-q}`.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.H2.Defs
import Submission.Work.Coercivity.slice_ibp

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

/-- The angular-slice differentiability of a `SmoothNbhd` function at interior points. -/
theorem differentiableAt_slice (v : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd v) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) : DifferentiableAt ℝ (fun θ' => v z θ') θ :=
  Work.Coercivity.smoothNbhd_slice_differentiableAt v hsm hz hθ

/-- Derivative of the primitive `θ ↦ (1/2)·sin(2θ)^{1-q}·f(z,θ)·v(z,θ)²` at an interior point,
written in the form produced by the product rule. -/
theorem ibp_prim_hasDerivAt (q : ℝ) (f v : ℝ → ℝ → ℝ) (hsmf : Spaces.SmoothNbhd f)
    (hsmv : Spaces.SmoothNbhd v) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun t => (1 / 2) * (Real.sin (2 * t)) ^ (1 - q) * f z t * (v z t) ^ 2)
      ((Real.sin (2 * θ)) ^ (-q) * (f z θ * Spaces.Dth v z θ * v z θ
        + (v z θ) ^ 2 * (Spaces.Dth f z θ / 2
            + (1 - q) * Real.cos (2 * θ) * f z θ))) θ := by
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hsinne : Real.sin (2 * θ) ≠ 0 := ne_of_gt hsin
  have hs2 : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (2 * Real.cos (2 * θ)) θ := by
    have h1 : HasDerivAt (fun t : ℝ => 2 * t) (2 : ℝ) θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    have h := (Real.hasDerivAt_sin (2 * θ)).comp θ h1
    simpa only [Function.comp_def, mul_comm] using h
  have hpow : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ (1 - q))
      ((1 - q) * (Real.sin (2 * θ)) ^ (1 - q - 1) * (2 * Real.cos (2 * θ))) θ := by
    have h := (Real.hasDerivAt_rpow_const (x := Real.sin (2 * θ)) (p := 1 - q)
      (Or.inl hsinne)).comp θ hs2
    simpa only [Function.comp_def] using h
  have hf : HasDerivAt (fun t : ℝ => f z t) (Spaces.pth f z θ) θ :=
    (differentiableAt_slice f hsmf hz hθ).hasDerivAt
  have hv : HasDerivAt (fun t : ℝ => v z t) (Spaces.pth v z θ) θ :=
    (differentiableAt_slice v hsmv hz hθ).hasDerivAt
  have hv2 : HasDerivAt (fun t : ℝ => (v z t) ^ 2) (2 * v z θ * Spaces.pth v z θ) θ := by
    have h : HasDerivAt (fun t : ℝ => v z t * v z t)
        (Spaces.pth v z θ * v z θ + v z θ * Spaces.pth v z θ) θ := hv.mul hv
    convert h using 1
    · funext t; ring
    · ring
  -- the primitive and its derivative, in raw product-rule form
  have hmain : HasDerivAt (fun t => (1 / 2) * (Real.sin (2 * t)) ^ (1 - q) * f z t * (v z t) ^ 2)
      ((1 / 2) * (((1 - q) * (Real.sin (2 * θ)) ^ (1 - q - 1) * (2 * Real.cos (2 * θ)))
          * f z θ * (v z θ) ^ 2
        + (Real.sin (2 * θ)) ^ (1 - q) * Spaces.pth f z θ * (v z θ) ^ 2
        + (Real.sin (2 * θ)) ^ (1 - q) * f z θ * (2 * v z θ * Spaces.pth v z θ))) θ := by
    have h1 : HasDerivAt (fun t => (1 / 2) * (Real.sin (2 * t)) ^ (1 - q))
        ((1 / 2) * ((1 - q) * (Real.sin (2 * θ)) ^ (1 - q - 1) * (2 * Real.cos (2 * θ)))) θ :=
      hpow.const_mul (1 / 2)
    have h2 : HasDerivAt (fun t => (1 / 2) * (Real.sin (2 * t)) ^ (1 - q) * f z t)
        ((1 / 2) * ((1 - q) * (Real.sin (2 * θ)) ^ (1 - q - 1) * (2 * Real.cos (2 * θ))) * f z θ
          + (1 / 2) * (Real.sin (2 * θ)) ^ (1 - q) * Spaces.pth f z θ) θ := h1.mul hf
    have h3 : HasDerivAt
        (fun t => (1 / 2) * (Real.sin (2 * t)) ^ (1 - q) * f z t * (v z t) ^ 2)
        (((1 / 2) * ((1 - q) * (Real.sin (2 * θ)) ^ (1 - q - 1) * (2 * Real.cos (2 * θ))) * f z θ
            + (1 / 2) * (Real.sin (2 * θ)) ^ (1 - q) * Spaces.pth f z θ) * (v z θ) ^ 2
          + ((1 / 2) * (Real.sin (2 * θ)) ^ (1 - q) * f z θ)
              * (2 * v z θ * Spaces.pth v z θ)) θ := h2.mul hv2
    convert h3 using 1
    ring
  -- the `rpow` bookkeeping
  have hA : (Real.sin (2 * θ)) ^ (-q) = (Real.sin (2 * θ)) ^ (1 - q - 1) := by
    rw [show 1 - q - 1 = -q by ring]
  have hB : (Real.sin (2 * θ)) ^ (1 - q)
      = (Real.sin (2 * θ)) ^ (1 - q - 1) * Real.sin (2 * θ) := by
    have h1 : (Real.sin (2 * θ)) ^ (1 - q - 1) * Real.sin (2 * θ)
        = (Real.sin (2 * θ)) ^ (1 - q - 1) * (Real.sin (2 * θ)) ^ (1 : ℝ) := by
      rw [Real.rpow_one]
    rw [h1, ← Real.rpow_add hsin, show 1 - q - 1 + 1 = 1 - q by ring]
  have hDth : Spaces.Dth v z θ = Real.sin (2 * θ) * Spaces.pth v z θ := rfl
  have hDthf : Spaces.Dth f z θ = Real.sin (2 * θ) * Spaces.pth f z θ := rfl
  convert hmain using 1
  rw [hDth, hDthf, hA, hB]
  ring

/-- **Angular integration by parts with a general weight.**  For `q ∈ (0,2)`, `z > 0`, `f`, `v`
smooth on a neighbourhood of the closed quadrant, and with the boundary terms
`sin(2θ)^{1-q}·f(z,θ)·v(z,θ)² → 0` at `θ → 0⁺` and `θ → π/2⁻`,
`∫_θ f·D_θ(v)·v·sin(2θ)^{-q} = -∫_θ v²·(D_θf/2 + (1-q)cos(2θ)·f)·sin(2θ)^{-q}`.

The two `IntervalIntegrable` hypotheses are the interval-integrability of the derivative
integrand `sin(2θ)^{-q}·(f D_θv·v + v²(D_θf/2 + (1-q)cos(2θ)f))` and of its second summand
`sin(2θ)^{-q}·v²(D_θf/2 + (1-q)cos(2θ)f)`; their difference is `sin(2θ)^{-q}·f·D_θv·v`, whose
integral is the left-hand side. -/
theorem ibp_hard (q : ℝ) (f v : ℝ → ℝ → ℝ) (hsmf : Spaces.SmoothNbhd f)
    (hsmv : Spaces.SmoothNbhd v) (hq0 : 0 < q) (hq2 : q < 2) {z : ℝ} (hz : 0 < z)
    (hvan : Filter.Tendsto (fun θ => (Real.sin (2 * θ)) ^ (1 - q) * (f z θ * (v z θ) ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hvan2 : Filter.Tendsto (fun θ => (Real.sin (2 * θ)) ^ (1 - q) * (f z θ * (v z θ) ^ 2))
      (𝓝[<] (π / 2)) (𝓝 0))
    (hint : IntervalIntegrable (fun θ => (Real.sin (2 * θ)) ^ (-q)
        * (f z θ * Spaces.Dth v z θ * v z θ
          + (v z θ) ^ 2 * (Spaces.Dth f z θ / 2
              + (1 - q) * Real.cos (2 * θ) * f z θ))) volume 0 (π / 2))
    (hK : IntervalIntegrable (fun θ => (v z θ) ^ 2 * (Spaces.Dth f z θ / 2
              + (1 - q) * Real.cos (2 * θ) * f z θ) * (Real.sin (2 * θ)) ^ (-q))
      volume 0 (π / 2)) :
    ∫ θ in Spaces.Iθ, f z θ * Spaces.Dth v z θ * v z θ * (Real.sin (2 * θ)) ^ (-q)
      = -∫ θ in Spaces.Iθ, (v z θ) ^ 2 * (Spaces.Dth f z θ / 2
          + (1 - q) * Real.cos (2 * θ) * f z θ) * (Real.sin (2 * θ)) ^ (-q) := by
  have hpi : (0 : ℝ) < π / 2 := by positivity
  have hIcc : ∀ u : ℝ → ℝ, ∫ θ in Spaces.Iθ, u θ = ∫ θ in (0 : ℝ)..(π / 2), u θ := by
    intro u
    rw [show Spaces.Iθ = Set.Icc 0 (π / 2) from rfl,
      MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hpi.le]
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) (π / 2),
      HasDerivAt (fun θ => (1 / 2) * (Real.sin (2 * θ)) ^ (1 - q) * f z θ * (v z θ) ^ 2)
        ((Real.sin (2 * t)) ^ (-q) * (f z t * Spaces.Dth v z t * v z t
          + (v z t) ^ 2 * (Spaces.Dth f z t / 2
              + (1 - q) * Real.cos (2 * t) * f z t))) t :=
    fun t ht => ibp_prim_hasDerivAt q f v hsmf hsmv hz ht
  have hFTC : (∫ t in (0 : ℝ)..(π / 2), (Real.sin (2 * t)) ^ (-q)
      * (f z t * Spaces.Dth v z t * v z t
        + (v z t) ^ 2 * (Spaces.Dth f z t / 2 + (1 - q) * Real.cos (2 * t) * f z t))) = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hpi
      (f := fun θ => (1 / 2) * (Real.sin (2 * θ)) ^ (1 - q) * f z θ * (v z θ) ^ 2)
      (f' := fun t => (Real.sin (2 * t)) ^ (-q) * (f z t * Spaces.Dth v z t * v z t
        + (v z t) ^ 2 * (Spaces.Dth f z t / 2 + (1 - q) * Real.cos (2 * t) * f z t)))
      hderiv hint (by simpa only [mul_assoc] using hvan.const_mul (1 / 2))
      (by simpa only [mul_assoc] using hvan2.const_mul (1 / 2))
    simpa using h
  have hA : IntervalIntegrable (fun θ => f z θ * Spaces.Dth v z θ * v z θ
      * (Real.sin (2 * θ)) ^ (-q)) volume 0 (π / 2) := by
    have hsub := hint.sub hK
    have hfun : (fun θ => (Real.sin (2 * θ)) ^ (-q)
          * (f z θ * Spaces.Dth v z θ * v z θ
            + (v z θ) ^ 2 * (Spaces.Dth f z θ / 2 + (1 - q) * Real.cos (2 * θ) * f z θ))
        - (v z θ) ^ 2 * (Spaces.Dth f z θ / 2 + (1 - q) * Real.cos (2 * θ) * f z θ)
            * (Real.sin (2 * θ)) ^ (-q))
        = fun θ => f z θ * Spaces.Dth v z θ * v z θ * (Real.sin (2 * θ)) ^ (-q) := by
      funext θ; ring
    rw [hfun] at hsub
    exact hsub
  have hsum : (∫ t in (0 : ℝ)..(π / 2), f z t * Spaces.Dth v z t * v z t
        * (Real.sin (2 * t)) ^ (-q))
      + (∫ t in (0 : ℝ)..(π / 2), (v z t) ^ 2 * (Spaces.Dth f z t / 2
        + (1 - q) * Real.cos (2 * t) * f z t) * (Real.sin (2 * t)) ^ (-q)) = 0 := by
    have hfun : (fun θ => (Real.sin (2 * θ)) ^ (-q)
        * (f z θ * Spaces.Dth v z θ * v z θ
          + (v z θ) ^ 2 * (Spaces.Dth f z θ / 2 + (1 - q) * Real.cos (2 * θ) * f z θ)))
        = fun θ => f z θ * Spaces.Dth v z θ * v z θ * (Real.sin (2 * θ)) ^ (-q)
          + (v z θ) ^ 2 * (Spaces.Dth f z θ / 2 + (1 - q) * Real.cos (2 * θ) * f z θ)
              * (Real.sin (2 * θ)) ^ (-q) := by
      funext θ; ring
    rw [← intervalIntegral.integral_add hA hK, ← hfun]
    exact hFTC
  rw [hIcc (fun θ => f z θ * Spaces.Dth v z θ * v z θ * (Real.sin (2 * θ)) ^ (-q)),
      hIcc (fun θ => (v z θ) ^ 2 * (Spaces.Dth f z θ / 2 + (1 - q) * Real.cos (2 * θ) * f z θ)
        * (Real.sin (2 * θ)) ^ (-q))]
  linarith

end Work.FTS.H2
