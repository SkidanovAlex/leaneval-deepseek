/-
# Area 4 / HB §12 — the Laplace transform of Heath-Brown's §7 test function

Companion to `TestFun.lean`.  For `θ ∈ (π/2, π)` and `λ̂ > 0` the transform
`FT θ λ̂ z = ∫₀^{2γ} e^{-zt} f(t) dt` (`γ = gammaT θ λ̂`, `ζ = zetaT θ λ̂`) of HB's §7 test
function is elementary: on the support `[0,2γ]` the closed form of `f` is
`λ̂²(1+tan²θ)² · h(t)` with
`h(t) = (2γ-t)(cos(ζt)/2 + cos²θ) + sin(2θ-ζt)/(2ζ) - sin 2θ/ζ + 2 cos θ sin(ζt-θ)/ζ`,
and integrating the five elementary pieces (`1`, `t`, `cos ζt`, `t cos ζt`, `sin ζt` against
`e^{-zt}`) gives the stated closed form.  This file contains the (mechanical) assembly; the three
non-trivial elementary integrals are separate modules
(`integral_exp_neg_cos`, `integral_exp_neg_sin`, `integral_mul_exp_neg_cos`).
-/
import Mathlib
import Submission.Work.LinnikAreas.Density4.TestFun
import Submission.Work.LinnikAreas.Density4.integral_exp_neg_cos
import Submission.Work.LinnikAreas.Density4.integral_exp_neg_sin
import Submission.Work.LinnikAreas.Density4.integral_mul_exp_neg_cos

open scoped BigOperators
open MeasureTheory intervalIntegral

noncomputable section

namespace Work.LinnikAreas.Density4

/-! ## Elementary integrals -/

/-- `∫₀^T e^{-zt} dt = (1 - e^{-zT})/z` for `z ≠ 0`. -/
theorem integral_exp_neg_zero_T (z T : ℝ) (hz : z ≠ 0) :
    ∫ t in (0:ℝ)..T, Real.exp (-(z*t)) = (1 - Real.exp (-(z*T)))/z := by
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) T,
      HasDerivAt (fun t : ℝ => -Real.exp (-(z*t))) (z * Real.exp (-(z*x))) x := by
    intro x hx
    have h1 : HasDerivAt (fun t : ℝ => -(z*t)) (-z) x := by
      have := (hasDerivAt_id x).const_mul (-z)
      simpa [neg_mul] using this
    have h3 : HasDerivAt (fun t : ℝ => -Real.exp (-(z*t))) (-(Real.exp (-(z*x)) * (-z))) x :=
      h1.exp.neg
    have hval : -(Real.exp (-(z*x)) * (-z)) = z * Real.exp (-(z*x)) := by ring
    rwa [hval] at h3
  have hint : IntervalIntegrable (fun x : ℝ => z * Real.exp (-(z*x))) volume (0:ℝ) T :=
    (by fun_prop : Continuous fun x : ℝ => z * Real.exp (-(z*x))).intervalIntegrable _ _
  have key : z * (∫ t in (0:ℝ)..T, Real.exp (-(z*t))) = 1 - Real.exp (-(z*T)) := by
    rw [← intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    simp only [mul_zero, neg_zero, Real.exp_zero, sub_neg_eq_add]
    ring
  rw [eq_div_iff hz, mul_comm (∫ t in (0:ℝ)..T, Real.exp (-(z*t))) z]
  exact key

/-- `∫₀^T t e^{-zt} dt = (1 - e^{-zT}(1+Tz))/z²` for `z ≠ 0`. -/
theorem integral_mul_exp_neg_zero_T (z T : ℝ) (hz : z ≠ 0) :
    ∫ t in (0:ℝ)..T, t * Real.exp (-(z*t)) = (1 - Real.exp (-(z*T))*(1 + T*z))/z^2 := by
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) T,
      HasDerivAt (fun t : ℝ => -(z*t + 1) * Real.exp (-(z*t)))
        (z^2 * (x * Real.exp (-(z*x)))) x := by
    intro x hx
    have h1 : HasDerivAt (fun t : ℝ => z*t + 1) z x := by
      simpa using ((hasDerivAt_id x).const_mul z).add_const 1
    have h2 : HasDerivAt (fun t : ℝ => Real.exp (-(z*t))) (Real.exp (-(z*x)) * (-z)) x := by
      have h3 : HasDerivAt (fun t : ℝ => -(z*t)) (-z) x := by
        have := (hasDerivAt_id x).const_mul (-z)
        simpa [neg_mul] using this
      exact h3.exp
    have h4 := h1.neg.mul h2
    exact h4.congr_deriv (by simp only [Pi.neg_apply]; ring)
  have hint : IntervalIntegrable (fun x : ℝ => z^2 * (x * Real.exp (-(z*x)))) volume (0:ℝ) T :=
    (by fun_prop : Continuous fun x : ℝ => z^2 * (x * Real.exp (-(z*x)))).intervalIntegrable _ _
  have key : z^2 * (∫ t in (0:ℝ)..T, t * Real.exp (-(z*t)))
      = 1 - Real.exp (-(z*T))*(1 + T*z) := by
    rw [← intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    simp only [mul_zero, add_zero, neg_zero, Real.exp_zero, mul_one]
    ring
  rw [eq_div_iff (pow_ne_zero 2 hz), mul_comm (∫ t in (0:ℝ)..T, t * Real.exp (-(z*t))) (z^2)]
  exact key

/-- Linearity of the interval integral for a five-term linear combination of continuous
integrands. -/
theorem integral_lin5 (a b : ℝ) (c0 c1 c2 c3 c4 : ℝ) {f0 f1 f2 f3 f4 : ℝ → ℝ}
    (h0 : IntervalIntegrable f0 volume a b) (h1 : IntervalIntegrable f1 volume a b)
    (h2 : IntervalIntegrable f2 volume a b) (h3 : IntervalIntegrable f3 volume a b)
    (h4 : IntervalIntegrable f4 volume a b) :
    ∫ x in a..b, (c0 * f0 x + c1 * f1 x + c2 * f2 x + c3 * f3 x + c4 * f4 x)
      = c0 * (∫ x in a..b, f0 x) + c1 * (∫ x in a..b, f1 x) + c2 * (∫ x in a..b, f2 x)
        + c3 * (∫ x in a..b, f3 x) + c4 * (∫ x in a..b, f4 x) := by
  have h01 : IntervalIntegrable (fun x => c0 * f0 x + c1 * f1 x) volume a b :=
    (h0.const_mul c0).add (h1.const_mul c1)
  have h012 : IntervalIntegrable (fun x => c0 * f0 x + c1 * f1 x + c2 * f2 x) volume a b :=
    h01.add (h2.const_mul c2)
  have h0123 : IntervalIntegrable (fun x => c0 * f0 x + c1 * f1 x + c2 * f2 x + c3 * f3 x)
      volume a b := h012.add (h3.const_mul c3)
  rw [intervalIntegral.integral_add h0123 (h4.const_mul c4)]
  rw [intervalIntegral.integral_add h012 (h3.const_mul c3)]
  rw [intervalIntegral.integral_add h01 (h2.const_mul c2)]
  rw [intervalIntegral.integral_add (h0.const_mul c0) (h1.const_mul c1)]
  simp only [intervalIntegral.integral_const_mul]

/-- Pointwise expansion of the `fT` integrand into the five elementary integrals of HB's
computation. -/
theorem testfun_integrand_expand (θ γ ζ z t : ℝ) :
    Real.exp (-(z*t)) * ((2*γ - t) * (Real.cos (ζ*t)/2 + Real.cos θ^2)
        + Real.sin (2*θ - ζ*t)/(2*ζ) - Real.sin (2*θ)/ζ
        + 2*Real.cos θ*Real.sin (ζ*t - θ)/ζ)
  = (2*γ*Real.cos θ^2 - Real.sin (2*θ)/ζ) * Real.exp (-(z*t))
    + (γ - Real.sin (2*θ)/(2*ζ)) * (Real.exp (-(z*t)) * Real.cos (ζ*t))
    - Real.cos θ^2 * (t * Real.exp (-(z*t)))
    - (1/2) * (t * Real.exp (-(z*t)) * Real.cos (ζ*t))
    + (1/2 + Real.cos θ^2)/ζ * (Real.exp (-(z*t)) * Real.sin (ζ*t)) := by
  rw [Real.sin_sub, Real.sin_sub, Real.sin_two_mul, Real.cos_two_mul]
  ring

/-! ## The Laplace transform in closed form -/

/-- **HB §7, Laplace transform of the test function.**  The closed form of
`FT θ λ̂ z = ∫₀^{2γ} e^{-zt} f(t) dt`, conditional on the three elementary integrals
`∫₀^{2γ} e^{-zt}cos(ζt)`, `∫₀^{2γ} e^{-zt}sin(ζt)` and `∫₀^{2γ} t e^{-zt}cos(ζt)`
(proved in the separate modules `integral_exp_neg_cos`, `integral_exp_neg_sin`,
`integral_mul_exp_neg_cos`). -/
theorem testfun_laplace_of_integrals (θ lam z : ℝ) (hθ1 : Real.pi / 2 < θ) (hθ2 : θ < Real.pi)
    (hlam : 0 < lam) (hz : z ≠ 0)
    (hIc : ∫ t in (0:ℝ)..(2 * gammaT θ lam), Real.exp (-(z*t)) * Real.cos (zetaT θ lam * t)
        = ((1 - Real.exp (-(z*(2 * gammaT θ lam))) * Real.cos ((2 * gammaT θ lam) * zetaT θ lam))
              * z
            + Real.exp (-(z*(2 * gammaT θ lam))) * Real.sin ((2 * gammaT θ lam) * zetaT θ lam)
              * zetaT θ lam)
          / (z^2 + zetaT θ lam^2))
    (hIs : ∫ t in (0:ℝ)..(2 * gammaT θ lam), Real.exp (-(z*t)) * Real.sin (zetaT θ lam * t)
        = ((1 - Real.exp (-(z*(2 * gammaT θ lam))) * Real.cos ((2 * gammaT θ lam) * zetaT θ lam))
              * zetaT θ lam
            - Real.exp (-(z*(2 * gammaT θ lam))) * Real.sin ((2 * gammaT θ lam) * zetaT θ lam) * z)
          / (z^2 + zetaT θ lam^2))
    (hItc : ∫ t in (0:ℝ)..(2 * gammaT θ lam), t * Real.exp (-(z*t)) * Real.cos (zetaT θ lam * t)
        = Real.exp (-(z*(2 * gammaT θ lam))) *
            ((-(z*(2 * gammaT θ lam)) / (z^2 + zetaT θ lam^2)
                + (zetaT θ lam^2 - z^2) / (z^2 + zetaT θ lam^2)^2)
                * Real.cos (zetaT θ lam * (2 * gammaT θ lam))
              + (zetaT θ lam * (2 * gammaT θ lam) / (z^2 + zetaT θ lam^2)
                + 2 * zetaT θ lam * z / (z^2 + zetaT θ lam^2)^2)
                * Real.sin (zetaT θ lam * (2 * gammaT θ lam)))
          - (zetaT θ lam^2 - z^2) / (z^2 + zetaT θ lam^2)^2) :
    Work.LinnikAreas.Density4.FT θ lam z =
      lam ^ 2 * (1 + Real.tan θ ^ 2) ^ 2 *
      ( (2 * Work.LinnikAreas.Density4.gammaT θ lam * Real.cos θ ^ 2
            - Real.sin (2 * θ) / Work.LinnikAreas.Density4.zetaT θ lam)
          * ((1 - Real.exp (-(2 * Work.LinnikAreas.Density4.gammaT θ lam * z))) / z)
        - Real.cos θ ^ 2
          * ((1 - Real.exp (-(2 * Work.LinnikAreas.Density4.gammaT θ lam * z))
              * (1 + 2 * Work.LinnikAreas.Density4.gammaT θ lam * z)) / z ^ 2)
        + (Work.LinnikAreas.Density4.gammaT θ lam
            - Real.sin (2 * θ) / (2 * Work.LinnikAreas.Density4.zetaT θ lam))
          * (((1 - Real.exp (-(2 * Work.LinnikAreas.Density4.gammaT θ lam * z))
                * Real.cos (2 * θ)) * z
              + Real.exp (-(2 * Work.LinnikAreas.Density4.gammaT θ lam * z))
                * Real.sin (2 * θ) * Work.LinnikAreas.Density4.zetaT θ lam)
              / (z ^ 2 + Work.LinnikAreas.Density4.zetaT θ lam ^ 2))
        - (1/2)
          * (((1 - Real.exp (-(2 * Work.LinnikAreas.Density4.gammaT θ lam * z))
                * (Real.cos (2 * θ) * (1 + 2 * Work.LinnikAreas.Density4.gammaT θ lam * z)
                  + Real.sin (2 * θ) * (2 * θ)))
              * (z ^ 2 - Work.LinnikAreas.Density4.zetaT θ lam ^ 2)
              - (Real.exp (-(2 * Work.LinnikAreas.Density4.gammaT θ lam * z))
                  * (Real.cos (2 * θ) * (2 * θ)
                    - Real.sin (2 * θ) * (1 + 2 * Work.LinnikAreas.Density4.gammaT θ lam * z)))
                * (2 * Work.LinnikAreas.Density4.zetaT θ lam * z))
              / (z ^ 2 + Work.LinnikAreas.Density4.zetaT θ lam ^ 2) ^ 2)
        + (1/2 + Real.cos θ ^ 2) / Work.LinnikAreas.Density4.zetaT θ lam
          * (((1 - Real.exp (-(2 * Work.LinnikAreas.Density4.gammaT θ lam * z))
                * Real.cos (2 * θ)) * Work.LinnikAreas.Density4.zetaT θ lam
              - Real.exp (-(2 * Work.LinnikAreas.Density4.gammaT θ lam * z))
                * Real.sin (2 * θ) * z)
              / (z ^ 2 + Work.LinnikAreas.Density4.zetaT θ lam ^ 2)) ) := by
  -- elementary facts about the parameters
  have hζpos : 0 < zetaT θ lam := zetaT_pos hθ1 hθ2 hlam
  have hζne : zetaT θ lam ≠ 0 := ne_of_gt hζpos
  have hWne : z ^ 2 + zetaT θ lam ^ 2 ≠ 0 := by
    have h : 0 < z ^ 2 + zetaT θ lam ^ 2 := by
      have := pow_pos hζpos 2
      nlinarith [sq_nonneg z]
    exact ne_of_gt h
  have hγpos : 0 < gammaT θ lam := gammaT_pos hθ1 hθ2 hlam
  have h2g : (0:ℝ) < 2 * gammaT θ lam := by linarith
  have hγζ : gammaT θ lam * zetaT θ lam = θ := by
    rw [gammaT]
    field_simp
  have hE : Real.exp (-(z * (2 * gammaT θ lam))) = Real.exp (-(2 * gammaT θ lam * z)) := by
    congr 1; ring
  have h2γζ : (2 * gammaT θ lam) * zetaT θ lam = 2 * θ := by
    rw [show (2 * gammaT θ lam) * zetaT θ lam = 2 * (gammaT θ lam * zetaT θ lam) by ring, hγζ]
  have h2γζ' : zetaT θ lam * (2 * gammaT θ lam) = 2 * θ := by
    rw [show zetaT θ lam * (2 * gammaT θ lam) = 2 * (gammaT θ lam * zetaT θ lam) by ring, hγζ]
  have hc2 : Real.cos ((2 * gammaT θ lam) * zetaT θ lam) = Real.cos (2 * θ) := by rw [h2γζ]
  have hs2 : Real.sin ((2 * gammaT θ lam) * zetaT θ lam) = Real.sin (2 * θ) := by rw [h2γζ]
  have hc2' : Real.cos (zetaT θ lam * (2 * gammaT θ lam)) = Real.cos (2 * θ) := by rw [h2γζ']
  have hs2' : Real.sin (zetaT θ lam * (2 * gammaT θ lam)) = Real.sin (2 * θ) := by rw [h2γζ']
  -- the five elementary integrals in the statement's own normal form
  have hI1 : ∫ t in (0:ℝ)..(2 * gammaT θ lam), Real.exp (-(z*t))
      = (1 - Real.exp (-(2 * gammaT θ lam * z)))/z := by
    rw [integral_exp_neg_zero_T z (2 * gammaT θ lam) hz, hE]
  have hIt : ∫ t in (0:ℝ)..(2 * gammaT θ lam), t * Real.exp (-(z*t))
      = (1 - Real.exp (-(2 * gammaT θ lam * z)) * (1 + 2 * gammaT θ lam * z))/z^2 := by
    rw [integral_mul_exp_neg_zero_T z (2 * gammaT θ lam) hz, hE]
  have hIc' : ∫ t in (0:ℝ)..(2 * gammaT θ lam), Real.exp (-(z*t)) * Real.cos (zetaT θ lam * t)
      = ((1 - Real.exp (-(2 * gammaT θ lam * z)) * Real.cos (2 * θ)) * z
          + Real.exp (-(2 * gammaT θ lam * z)) * Real.sin (2 * θ) * zetaT θ lam)
        / (z^2 + zetaT θ lam^2) := by
    rw [hIc, hE, hc2, hs2]
  have hIs' : ∫ t in (0:ℝ)..(2 * gammaT θ lam), Real.exp (-(z*t)) * Real.sin (zetaT θ lam * t)
      = ((1 - Real.exp (-(2 * gammaT θ lam * z)) * Real.cos (2 * θ)) * zetaT θ lam
          - Real.exp (-(2 * gammaT θ lam * z)) * Real.sin (2 * θ) * z)
        / (z^2 + zetaT θ lam^2) := by
    rw [hIs, hE, hc2, hs2]
  have hItc' : ∫ t in (0:ℝ)..(2 * gammaT θ lam), t * Real.exp (-(z*t)) * Real.cos (zetaT θ lam * t)
      = ((1 - Real.exp (-(2 * gammaT θ lam * z))
            * (Real.cos (2 * θ) * (1 + 2 * gammaT θ lam * z) + Real.sin (2 * θ) * (2 * θ)))
          * (z^2 - zetaT θ lam^2)
          - (Real.exp (-(2 * gammaT θ lam * z))
              * (Real.cos (2 * θ) * (2 * θ) - Real.sin (2 * θ) * (1 + 2 * gammaT θ lam * z)))
            * (2 * zetaT θ lam * z))
        / (z^2 + zetaT θ lam^2)^2 := by
    rw [hItc, hE, hc2', hs2']
    rw [show (2:ℝ) * θ = 2 * gammaT θ lam * zetaT θ lam by
      rw [show 2 * gammaT θ lam * zetaT θ lam = 2 * (gammaT θ lam * zetaT θ lam) by ring, hγζ]]
    field_simp
    ring
  -- the integrand on the support, with the constant prefactor pulled out
  have step_a : ∫ t in (0:ℝ)..(2 * gammaT θ lam), Real.exp (-(z*t)) * fT θ lam t
      = ∫ t in (0:ℝ)..(2 * gammaT θ lam),
          (lam^2 * (1 + Real.tan θ^2)^2) *
            (Real.exp (-(z*t)) * ((2*gammaT θ lam - t) * (Real.cos (zetaT θ lam*t)/2 + Real.cos θ^2)
              + Real.sin (2*θ - zetaT θ lam*t)/(2*zetaT θ lam) - Real.sin (2*θ)/zetaT θ lam
              + 2*Real.cos θ*Real.sin (zetaT θ lam*t - θ)/zetaT θ lam)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : 0 ≤ t ∧ t ≤ 2 * gammaT θ lam := by
      rw [Set.uIcc_of_le h2g.le] at ht
      exact ht
    dsimp only
    rw [fT, if_pos ht']
    ring
  have step_b : ∫ t in (0:ℝ)..(2 * gammaT θ lam),
          (lam^2 * (1 + Real.tan θ^2)^2) *
            (Real.exp (-(z*t)) * ((2*gammaT θ lam - t) * (Real.cos (zetaT θ lam*t)/2 + Real.cos θ^2)
              + Real.sin (2*θ - zetaT θ lam*t)/(2*zetaT θ lam) - Real.sin (2*θ)/zetaT θ lam
              + 2*Real.cos θ*Real.sin (zetaT θ lam*t - θ)/zetaT θ lam))
      = (lam^2 * (1 + Real.tan θ^2)^2) *
          (∫ t in (0:ℝ)..(2 * gammaT θ lam),
            Real.exp (-(z*t)) * ((2*gammaT θ lam - t) * (Real.cos (zetaT θ lam*t)/2 + Real.cos θ^2)
              + Real.sin (2*θ - zetaT θ lam*t)/(2*zetaT θ lam) - Real.sin (2*θ)/zetaT θ lam
              + 2*Real.cos θ*Real.sin (zetaT θ lam*t - θ)/zetaT θ lam)) :=
    intervalIntegral.integral_const_mul _ _
  -- pointwise expansion into the five elementary integrals
  have hpt : ∀ t : ℝ, Real.exp (-(z*t)) *
        ((2*gammaT θ lam - t) * (Real.cos (zetaT θ lam*t)/2 + Real.cos θ^2)
          + Real.sin (2*θ - zetaT θ lam*t)/(2*zetaT θ lam) - Real.sin (2*θ)/zetaT θ lam
          + 2*Real.cos θ*Real.sin (zetaT θ lam*t - θ)/zetaT θ lam)
      = (2 * gammaT θ lam * Real.cos θ^2 - Real.sin (2*θ)/zetaT θ lam) * (Real.exp (-(z*t)))
        + (gammaT θ lam - Real.sin (2*θ)/(2*zetaT θ lam))
            * (Real.exp (-(z*t)) * Real.cos (zetaT θ lam*t))
        + (-(Real.cos θ^2)) * (t * Real.exp (-(z*t)))
        + (-(1/2)) * (t * Real.exp (-(z*t)) * Real.cos (zetaT θ lam*t))
        + ((1/2 + Real.cos θ^2)/zetaT θ lam) * (Real.exp (-(z*t)) * Real.sin (zetaT θ lam*t)) := by
    intro t
    rw [testfun_integrand_expand θ (gammaT θ lam) (zetaT θ lam) z t]
    ring
  have step_c : ∫ t in (0:ℝ)..(2 * gammaT θ lam), Real.exp (-(z*t)) *
        ((2*gammaT θ lam - t) * (Real.cos (zetaT θ lam*t)/2 + Real.cos θ^2)
          + Real.sin (2*θ - zetaT θ lam*t)/(2*zetaT θ lam) - Real.sin (2*θ)/zetaT θ lam
          + 2*Real.cos θ*Real.sin (zetaT θ lam*t - θ)/zetaT θ lam)
      = (2 * gammaT θ lam * Real.cos θ^2 - Real.sin (2*θ)/zetaT θ lam)
          * (∫ t in (0:ℝ)..(2 * gammaT θ lam), Real.exp (-(z*t)))
        + (gammaT θ lam - Real.sin (2*θ)/(2*zetaT θ lam))
          * (∫ t in (0:ℝ)..(2 * gammaT θ lam), Real.exp (-(z*t)) * Real.cos (zetaT θ lam*t))
        + (-(Real.cos θ^2))
          * (∫ t in (0:ℝ)..(2 * gammaT θ lam), t * Real.exp (-(z*t)))
        + (-(1/2))
          * (∫ t in (0:ℝ)..(2 * gammaT θ lam), t * Real.exp (-(z*t)) * Real.cos (zetaT θ lam*t))
        + ((1/2 + Real.cos θ^2)/zetaT θ lam)
          * (∫ t in (0:ℝ)..(2 * gammaT θ lam), Real.exp (-(z*t)) * Real.sin (zetaT θ lam*t)) := by
    rw [intervalIntegral.integral_congr (fun t _ => hpt t)]
    rw [integral_lin5 (a := (0:ℝ)) (b := 2 * gammaT θ lam)
        (c0 := 2 * gammaT θ lam * Real.cos θ^2 - Real.sin (2*θ)/zetaT θ lam)
        (c1 := gammaT θ lam - Real.sin (2*θ)/(2*zetaT θ lam))
        (c2 := -(Real.cos θ^2)) (c3 := -(1/2)) (c4 := (1/2 + Real.cos θ^2)/zetaT θ lam)
        (f0 := fun t => Real.exp (-(z*t)))
        (f1 := fun t => Real.exp (-(z*t)) * Real.cos (zetaT θ lam*t))
        (f2 := fun t => t * Real.exp (-(z*t)))
        (f3 := fun t => t * Real.exp (-(z*t)) * Real.cos (zetaT θ lam*t))
        (f4 := fun t => Real.exp (-(z*t)) * Real.sin (zetaT θ lam*t))
        ((by fun_prop : Continuous fun t : ℝ => Real.exp (-(z*t))).intervalIntegrable _ _)
        ((by fun_prop : Continuous fun t : ℝ => Real.exp (-(z*t)) * Real.cos (zetaT θ lam*t)).intervalIntegrable _ _)
        ((by fun_prop : Continuous fun t : ℝ => t * Real.exp (-(z*t))).intervalIntegrable _ _)
        ((by fun_prop : Continuous fun t : ℝ => t * Real.exp (-(z*t)) * Real.cos (zetaT θ lam*t)).intervalIntegrable _ _)
        ((by fun_prop : Continuous fun t : ℝ => Real.exp (-(z*t)) * Real.sin (zetaT θ lam*t)).intervalIntegrable _ _)]
  rw [FT, step_a, step_b, step_c, hI1, hIt, hIc', hIs', hItc']
  ring

/-- **HB §7**: the Laplace transform `F(z) = ∫₀^{2γ} e^{-zt} f(t) dt` of the §7 test function
`f = g ⊛ g` in closed form. -/
theorem testfun_laplace (θ lam z : ℝ) (hθ1 : Real.pi / 2 < θ) (hθ2 : θ < Real.pi)
    (hlam : 0 < lam) (hz : z ≠ 0) :
    Work.LinnikAreas.Density4.FT θ lam z =
      lam ^ 2 * (1 + Real.tan θ ^ 2) ^ 2 *
      ( (2 * Work.LinnikAreas.Density4.gammaT θ lam * Real.cos θ ^ 2
            - Real.sin (2 * θ) / Work.LinnikAreas.Density4.zetaT θ lam)
          * ((1 - Real.exp (-(2 * Work.LinnikAreas.Density4.gammaT θ lam * z))) / z)
        - Real.cos θ ^ 2
          * ((1 - Real.exp (-(2 * Work.LinnikAreas.Density4.gammaT θ lam * z))
              * (1 + 2 * Work.LinnikAreas.Density4.gammaT θ lam * z)) / z ^ 2)
        + (Work.LinnikAreas.Density4.gammaT θ lam
            - Real.sin (2 * θ) / (2 * Work.LinnikAreas.Density4.zetaT θ lam))
          * (((1 - Real.exp (-(2 * Work.LinnikAreas.Density4.gammaT θ lam * z))
                * Real.cos (2 * θ)) * z
              + Real.exp (-(2 * Work.LinnikAreas.Density4.gammaT θ lam * z))
                * Real.sin (2 * θ) * Work.LinnikAreas.Density4.zetaT θ lam)
              / (z ^ 2 + Work.LinnikAreas.Density4.zetaT θ lam ^ 2))
        - (1/2)
          * (((1 - Real.exp (-(2 * Work.LinnikAreas.Density4.gammaT θ lam * z))
                * (Real.cos (2 * θ) * (1 + 2 * Work.LinnikAreas.Density4.gammaT θ lam * z)
                  + Real.sin (2 * θ) * (2 * θ)))
              * (z ^ 2 - Work.LinnikAreas.Density4.zetaT θ lam ^ 2)
              - (Real.exp (-(2 * Work.LinnikAreas.Density4.gammaT θ lam * z))
                  * (Real.cos (2 * θ) * (2 * θ)
                    - Real.sin (2 * θ) * (1 + 2 * Work.LinnikAreas.Density4.gammaT θ lam * z)))
                * (2 * Work.LinnikAreas.Density4.zetaT θ lam * z))
              / (z ^ 2 + Work.LinnikAreas.Density4.zetaT θ lam ^ 2) ^ 2)
        + (1/2 + Real.cos θ ^ 2) / Work.LinnikAreas.Density4.zetaT θ lam
          * (((1 - Real.exp (-(2 * Work.LinnikAreas.Density4.gammaT θ lam * z))
                * Real.cos (2 * θ)) * Work.LinnikAreas.Density4.zetaT θ lam
              - Real.exp (-(2 * Work.LinnikAreas.Density4.gammaT θ lam * z))
                * Real.sin (2 * θ) * z)
              / (z ^ 2 + Work.LinnikAreas.Density4.zetaT θ lam ^ 2)) ) := by
  have hW : z ^ 2 + zetaT θ lam ^ 2 ≠ 0 := by
    have h := zetaT_pos hθ1 hθ2 hlam
    exact ne_of_gt (by positivity)
  refine testfun_laplace_of_integrals θ lam z hθ1 hθ2 hlam hz ?_ ?_ ?_
  · exact integral_exp_neg_cos z (zetaT θ lam) (2 * gammaT θ lam) hW
  · exact integral_exp_neg_sin z (zetaT θ lam) (2 * gammaT θ lam) hW
  · exact integral_mul_exp_neg_cos z (zetaT θ lam) (2 * gammaT θ lam) hW

end Work.LinnikAreas.Density4
