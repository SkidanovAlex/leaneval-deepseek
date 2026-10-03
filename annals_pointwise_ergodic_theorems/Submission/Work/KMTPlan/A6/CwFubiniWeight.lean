/-
# The weighted Fubini identity for the `cw`-coefficients (Area `A6`)

For the model approximation of Krause--Mirek--Tao, *Pointwise ergodic theorems for
non-conventional bilinear polynomial averages*, Ann. of Math. 195 (3) 2022, the coefficient of the
twisted bilinear multiplier `Work.KMTAreas.A7.Btwist` can be written in two equivalent ways: as a
time-average of products of inverse Fourier coefficients `cw` of the *modulated* bumps, or as a
double integral over `ℝ²` of the *unmodulated* bumps against the oscillatory integral
`∫_{1/2}^1 W(t) e(u(t)ξ₁ + v(t)ξ₂) dt`.  Here the §6 model of area `A6` uses a genuinely
`t`-dependent weight `W` (the weights `mdlW1`, `mdlW2` of the model approximation, which carry the
integration-by-parts of `Work.KMTPlan.A6.MdlBumpIntegIdent`), so the unweighted identity
`Work.A7.cw_interval_integral_fubini` (in `Submission/Work/A7/ModelApproxCore_cw_fubini.lean`,
where `W ≡ 1`) does not apply, and the weighted form proved here is needed.

The mathematical content is the same elementary Fubini theorem: `e(x) = ee x = exp(2πix)` is a
character, and both sides are the two orderings of the iterated integral of the *single* integrand

`(t, ξ₁, ξ₂) ↦ W(t) · a(ξ₁) e(u(t)ξ₁) e(-j₁ξ₁) · b(ξ₂) e(v(t)ξ₂) e(-j₂ξ₂)`

over `(1/2,1] × ℝ × ℝ`, which factorises in `(ξ₁,ξ₂)` for fixed `t`.  The left-hand side is the
`(t,(ξ₁,ξ₂))` ordering (`integral_prod_mul` for the product of the two `ξ`-integrals, `cw` being
a genuine Bochner integral because `‖a · e(u t ·)‖ = ‖a‖` is integrable), the right-hand side is
the `((ξ₁,ξ₂),t)` ordering (`integral_const_mul` for the constant `a ξ₁ b ξ₂ e(-j₁ξ₁-j₂ξ₂)`, then
`integral_integral` + `integral_integral_swap`).  The hypotheses are exactly what makes those
steps valid: `a`, `b` integrable (for the `ξ`-integrals), `W` integrable on `(1/2,1]` (for the
`t`-integral), and the measurabilities for the Fubini measurability side conditions.
-/
import Mathlib
import Submission.Work.A7.ModelApproxCore_cw_fubini

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory intervalIntegral
open scoped BigOperators

/-- **The weighted Fubini identity of the §6 model coefficient.**

For integrable bumps `a`, `b : ℝ → ℂ`, measurable phases `u`, `v : ℝ → ℝ`, and a weight
`W : ℝ → ℂ` integrable on `(1/2,1]`,

`∫_{1/2}^1 W t · 𝓕⁻(a · e(u t ·))(j₁) · 𝓕⁻(b · e(v t ·))(j₂) dt
   = ∫_{ℝ}∫_{ℝ} a(ξ₁) b(ξ₂) (∫_{1/2}^1 W t · e(u t ξ₁ + v t ξ₂) dt) e(-j₁ξ₁-j₂ξ₂) dξ₁dξ₂`,

where `𝓕⁻(m)(j) = cw m j = ∫ m(θ) e(-jθ) dθ` is the inverse Fourier coefficient at the integer
frequency `j`.  Both sides are the two orderings of the iterated integral of the single integrand
`(t,ξ₁,ξ₂) ↦ W t · (a ξ₁ e(u t ξ₁) e(-j₁ξ₁)) · (b ξ₂ e(v t ξ₂) e(-j₂ξ₂))`. -/
theorem CwFubiniWeight {a b : ℝ → ℂ} (ha : MeasureTheory.Integrable a) (hb : MeasureTheory.Integrable b)
    (ham : Measurable a) (hbm : Measurable b) {u v : ℝ → ℝ} (hu : Measurable u) (hv : Measurable v)
    {W : ℝ → ℂ} (hW : MeasureTheory.Integrable W (MeasureTheory.volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)))
    (hWm : Measurable W) (ja jb : ℤ) :
    ∫ t in (1 / 2 : ℝ)..1,
        W t * Work.KMTAreas.A7.cw (fun ξ => a ξ * Work.KMTAreas.A7.ee (u t * ξ)) ja
          * Work.KMTAreas.A7.cw (fun ξ => b ξ * Work.KMTAreas.A7.ee (v t * ξ)) jb
      = ∫ ξ₁ : ℝ, ∫ ξ₂ : ℝ,
          a ξ₁ * b ξ₂ * (∫ t in (1 / 2 : ℝ)..1, W t * Work.KMTAreas.A7.ee (u t * ξ₁ + v t * ξ₂))
            * Work.KMTAreas.A7.ee (-(ja : ℝ) * ξ₁ - (jb : ℝ) * ξ₂) := by
  classical
  set s : Set ℝ := Set.Ioc (1/2 : ℝ) 1 with hs
  set μt : Measure ℝ := volume.restrict s with hμt
  have hWi : Integrable W μt := by rw [hμt, hs]; exact hW
  have hWn : Integrable (fun t : ℝ => ‖W t‖) μt := hWi.norm
  have hG : Integrable (fun z : ℝ × ℝ => ‖a z.1‖ * ‖b z.2‖) (volume.prod volume) :=
    ha.norm.mul_prod hb.norm
  -- the modulus of the common integrand, in the `(t,(ξ₁,ξ₂))` order
  have hbound : ∀ (t ξ₁ ξ₂ : ℝ),
      ‖W t * (a ξ₁ * Work.KMTAreas.A7.ee (u t * ξ₁) * Work.KMTAreas.A7.ee (-(ja : ℝ) * ξ₁))
        * (b ξ₂ * Work.KMTAreas.A7.ee (v t * ξ₂) * Work.KMTAreas.A7.ee (-(jb : ℝ) * ξ₂))‖
      = ‖W t‖ * (‖a ξ₁‖ * ‖b ξ₂‖) := by
    intro t ξ₁ ξ₂
    simp only [norm_mul, Work.A7.ee_norm_char]
    ring
  -- the same modulus, in the `((ξ₁,ξ₂),t)` order
  have hboundR : ∀ (t ξ₁ ξ₂ : ℝ),
      ‖W t * (a ξ₁ * Work.KMTAreas.A7.ee (u t * ξ₁) * Work.KMTAreas.A7.ee (-(ja : ℝ) * ξ₁))
        * (b ξ₂ * Work.KMTAreas.A7.ee (v t * ξ₂) * Work.KMTAreas.A7.ee (-(jb : ℝ) * ξ₂))‖
      = (‖a ξ₁‖ * ‖b ξ₂‖) * ‖W t‖ := by
    intro t ξ₁ ξ₂
    rw [hbound t ξ₁ ξ₂]
    ring
  -- integrability of the common integrand, in the `(t,z)` order (used by the Fubini swap)
  have hL : Integrable (fun w : ℝ × (ℝ × ℝ) =>
      W w.1 * (a w.2.1 * Work.KMTAreas.A7.ee (u w.1 * w.2.1)
        * Work.KMTAreas.A7.ee (-(ja : ℝ) * w.2.1))
        * (b w.2.2 * Work.KMTAreas.A7.ee (v w.1 * w.2.2)
          * Work.KMTAreas.A7.ee (-(jb : ℝ) * w.2.2)))
      (μt.prod (volume.prod volume)) := by
    refine (hWn.mul_prod hG).mono' ?_ ?_
    · simp only [Work.KMTAreas.A7.ee]; fun_prop
    · filter_upwards with w
      simp only [hbound w.1 w.2.1 w.2.2, le_refl]
  -- integrability of the common integrand, in the `(z,t)` order (used to marginalise)
  have hLR : Integrable (fun w : (ℝ × ℝ) × ℝ =>
      W w.2 * (a w.1.1 * Work.KMTAreas.A7.ee (u w.2 * w.1.1)
        * Work.KMTAreas.A7.ee (-(ja : ℝ) * w.1.1))
        * (b w.1.2 * Work.KMTAreas.A7.ee (v w.2 * w.1.2)
          * Work.KMTAreas.A7.ee (-(jb : ℝ) * w.1.2)))
      ((volume.prod volume).prod μt) := by
    refine (hG.mul_prod hWn).mono' ?_ ?_
    · simp only [Work.KMTAreas.A7.ee]; fun_prop
    · filter_upwards with w
      simp only [hboundR w.2 w.1.1 w.1.2, le_refl]
  have hmarg : Integrable (fun z : ℝ × ℝ =>
      ∫ t, W t * (a z.1 * Work.KMTAreas.A7.ee (u t * z.1) * Work.KMTAreas.A7.ee (-(ja : ℝ) * z.1))
        * (b z.2 * Work.KMTAreas.A7.ee (v t * z.2) * Work.KMTAreas.A7.ee (-(jb : ℝ) * z.2)) ∂μt)
      (volume.prod volume) := hLR.integral_prod_left
  -- the pointwise identity in `(ξ₁,ξ₂)`: the `t`-integral of the weighted phase is the inner
  -- integral of the common integrand
  have hpt : ∀ ξ₁ ξ₂ : ℝ,
      a ξ₁ * b ξ₂ * (∫ t in (1/2 : ℝ)..1, W t * Work.KMTAreas.A7.ee (u t * ξ₁ + v t * ξ₂))
          * Work.KMTAreas.A7.ee (-(ja : ℝ) * ξ₁ - (jb : ℝ) * ξ₂)
        = ∫ t, W t * (a ξ₁ * Work.KMTAreas.A7.ee (u t * ξ₁) * Work.KMTAreas.A7.ee (-(ja : ℝ) * ξ₁))
            * (b ξ₂ * Work.KMTAreas.A7.ee (v t * ξ₂) * Work.KMTAreas.A7.ee (-(jb : ℝ) * ξ₂)) ∂μt := by
    intro ξ₁ ξ₂
    rw [intervalIntegral.integral_of_le (show (1/2 : ℝ) ≤ 1 by norm_num), ← hs, ← hμt]
    have hrearr : a ξ₁ * b ξ₂ * (∫ t, W t * Work.KMTAreas.A7.ee (u t * ξ₁ + v t * ξ₂) ∂μt)
        * Work.KMTAreas.A7.ee (-(ja : ℝ) * ξ₁ - (jb : ℝ) * ξ₂)
        = (a ξ₁ * b ξ₂ * Work.KMTAreas.A7.ee (-(ja : ℝ) * ξ₁ - (jb : ℝ) * ξ₂))
          * (∫ t, W t * Work.KMTAreas.A7.ee (u t * ξ₁ + v t * ξ₂) ∂μt) := by ring
    rw [hrearr, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    rw [show -(ja : ℝ) * ξ₁ - (jb : ℝ) * ξ₂
        = (-(ja : ℝ) * ξ₁) + (-(jb : ℝ) * ξ₂) by ring]
    simp only [Work.A7.ee_add_char]
    ring
  -- the left-hand side, directly as the `(t, z)` iterated integral
  have hA : (∫ t in (1/2 : ℝ)..1,
        W t * Work.KMTAreas.A7.cw (fun ξ => a ξ * Work.KMTAreas.A7.ee (u t * ξ)) ja
          * Work.KMTAreas.A7.cw (fun ξ => b ξ * Work.KMTAreas.A7.ee (v t * ξ)) jb)
      = ∫ t, ∫ z : ℝ × ℝ,
            W t * (a z.1 * Work.KMTAreas.A7.ee (u t * z.1) * Work.KMTAreas.A7.ee (-(ja : ℝ) * z.1))
              * (b z.2 * Work.KMTAreas.A7.ee (v t * z.2)
                * Work.KMTAreas.A7.ee (-(jb : ℝ) * z.2)) ∂(volume.prod volume) ∂μt := by
    rw [intervalIntegral.integral_of_le (show (1/2 : ℝ) ≤ 1 by norm_num), ← hs, ← hμt]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [Work.KMTAreas.A7.cw]
    rw [show W t * (∫ θ, a θ * Work.KMTAreas.A7.ee (u t * θ) * Work.KMTAreas.A7.ee (-(ja : ℝ) * θ))
          * (∫ θ, b θ * Work.KMTAreas.A7.ee (v t * θ) * Work.KMTAreas.A7.ee (-(jb : ℝ) * θ))
        = W t * ((∫ θ, a θ * Work.KMTAreas.A7.ee (u t * θ) * Work.KMTAreas.A7.ee (-(ja : ℝ) * θ))
          * (∫ θ, b θ * Work.KMTAreas.A7.ee (v t * θ) * Work.KMTAreas.A7.ee (-(jb : ℝ) * θ)))
        by ring]
    rw [← MeasureTheory.integral_prod_mul, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    ring
  -- the right-hand side, rearranged to the same `(t, z)` iterated integral
  have hB : (∫ ξ₁ : ℝ, ∫ ξ₂ : ℝ,
          a ξ₁ * b ξ₂ * (∫ t in (1/2 : ℝ)..1,
              W t * Work.KMTAreas.A7.ee (u t * ξ₁ + v t * ξ₂))
            * Work.KMTAreas.A7.ee (-(ja : ℝ) * ξ₁ - (jb : ℝ) * ξ₂))
      = ∫ t, ∫ z : ℝ × ℝ,
            W t * (a z.1 * Work.KMTAreas.A7.ee (u t * z.1) * Work.KMTAreas.A7.ee (-(ja : ℝ) * z.1))
              * (b z.2 * Work.KMTAreas.A7.ee (v t * z.2)
                * Work.KMTAreas.A7.ee (-(jb : ℝ) * z.2)) ∂(volume.prod volume) ∂μt := by
    have hstep1 : (∫ ξ₁ : ℝ, ∫ ξ₂ : ℝ,
          a ξ₁ * b ξ₂ * (∫ t in (1/2 : ℝ)..1,
              W t * Work.KMTAreas.A7.ee (u t * ξ₁ + v t * ξ₂))
            * Work.KMTAreas.A7.ee (-(ja : ℝ) * ξ₁ - (jb : ℝ) * ξ₂))
        = ∫ ξ₁ : ℝ, ∫ ξ₂ : ℝ,
            ∫ t, W t * (a ξ₁ * Work.KMTAreas.A7.ee (u t * ξ₁)
                * Work.KMTAreas.A7.ee (-(ja : ℝ) * ξ₁))
              * (b ξ₂ * Work.KMTAreas.A7.ee (v t * ξ₂)
                * Work.KMTAreas.A7.ee (-(jb : ℝ) * ξ₂)) ∂μt := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ξ₁ => ?_)
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ξ₂ => ?_)
      exact hpt ξ₁ ξ₂
    rw [hstep1, MeasureTheory.integral_integral hmarg]
    exact (MeasureTheory.integral_integral_swap hL).symm
  rw [hA, hB]

end

end Work.KMTPlan.A6
