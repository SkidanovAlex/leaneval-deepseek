/-
# The Fubini identity for the two `cw`-coefficients of the §6 model approximation (Area `A7`)

For the model approximation of Krause--Mirek--Tao, *Pointwise ergodic theorems for
non-conventional bilinear polynomial averages*, Ann. of Math. 195 (3) 2022, one needs the
identity

`∫_{1/2}^1 𝓕⁻(φ_{N,t})(j₁) · 𝓕⁻(φ̃_{N,t})(j₂) dt
   = ∫∫_{ℝ²} φ_N(ξ₁) φ̃_N(ξ₂) m̃_{N,ℝ}(ξ₁,ξ₂) e(-j₁ξ₁-j₂ξ₂) dξ₁dξ₂`

expressing the coefficient of the twisted bilinear multiplier (`Work.KMTAreas.A7.Btwist`) in the
two equivalent ways: as the time-average of products of the inverse Fourier coefficients
`cw` of the *modulated* bumps `φ_{N,t} = φ_N · e(Nt·)` and `φ̃_{N,t} = φ̃_N · e(P(Nt)·)`, and as the
double integral of the *unmodulated* bumps against the oscillatory integral
`m̃_{N,ℝ} = ∫_{1/2}^1 e(ξ₁Nt + ξ₂P(Nt)) dt`.  It is the "`bn-ident`/Fubini" step of the
decomposition of the model operator.

The mathematical content is the elementary Fubini theorem — `e(x) = ee x = exp(2πix)` is a
character, so the two sides are the two orderings of the iterated integral of the *same*
integrand

`(t, ξ₁, ξ₂) ↦ φ_N(ξ₁) e(Ntξ₁) e(-j₁ξ₁) · φ̃_N(ξ₂) e(P(Nt)ξ₂) e(-j₂ξ₂)`,

which factorises in `(ξ₁, ξ₂)` for fixed `t`.  What has to be supplied formally is only the
integrability of `φ_N`, `φ̃_N` (compact support and boundedness of the KMT cutoff `η`), which is
what makes the three Fubini/Tonelli rearrangements legitimate; it is isolated in
`Work.A7.varphiN_integrable_measurable` and `Work.A7.varphitildeN_integrable_measurable`.

The main lemma is stated in the general form `cw_interval_integral_fubini`, for an arbitrary pair
of integrable bumps `a`, `b` and arbitrary measurable phases `u`, `v`; the target statement is
the specialisation `a = φ_N`, `b = φ̃_N`, `u t = N t`, `v t = P(Nt)`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.ModelApproxDefs
import Submission.Work.A7.varphiN_integrable_measurable
import Submission.Work.A7.varphitildeN_integrable_measurable

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

namespace Work.A7

noncomputable section

open MeasureTheory intervalIntegral
open scoped BigOperators
open Work.KMTAreas.A7

/-! ## The character `e(x) = ee x = exp(2πix)` -/

/-- `ee` is a character: `ee (x + y) = ee x * ee y`. -/
lemma ee_add_char (x y : ℝ) : ee (x + y) = ee x * ee y := by
  rw [ee, ee, ee, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `ee` takes values of modulus one. -/
lemma ee_norm_char (x : ℝ) : ‖ee x‖ = 1 := by
  have h : ee x = Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) := by
    simp only [ee]
    congr 1
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-! ## The general Fubini identity -/

/-- **Fubini for the product of two `cw`-coefficients of modulated bumps.**

For integrable bumps `a`, `b : ℝ → ℂ` and measurable phases `u`, `v : ℝ → ℝ`,

`∫_{1/2}^1 𝓕⁻(a · e(u t ·))(j₁) · 𝓕⁻(b · e(v t ·))(j₂) dt
   = ∫_{ℝ}∫_{ℝ} a(ξ₁) b(ξ₂) (∫_{1/2}^1 e(u t ξ₁ + v t ξ₂) dt) e(-j₁ξ₁-j₂ξ₂) dξ₁dξ₂`,

where `𝓕⁻(m)(j) = cw m j = ∫ m(θ) e(-jθ) dθ` is the inverse Fourier coefficient at the integer
frequency `j`.

Both sides are the integral of the single integrand
`(t,ξ₁,ξ₂) ↦ (a ξ₁ e(u t ξ₁) e(-j₁ξ₁)) · (b ξ₂ e(v t ξ₂) e(-j₂ξ₂))` over
`(1/2,1] × ℝ × ℝ`: the left-hand side by Fubini for the *product* of the two `ξ`-integrals
(`integral_prod_mul`), the right-hand side by pulling the constant
`a ξ₁ b ξ₂ e(-j₁ξ₁-j₂ξ₂)` out of the `t`-integral (`integral_const_mul`), using the character
property to write `e(u t ξ₁) e(v t ξ₂) = e(u t ξ₁ + v t ξ₂)`, and then Fubini
(`integral_integral` + `integral_integral_swap`).  The integrability hypotheses are exactly
what makes those steps valid (see `ee_add_char`, `ee_norm_char`). -/
theorem cw_interval_integral_fubini {a b : ℝ → ℂ} (ha : Integrable a) (hb : Integrable b)
    (ham : Measurable a) (hbm : Measurable b) {u v : ℝ → ℝ} (hu : Measurable u)
    (hv : Measurable v) (ja jb : ℤ) :
    ∫ t in (1/2 : ℝ)..1, cw (fun ξ => a ξ * ee (u t * ξ)) ja * cw (fun ξ => b ξ * ee (v t * ξ)) jb
      = ∫ ξ₁ : ℝ, ∫ ξ₂ : ℝ,
          a ξ₁ * b ξ₂ * (∫ t in (1/2 : ℝ)..1, ee (u t * ξ₁ + v t * ξ₂))
            * ee (-(ja : ℝ) * ξ₁ - (jb : ℝ) * ξ₂) := by
  classical
  set s : Set ℝ := Set.Ioc (1/2 : ℝ) 1 with hs
  set μt : Measure ℝ := volume.restrict s with hμt
  have hfin : IsFiniteMeasure μt := ⟨by
    rw [hμt, MeasureTheory.Measure.restrict_apply_univ, hs, Real.volume_Ioc]
    norm_num⟩
  have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) μt :=
    (MeasureTheory.integrable_const_iff).mpr (Or.inr hfin)
  have hG : Integrable (fun z : ℝ × ℝ => ‖a z.1‖ * ‖b z.2‖) (volume.prod volume) :=
    ha.norm.mul_prod hb.norm
  -- integrability of the common integrand, in the `(t, z)` order (used by the Fubini swap)
  have hL : Integrable (fun w : ℝ × (ℝ × ℝ) =>
      (a w.2.1 * ee (u w.1 * w.2.1) * ee (-(ja : ℝ) * w.2.1))
        * (b w.2.2 * ee (v w.1 * w.2.2) * ee (-(jb : ℝ) * w.2.2)))
      (μt.prod (volume.prod volume)) := by
    refine (h1.mul_prod hG).mono' ?_ ?_
    · simp only [ee]; fun_prop
    · filter_upwards with w
      simp only [norm_mul, ee_norm_char, mul_one, one_mul, le_refl]
  -- integrability of the common integrand, in the `(z, t)` order (used to marginalise)
  have hLR : Integrable (fun w : (ℝ × ℝ) × ℝ =>
      (a w.1.1 * ee (u w.2 * w.1.1) * ee (-(ja : ℝ) * w.1.1))
        * (b w.1.2 * ee (v w.2 * w.1.2) * ee (-(jb : ℝ) * w.1.2)))
      ((volume.prod volume).prod μt) := by
    refine (hG.mul_prod h1).mono' ?_ ?_
    · simp only [ee]; fun_prop
    · filter_upwards with w
      simp only [norm_mul, ee_norm_char, mul_one, one_mul, le_refl]
  have hmarg : Integrable (fun z : ℝ × ℝ =>
      ∫ t, (a z.1 * ee (u t * z.1) * ee (-(ja : ℝ) * z.1))
        * (b z.2 * ee (v t * z.2) * ee (-(jb : ℝ) * z.2)) ∂μt)
      (volume.prod volume) := hLR.integral_prod_left
  -- the pointwise identity in `(ξ₁,ξ₂)`: the `t`-integral of the phase is the inner integral
  have hpt : ∀ ξ₁ ξ₂ : ℝ,
      a ξ₁ * b ξ₂ * (∫ t in (1/2 : ℝ)..1, ee (u t * ξ₁ + v t * ξ₂))
          * ee (-(ja : ℝ) * ξ₁ - (jb : ℝ) * ξ₂)
        = ∫ t, (a ξ₁ * ee (u t * ξ₁) * ee (-(ja : ℝ) * ξ₁))
            * (b ξ₂ * ee (v t * ξ₂) * ee (-(jb : ℝ) * ξ₂)) ∂μt := by
    intro ξ₁ ξ₂
    rw [intervalIntegral.integral_of_le (show (1/2 : ℝ) ≤ 1 by norm_num), ← hs, ← hμt]
    have hrearr : a ξ₁ * b ξ₂
        * (∫ t, ee (u t * ξ₁ + v t * ξ₂) ∂μt) * ee (-(ja : ℝ) * ξ₁ - (jb : ℝ) * ξ₂)
        = (a ξ₁ * b ξ₂ * ee (-(ja : ℝ) * ξ₁ - (jb : ℝ) * ξ₂))
          * (∫ t, ee (u t * ξ₁ + v t * ξ₂) ∂μt) := by ring
    rw [hrearr, ← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    rw [show -(ja : ℝ) * ξ₁ - (jb : ℝ) * ξ₂ = (-(ja : ℝ) * ξ₁) + (-(jb : ℝ) * ξ₂) by ring,
      ee_add_char, ee_add_char]
    ring
  -- the left-hand side, directly as the `(t, z)` iterated integral
  have hA : (∫ t in (1/2 : ℝ)..1,
        cw (fun ξ => a ξ * ee (u t * ξ)) ja * cw (fun ξ => b ξ * ee (v t * ξ)) jb)
      = ∫ t, ∫ z : ℝ × ℝ, (a z.1 * ee (u t * z.1) * ee (-(ja : ℝ) * z.1))
            * (b z.2 * ee (v t * z.2) * ee (-(jb : ℝ) * z.2)) ∂(volume.prod volume) ∂μt := by
    rw [intervalIntegral.integral_of_le (show (1/2 : ℝ) ≤ 1 by norm_num), ← hs, ← hμt]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [cw]
    rw [← MeasureTheory.integral_prod_mul]
  -- the right-hand side, rearranged to the same `(t, z)` iterated integral
  have hB : (∫ ξ₁ : ℝ, ∫ ξ₂ : ℝ,
          a ξ₁ * b ξ₂ * (∫ t in (1/2 : ℝ)..1, ee (u t * ξ₁ + v t * ξ₂))
            * ee (-(ja : ℝ) * ξ₁ - (jb : ℝ) * ξ₂))
      = ∫ t, ∫ z : ℝ × ℝ, (a z.1 * ee (u t * z.1) * ee (-(ja : ℝ) * z.1))
            * (b z.2 * ee (v t * z.2) * ee (-(jb : ℝ) * z.2)) ∂(volume.prod volume) ∂μt := by
    have hstep1 : (∫ ξ₁ : ℝ, ∫ ξ₂ : ℝ,
          a ξ₁ * b ξ₂ * (∫ t in (1/2 : ℝ)..1, ee (u t * ξ₁ + v t * ξ₂))
            * ee (-(ja : ℝ) * ξ₁ - (jb : ℝ) * ξ₂))
        = ∫ ξ₁ : ℝ, ∫ ξ₂ : ℝ,
            ∫ t, (a ξ₁ * ee (u t * ξ₁) * ee (-(ja : ℝ) * ξ₁))
              * (b ξ₂ * ee (v t * ξ₂) * ee (-(jb : ℝ) * ξ₂)) ∂μt := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ξ₁ => ?_)
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ξ₂ => ?_)
      exact hpt ξ₁ ξ₂
    rw [hstep1, MeasureTheory.integral_integral hmarg]
    exact (MeasureTheory.integral_integral_swap hL).symm
  rw [hA, hB]

/-! ## The target statement -/

/-- The oscillatory integral `m̃_{N,ℝ}` with the phase written in the order in which the
general Fubini lemma produces it. -/
lemma mTilde_eq_phase (P : Polynomial ℤ) (N : ℕ) (ξ₁ ξ₂ : ℝ) :
    mTilde P N ξ₁ ξ₂
      = ∫ t in (1/2 : ℝ)..1, ee (((N : ℝ) * t) * ξ₁ + (PevalR P ((N : ℝ) * t)) * ξ₂) := by
  rw [mTilde]
  refine intervalIntegral.integral_congr fun t _ => ?_
  congr 1
  ring

/-- **The Fubini identity of the §6 model approximation** (the "`bn-ident`/Fubini" step): the
time-average of the products of the inverse Fourier coefficients of the modulated bumps
`φ_{N,t} = φ_N e(Nt·)`, `φ̃_{N,t} = φ̃_N e(P(Nt)·)` equals the double integral of the
unmodulated bumps against the oscillatory integral `m̃_{N,ℝ}`.

This is `cw_interval_integral_fubini` specialised to `a = φ_N`, `b = φ̃_N`, `u t = N t`,
`v t = P(Nt)`; the two sides are the two orderings of the iterated integral of the single
integrand `(t,ξ₁,ξ₂) ↦ φ_N(ξ₁) e(Ntξ₁-j₁ξ₁) · φ̃_N(ξ₂) e(P(Nt)ξ₂-j₂ξ₂)`. -/
theorem ModelApproxCore_cw_fubini (P : Polynomial ℤ) (d : ℕ) (N : ℕ) (k₁ k₂ : ℕ)
    (j₁ j₂ : ℤ) :
    ∫ t in (1/2 : ℝ)..1,
        Work.KMTAreas.A7.cw (Work.KMTAreas.A7.varphiNt N k₁ t) j₁
          * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.varphitildeNt P d N k₂ t) j₂
      = ∫ ξ₁ : ℝ, ∫ ξ₂ : ℝ,
          Work.KMTAreas.A7.varphiN N k₁ ξ₁ * Work.KMTAreas.A7.varphitildeN d N k₂ ξ₂
            * Work.KMTAreas.A7.mTilde P N ξ₁ ξ₂
            * Work.KMTAreas.A7.ee (-(j₁ : ℝ) * ξ₁ - (j₂ : ℝ) * ξ₂) := by
  obtain ⟨hAi, hAm⟩ := varphiN_integrable_measurable N k₁
  obtain ⟨hBi, hBm⟩ := varphitildeN_integrable_measurable d N k₂
  trans ∫ ξ₁ : ℝ, ∫ ξ₂ : ℝ,
      varphiN N k₁ ξ₁ * varphitildeN d N k₂ ξ₂
        * (∫ t in (1/2 : ℝ)..1,
            ee (((N : ℝ) * t) * ξ₁ + (PevalR P ((N : ℝ) * t)) * ξ₂))
        * ee (-(j₁ : ℝ) * ξ₁ - (j₂ : ℝ) * ξ₂)
  · exact cw_interval_integral_fubini (a := varphiN N k₁) (b := varphitildeN d N k₂)
      (u := fun t : ℝ => (N : ℝ) * t) (v := fun t : ℝ => PevalR P ((N : ℝ) * t))
      hAi hBi hAm hBm (by fun_prop) (by unfold PevalR; fun_prop) j₁ j₂
  · refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ξ₁ => ?_)
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ξ₂ => ?_)
    simp only [mTilde_eq_phase P N ξ₁ ξ₂]

end

end Work.A7
