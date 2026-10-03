import Mathlib
import Submission.Lib.Unif2.Work.Potential.periodic_vertical_integral_invariance

/-!
# Fourier coefficient of a periodic holomorphic function on a half-plane

If `G` is holomorphic on the half-plane `{ζ : ζ.re < L}` and `2πi`-periodic there, then for every
non-zero integer `k` the `k`-th Fourier coefficient of the real part of `G` along the vertical line
`ζ = log r + θ i` is of the form `A r ^ k + B r ^ (-k)` for two constants `A`, `B` independent of
`r`.

The proof writes `Re G = (G + conj G)/2`.  For the holomorphic part we use that
`G (log r + θ i) = r^j (G (log r + θ i) exp (-j (log r + θ i)))` and that the integral of the
`2πi`-periodic holomorphic function `z ↦ G z * exp (-j z)` over a vertical segment is independent of
the segment (`Work.Potential.periodic_vertical_integral_invariance`).  The conjugate part is the
conjugate of the `(-k)`-th coefficient, and `conj (r ^ (-k)) = r ^ (-k)` because `r` is real.

## Main results

* `Work.Potential.periodic_holomorphic_fourier_coefficient`
-/

set_option linter.unusedVariables false

namespace Work.Potential

open scoped Interval ComplexConjugate
open MeasureTheory

/-- `exp (j log r) = r ^ j` for `r > 0` and `j : ℤ`. -/
private lemma exp_intCast_mul_log {r : ℝ} (hr : 0 < r) (j : ℤ) :
    Complex.exp ((j : ℂ) * (Real.log r : ℂ)) = (r : ℂ) ^ j := by
  have h2 : Complex.exp ((Real.log r : ℂ)) = (r : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hr]
  rw [Complex.exp_int_mul (Real.log r : ℂ) j, h2]

/-- `conj (r ^ n) = r ^ n` for `r : ℝ` and `n : ℤ`. -/
private lemma star_real_zpow (r : ℝ) (n : ℤ) :
    (starRingEnd ℂ) ((r : ℂ) ^ n) = (r : ℂ) ^ n := by
  rw [← Complex.ofReal_zpow]
  simp

/-- Pointwise identity: the Fourier weight of index `j` equals `r ^ j` times the exponential
weight `z ↦ exp (-j z)` evaluated at `log r + θ i`. -/
private lemma weighted_pointwise {r : ℝ} (hr : 0 < r) (j : ℤ) (θ : ℝ) :
    Complex.exp (-(((j : ℝ) * θ : ℂ) * Complex.I))
      = (r : ℂ) ^ j * Complex.exp (-(j : ℂ) * ((Real.log r : ℂ) + θ * Complex.I)) := by
  rw [← exp_intCast_mul_log hr j, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The Fourier weights of indices `j` and `-j` are conjugate to each other. -/
private lemma star_weight (j : ℤ) (θ : ℝ) :
    (starRingEnd ℂ) (Complex.exp (-(((j : ℝ) * θ : ℂ) * Complex.I)))
      = Complex.exp (-((((-j : ℤ) : ℝ) * θ : ℂ) * Complex.I)) := by
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- The weighted function `z ↦ G z * exp (-j z)` is analytic wherever `G` is. -/
private lemma weighted_analytic {L : ℝ} {G : ℂ → ℂ}
    (hG : ∀ ζ : ℂ, ζ.re < L → AnalyticAt ℂ G ζ) (j : ℤ) :
    ∀ ζ : ℂ, ζ.re < L → AnalyticAt ℂ (fun z => G z * Complex.exp (-(j : ℂ) * z)) ζ := by
  intro ζ hζ
  exact (hG ζ hζ).mul (by fun_prop)

/-- The weighted function `z ↦ G z * exp (-j z)` is `2πi`-periodic whenever `G` is. -/
private lemma weighted_periodic {L : ℝ} {G : ℂ → ℂ}
    (hper : ∀ ζ : ℂ, ζ.re < L → G (ζ + 2 * Real.pi * Complex.I) = G ζ) (j : ℤ) :
    ∀ ζ : ℂ, ζ.re < L →
      G (ζ + 2 * Real.pi * Complex.I) * Complex.exp (-(j : ℂ) * (ζ + 2 * Real.pi * Complex.I))
        = G ζ * Complex.exp (-(j : ℂ) * ζ) := by
  intro ζ hζ
  have hexp : Complex.exp (-(j : ℂ) * (ζ + 2 * Real.pi * Complex.I))
      = Complex.exp (-(j : ℂ) * ζ) := by
    rw [show -(j : ℂ) * (ζ + 2 * Real.pi * Complex.I)
          = -(j : ℂ) * ζ + (-(j : ℂ)) * (2 * Real.pi * Complex.I) by ring, Complex.exp_add]
    have he : Complex.exp ((-(j : ℂ)) * (2 * Real.pi * Complex.I)) = 1 := by
      rw [show (-(j : ℂ)) = ((-j : ℤ) : ℂ) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I (-j)
    rw [he, mul_one]
  rw [hper ζ hζ, hexp]

/-- **The holomorphic Fourier coefficient is `r ^ j` times a constant.**  For `j : ℤ` the integral
of `G (log r + θ i) * exp (-(j θ) i)` over one period equals `r ^ j` times the same integral
computed at a fixed reference radius `r₀`. -/
private lemma fourier_eq_zpow_mul
    {L : ℝ} {G : ℂ → ℂ}
    (hG : ∀ ζ : ℂ, ζ.re < L → AnalyticAt ℂ G ζ)
    (hper : ∀ ζ : ℂ, ζ.re < L → G (ζ + 2 * Real.pi * Complex.I) = G ζ)
    {r₀ : ℝ} (hr₀ : 0 < r₀) (hr₀L : Real.log r₀ < L)
    (j : ℤ) {r : ℝ} (hr : 0 < r) (hrL : Real.log r < L) :
    (∫ θ in (0:ℝ)..(2 * Real.pi),
        G ((Real.log r : ℂ) + θ * Complex.I)
          * Complex.exp (-(((j : ℝ) * θ : ℂ) * Complex.I)))
      = (r : ℂ) ^ j *
        (∫ θ in (0:ℝ)..(2 * Real.pi),
          G ((Real.log r₀ : ℂ) + θ * Complex.I)
            * Complex.exp (-(j : ℂ) * ((Real.log r₀ : ℂ) + θ * Complex.I))) := by
  have hinv :
      (∫ θ in (0:ℝ)..(2 * Real.pi),
          G ((Real.log r : ℂ) + θ * Complex.I)
            * Complex.exp (-(j : ℂ) * ((Real.log r : ℂ) + θ * Complex.I)))
        = ∫ θ in (0:ℝ)..(2 * Real.pi),
          G ((Real.log r₀ : ℂ) + θ * Complex.I)
            * Complex.exp (-(j : ℂ) * ((Real.log r₀ : ℂ) + θ * Complex.I)) :=
    periodic_vertical_integral_invariance (weighted_analytic hG j) (weighted_periodic hper j)
      hr hrL hr₀ hr₀L
  have hcongr :
      (∫ θ in (0:ℝ)..(2 * Real.pi),
          G ((Real.log r : ℂ) + θ * Complex.I)
            * Complex.exp (-(((j : ℝ) * θ : ℂ) * Complex.I)))
        = ∫ θ in (0:ℝ)..(2 * Real.pi),
            (r : ℂ) ^ j * (G ((Real.log r : ℂ) + θ * Complex.I)
              * Complex.exp (-(j : ℂ) * ((Real.log r : ℂ) + θ * Complex.I))) := by
    apply intervalIntegral.integral_congr
    intro θ _
    change G ((Real.log r : ℂ) + θ * Complex.I)
          * Complex.exp (-(((j : ℝ) * θ : ℂ) * Complex.I))
        = (r : ℂ) ^ j * (G ((Real.log r : ℂ) + θ * Complex.I)
            * Complex.exp (-(j : ℂ) * ((Real.log r : ℂ) + θ * Complex.I)))
    rw [weighted_pointwise hr j θ]
    ring
  rw [hcongr, intervalIntegral.integral_const_mul, ← hinv]

/-- The conjugate of the `k`-th Fourier coefficient of `conj G` is the `(-k)`-th Fourier
coefficient of `G`. -/
private lemma conj_fourier_eq (G : ℂ → ℂ) (r : ℝ) (k : ℤ) :
    (∫ θ in (0:ℝ)..(2 * Real.pi),
        (starRingEnd ℂ) (G ((Real.log r : ℂ) + θ * Complex.I))
          * Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I)))
      = (starRingEnd ℂ)
          (∫ θ in (0:ℝ)..(2 * Real.pi),
            G ((Real.log r : ℂ) + θ * Complex.I)
              * Complex.exp (-((((-k : ℤ) : ℝ) * θ : ℂ) * Complex.I))) := by
  rw [← intervalIntegral.intervalIntegral_conj]
  apply intervalIntegral.integral_congr
  intro θ _
  change (starRingEnd ℂ) (G ((Real.log r : ℂ) + θ * Complex.I))
        * Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I))
      = (starRingEnd ℂ) (G ((Real.log r : ℂ) + θ * Complex.I)
          * Complex.exp (-((((-k : ℤ) : ℝ) * θ : ℂ) * Complex.I)))
  rw [map_mul, star_weight (-k) θ]
  simp only [neg_neg]

theorem periodic_holomorphic_fourier_coefficient
    {L : ℝ} {G : ℂ → ℂ}
    (hG : ∀ ζ : ℂ, ζ.re < L → AnalyticAt ℂ G ζ)
    (hper : ∀ ζ : ℂ, ζ.re < L → G (ζ + 2 * Real.pi * Complex.I) = G ζ)
    {k : ℤ} (hk : k ≠ 0) :
    ∃ A B : ℂ, ∀ r : ℝ, 0 < r → Real.log r < L →
      (∫ θ in (0:ℝ)..(2 * Real.pi),
          ((G ((Real.log r : ℂ) + θ * Complex.I)).re : ℂ)
            * Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I)))
        = 2 * Real.pi * (A * (r : ℂ) ^ k + B * (r : ℂ) ^ (-k)) := by
  -- a reference radius in the half-plane
  set r₀ : ℝ := Real.exp (L - 1) with hr₀def
  have hr₀ : 0 < r₀ := Real.exp_pos _
  have hr₀L : Real.log r₀ < L := by
    rw [hr₀def, Real.log_exp]; linarith
  -- the two reference Fourier coefficients
  set Ck : ℂ := ∫ θ in (0:ℝ)..(2 * Real.pi),
      G ((Real.log r₀ : ℂ) + θ * Complex.I)
        * Complex.exp (-(k : ℂ) * ((Real.log r₀ : ℂ) + θ * Complex.I)) with hCkdef
  set Cmk : ℂ := ∫ θ in (0:ℝ)..(2 * Real.pi),
      G ((Real.log r₀ : ℂ) + θ * Complex.I)
        * Complex.exp (-((-k : ℤ) : ℂ) * ((Real.log r₀ : ℂ) + θ * Complex.I)) with hCmkdef
  refine ⟨Ck / (4 * (Real.pi : ℂ)), (starRingEnd ℂ) Cmk / (4 * (Real.pi : ℂ)), ?_⟩
  intro r hr hrL
  -- the holomorphic part
  have hPk : (∫ θ in (0:ℝ)..(2 * Real.pi),
        G ((Real.log r : ℂ) + θ * Complex.I)
          * Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I))) = (r : ℂ) ^ k * Ck := by
    rw [fourier_eq_zpow_mul hG hper hr₀ hr₀L k hr hrL, ← hCkdef]
  -- the conjugate part
  have hPmk : (∫ θ in (0:ℝ)..(2 * Real.pi),
        G ((Real.log r : ℂ) + θ * Complex.I)
          * Complex.exp (-((((-k : ℤ) : ℝ) * θ : ℂ) * Complex.I)))
      = (r : ℂ) ^ (-k) * Cmk := by
    rw [fourier_eq_zpow_mul hG hper hr₀ hr₀L (-k) hr hrL, ← hCmkdef]
  have hQ : (∫ θ in (0:ℝ)..(2 * Real.pi),
        (starRingEnd ℂ) (G ((Real.log r : ℂ) + θ * Complex.I))
          * Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I)))
      = (r : ℂ) ^ (-k) * (starRingEnd ℂ) Cmk := by
    rw [conj_fourier_eq G r k, hPmk, map_mul, star_real_zpow]
  -- split `Re G`
  have hsplit : (∫ θ in (0:ℝ)..(2 * Real.pi),
        ((G ((Real.log r : ℂ) + θ * Complex.I)).re : ℂ)
          * Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I)))
      = (1 / 2) * (∫ θ in (0:ℝ)..(2 * Real.pi),
            G ((Real.log r : ℂ) + θ * Complex.I)
              * Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I)))
        + (1 / 2) * (∫ θ in (0:ℝ)..(2 * Real.pi),
            (starRingEnd ℂ) (G ((Real.log r : ℂ) + θ * Complex.I))
              * Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I))) := by
    have hcG : Continuous (fun θ : ℝ => G ((Real.log r : ℂ) + θ * Complex.I)) := by
      rw [continuous_iff_continuousAt]
      intro θ
      refine ((hG _ ?_).continuousAt).comp (by fun_prop)
      simp [hrL]
    have hcE : Continuous (fun θ : ℝ =>
        Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I))) := by fun_prop
    have hI1 : IntervalIntegrable (fun θ : ℝ => (1 / 2 : ℂ)
        * (G ((Real.log r : ℂ) + θ * Complex.I)
          * Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I)))) volume (0 : ℝ)
        (2 * Real.pi) :=
      (continuous_const.mul (hcG.mul hcE)).intervalIntegrable _ _
    have hI2 : IntervalIntegrable (fun θ : ℝ => (1 / 2 : ℂ)
        * ((starRingEnd ℂ) (G ((Real.log r : ℂ) + θ * Complex.I))
          * Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I)))) volume (0 : ℝ)
        (2 * Real.pi) :=
      (continuous_const.mul (hcG.star.mul hcE)).intervalIntegrable _ _
    have h1 : (∫ θ in (0:ℝ)..(2 * Real.pi),
          ((G ((Real.log r : ℂ) + θ * Complex.I)).re : ℂ)
            * Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I)))
        = ∫ θ in (0:ℝ)..(2 * Real.pi),
            (1 / 2) * (G ((Real.log r : ℂ) + θ * Complex.I)
                * Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I)))
              + (1 / 2) * ((starRingEnd ℂ) (G ((Real.log r : ℂ) + θ * Complex.I))
                * Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I))) := by
      apply intervalIntegral.integral_congr
      intro θ _
      change ((G ((Real.log r : ℂ) + θ * Complex.I)).re : ℂ)
            * Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I))
          = (1 / 2) * (G ((Real.log r : ℂ) + θ * Complex.I)
                * Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I)))
              + (1 / 2) * ((starRingEnd ℂ) (G ((Real.log r : ℂ) + θ * Complex.I))
                * Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I)))
      rw [Complex.re_eq_add_conj]
      ring
    rw [h1, intervalIntegral.integral_add hI1 hI2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  rw [hsplit, hPk, hQ]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

end Work.Potential
