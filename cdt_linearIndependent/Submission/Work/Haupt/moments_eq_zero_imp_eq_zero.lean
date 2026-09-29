import Mathlib

/-!
# `Work.Haupt.moments_eq_zero_imp_eq_zero`

If a function `g` on `ℂ \ {0}` has all of its Laurent moments vanishing,
`∮_{C(0,ρ)} z ^ (-(n+1)) · g z = 0` for every `n : ℤ` and every `ρ > 0`,
then `g` vanishes identically.

The proof is via Fourier analysis on the circle `C(0,ρ)`: writing `φ θ = g (ρ · e^{iθ})`,
the moments are (up to a non-zero factor) the Fourier coefficients of `φ`; a continuous
periodic function all of whose Fourier coefficients vanish is zero.
-/

set_option linter.style.haveILetI false

namespace Work.Haupt

noncomputable section

open Complex

/-- Change of variables: the circle integral of `z ^ (-(n+1)) * g z` over `C(0,ρ)` (`ρ > 0`)
as an angle integral. -/
private theorem circleIntegral_zpow_mul_eq (g : ℂ → ℂ) (n : ℤ) {ρ : ℝ} (hρ : 0 < ρ) :
    (∮ t in C(0, ρ), t ^ (-(n + 1)) * g t)
      = Complex.I * (ρ : ℂ) ^ (-n) *
        (∫ θ in 0..2 * Real.pi, Complex.exp (-(n : ℂ) * (θ : ℂ) * Complex.I) *
          g ((ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) := by
  have key : ∀ θ : ℝ, deriv (circleMap 0 ρ) θ •
      (((ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ (-(n + 1)) *
        g ((ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
      = Complex.I * (ρ : ℂ) ^ (-n) *
        (Complex.exp (-(n : ℂ) * (θ : ℂ) * Complex.I) *
          g ((ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) := by
    intro θ
    have hρne : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
    rw [smul_eq_mul, deriv_circleMap, circleMap, zero_add, mul_zpow]
    rw [← Complex.exp_int_mul]
    have hpow : (↑ρ : ℂ) ^ (-(n + 1)) * ↑ρ = (↑ρ) ^ (-n) := by
      rw [show ((↑ρ : ℂ) ^ (-n)) = (↑ρ) ^ (-(n + 1) + 1) by ring_nf, zpow_add₀ hρne,
        zpow_one]
    have hexp : Complex.exp (↑θ * Complex.I) * Complex.exp (↑(-(n + 1)) * (↑θ * Complex.I))
        = Complex.exp (-↑n * ↑θ * Complex.I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [← hpow, ← hexp]; ring
  rw [circleIntegral]
  simp only [circleMap, zero_add]
  rw [show (∫ θ in 0..2 * Real.pi, deriv (circleMap 0 ρ) θ •
        ((↑ρ * Complex.exp (↑θ * Complex.I)) ^ (-(n + 1)) *
          g (↑ρ * Complex.exp (↑θ * Complex.I))))
      = ∫ θ in 0..2 * Real.pi, Complex.I * (↑ρ) ^ (-n) *
        (Complex.exp (-(↑n) * ↑θ * Complex.I) * g (↑ρ * Complex.exp (↑θ * Complex.I)))
      from by
        apply intervalIntegral.integral_congr; intro θ _; exact key θ]
  rw [intervalIntegral.integral_const_mul]

/-- A continuous `2π`-periodic function all of whose Fourier moments vanish is zero. -/
private theorem fourier_exp_moments_eq_zero_imp_eq_zero {φ : ℝ → ℂ} (hφ : Continuous φ)
    (hper : ∀ θ, φ (θ + 2 * Real.pi) = φ θ)
    (h : ∀ n : ℤ,
      (∫ θ in 0..2 * Real.pi, Complex.exp (-(n : ℂ) * (θ : ℂ) * Complex.I) * φ θ) = 0) :
    ∀ θ ∈ Set.Ioc 0 (2 * Real.pi), φ θ = 0 := by
  have hp : (0 : ℝ) < 2 * Real.pi := by positivity
  haveI : Fact ((0 : ℝ) < 2 * Real.pi) := ⟨hp⟩
  let F : C(AddCircle (2 * Real.pi), ℂ) :=
    ⟨AddCircle.liftIoc (2 * Real.pi) 0 φ,
      AddCircle.liftIoc_continuous (p := 2 * Real.pi) (a := 0) (f := φ)
        (by simpa using (hper 0).symm) (by simpa using hφ.continuousOn)⟩
  have hcoeff : ∀ n, fourierCoeff F n = 0 := by
    intro n
    have hfourier : ∀ x : ℝ, fourier (-n) (x : AddCircle (2 * Real.pi))
        = Complex.exp (-(n : ℂ) * (x : ℂ) * Complex.I) := by
      intro x
      rw [fourier_coe_apply]; congr 1; push_cast; field_simp
    rw [fourierCoeff_eq_intervalIntegral F n 0, zero_add]
    have hint : (∫ x in 0..2 * Real.pi,
          fourier (-n) (x : AddCircle (2 * Real.pi)) • F (x : AddCircle (2 * Real.pi)))
        = ∫ x in 0..2 * Real.pi, Complex.exp (-(n : ℂ) * (x : ℂ) * Complex.I) * φ x := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with x hx
      have hx' : x ∈ Set.Ioc (0 : ℝ) (2 * Real.pi) := by
        rw [Set.uIoc_of_le hp.le] at hx; exact hx
      rw [hfourier x, smul_eq_mul]
      have hFx : F (x : AddCircle (2 * Real.pi)) = φ x := by
        show AddCircle.liftIoc (2 * Real.pi) 0 φ (x : AddCircle (2 * Real.pi)) = φ x
        exact AddCircle.liftIoc_coe_apply (by simpa using hx')
      rw [hFx]
    rw [hint, h n, smul_zero]
  have hzero : ∀ y, F y = 0 := by
    intro y
    have hsum : Summable (fourierCoeff F) := by
      rw [show fourierCoeff F = fun _ => 0 from funext hcoeff]; exact summable_zero
    have hpt := has_pointwise_sum_fourier_series_of_summable hsum y
    have : HasSum (fun _ : ℤ => (0 : ℂ)) (F y) := by simpa [hcoeff] using hpt
    exact this.unique hasSum_zero
  intro θ hθ
  have : F (θ : AddCircle (2 * Real.pi)) = φ θ := by
    show AddCircle.liftIoc (2 * Real.pi) 0 φ (θ : AddCircle (2 * Real.pi)) = φ θ
    exact AddCircle.liftIoc_coe_apply (by simpa using hθ)
  rw [← this, hzero]

theorem moments_eq_zero_imp_eq_zero {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g {t : ℂ | t ≠ 0})
    (h : ∀ (n : ℤ) (ρ : ℝ), 0 < ρ → (∮ t in C(0, ρ), t ^ (-(n + 1)) * g t) = 0) :
    ∀ t : ℂ, t ≠ 0 → g t = 0 := by
  intro t ht
  have hρ : (0 : ℝ) < ‖t‖ := norm_pos_iff.mpr ht
  set φ : ℝ → ℂ := fun θ => g ((‖t‖ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) with hφdef
  have hφcont : Continuous φ := by
    rw [hφdef]
    refine hg.continuousOn.comp_continuous (by fun_prop) (fun θ => ?_)
    exact mul_ne_zero (by exact_mod_cast hρ.ne') (Complex.exp_ne_zero _)
  have hφper : ∀ θ, φ (θ + 2 * Real.pi) = φ θ := by
    intro θ
    rw [hφdef]
    have harg : (↑(θ + 2 * Real.pi) : ℂ) * Complex.I
        = ↑θ * Complex.I + 2 * ↑Real.pi * Complex.I := by push_cast; ring
    simp only
    rw [harg, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have hmom : ∀ n : ℤ,
      (∫ θ in 0..2 * Real.pi, Complex.exp (-(n : ℂ) * (θ : ℂ) * Complex.I) * φ θ) = 0 := by
    intro n
    have h1 := circleIntegral_zpow_mul_eq g n hρ
    rw [h n ‖t‖ hρ] at h1
    have hne : Complex.I * (‖t‖ : ℂ) ^ (-n) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (zpow_ne_zero _ (by exact_mod_cast hρ.ne'))
    rw [hφdef]
    exact (mul_eq_zero.mp h1.symm).resolve_left hne
  have hz := fourier_exp_moments_eq_zero_imp_eq_zero hφcont hφper hmom
  have htmem : t ∈ circleMap (0 : ℂ) ‖t‖ '' Set.Ioc 0 (2 * Real.pi) := by
    rw [image_circleMap_Ioc, Metric.mem_sphere, dist_eq_norm, sub_zero,
      abs_of_nonneg (norm_nonneg t)]
  obtain ⟨θ, hθ, hθeq⟩ := htmem
  have hgt : g (circleMap (0 : ℂ) ‖t‖ θ) = φ θ := by
    rw [hφdef]
    congr 1
    simp [circleMap]
  rw [← hθeq, hgt, hz θ hθ]

end

end Work.Haupt
