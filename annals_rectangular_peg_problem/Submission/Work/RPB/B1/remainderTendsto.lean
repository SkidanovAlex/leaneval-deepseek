import Mathlib

/-!
# The `R → ∞` remainder in the polar-cell area formula

This file proves `Work.RPB.B1.remainderTendsto`: for a `C¹` curve `u : ℝ → ℂ`, the double
integral

`(1 / (2π)) ∫_0^{2π} ∫_0^{2π} Im(u'(t) e^{-iθ}) (√(R² - Im(u(t) e^{-iθ})²) - R) dθ dt`

tends to `0` as `R → ∞`.

The mathematics is a uniform estimate.  If `M` bounds both `‖u t‖` and `‖u'(t)‖` on `[0, 2π]`
(possible because `u` is `C¹` and `[0, 2π]` is compact), then for every `t, θ`

* `|Im(u'(t) e^{-iθ})| ≤ ‖u'(t)‖ ≤ M`, and
* `|√(R² - y²) - R| ≤ y² / R ≤ M² / R` where `y = Im(u(t) e^{-iθ})` and `R ≥ 2M`,

so the integrand is bounded by `M³ / R`.  Integrating twice over an interval of length `2π`
gives `‖…‖ ≤ 4π² M³ / R`, and the prefactor `1 / (2π)` leaves `2π M³ / R → 0`.
-/

namespace Work.RPB.B1

open Complex Real

/-- For `R ≥ 2M ≥ 0` and `|y| ≤ M` the square-root remainder is bounded by `M² / R`. -/
lemma sqrt_rem_bound {M R y : ℝ} (hM : 0 ≤ M) (hR : 2 * M ≤ R) (hy : |y| ≤ M) :
    |Real.sqrt (R ^ 2 - y ^ 2) - R| ≤ M ^ 2 / R := by
  have hR0 : 0 ≤ R := by linarith
  have hyMsq : y ^ 2 ≤ M ^ 2 := by
    have h1 : |y| ^ 2 ≤ M ^ 2 := by nlinarith [abs_nonneg y]
    rwa [sq_abs] at h1
  have hssq : y ^ 2 ≤ R ^ 2 := by nlinarith
  rcases eq_or_lt_of_le hR0 with hR0' | hRpos
  · -- degenerate case `R = 0`, which forces `M = y = 0`
    subst hR0'
    have hM0 : M = 0 := by linarith
    subst hM0
    have hy0 : y = 0 := by
      have : |y| = 0 := le_antisymm (by simpa using hy) (abs_nonneg y)
      exact abs_eq_zero.mp this
    subst hy0
    simp
  · set s := Real.sqrt (R ^ 2 - y ^ 2) with hs
    have hs2 : s ^ 2 = R ^ 2 - y ^ 2 := by
      rw [hs, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ R ^ 2 - y ^ 2)]
    have hsnn : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg _
    have hsle : s ≤ R := by
      rw [hs]
      calc Real.sqrt (R ^ 2 - y ^ 2) ≤ Real.sqrt (R ^ 2) :=
            Real.sqrt_le_sqrt (by linarith [sq_nonneg y])
        _ = R := Real.sqrt_sq hR0
    have hRs : 0 ≤ R - s := by linarith
    rw [abs_sub_comm, abs_of_nonneg hRs]
    have h1 : (R - s) * R ≤ y ^ 2 := by
      calc (R - s) * R ≤ (R - s) * (R + s) := by
              apply mul_le_mul_of_nonneg_left _ hRs
              linarith
        _ = R ^ 2 - s ^ 2 := by ring
        _ = y ^ 2 := by rw [hs2]; ring
    have h2 : R - s ≤ y ^ 2 / R := by
      rw [le_div_iff₀ hRpos]; exact h1
    calc R - s ≤ y ^ 2 / R := h2
      _ ≤ M ^ 2 / R := div_le_div_of_nonneg_right hyMsq hR0

/-- A `C¹` map `u : ℝ → ℂ` admits a single constant `M ≥ 0` bounding both `‖u t‖` and
`‖u'(t)‖` on the compact interval `[0, 2π]`. -/
lemma exists_bound_u_deriv (u : ℝ → ℂ) (hu : ContDiff ℝ 1 u) :
    ∃ M, 0 ≤ M ∧ ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), ‖u t‖ ≤ M ∧ ‖deriv u t‖ ≤ M := by
  obtain ⟨M1, hM1⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 2 * Real.pi)).exists_bound_of_continuousOn
      (hu.continuous.norm.continuousOn)
  obtain ⟨M2, hM2⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 2 * Real.pi)).exists_bound_of_continuousOn
      (hu.continuous_deriv_one.norm.continuousOn)
  simp only [norm_norm] at hM1 hM2
  refine ⟨max M1 M2, ?_, ?_⟩
  · have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := ⟨le_rfl, by positivity⟩
    have h1 : 0 ≤ M1 := le_trans (norm_nonneg (u 0)) (hM1 0 h0)
    exact le_trans h1 (le_max_left _ _)
  · intro t ht
    exact ⟨le_trans (hM1 t ht) (le_max_left _ _), le_trans (hM2 t ht) (le_max_right _ _)⟩

/-- The uniform estimate for the double integral: for `R ≥ max (2M) 1` the whole expression is
bounded by `2π M³ / R`. -/
lemma remainder_integral_bound (u : ℝ → ℂ) {M : ℝ} (hM0 : 0 ≤ M)
    (hMu : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), ‖u t‖ ≤ M)
    (hMd : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), ‖deriv u t‖ ≤ M)
    {R : ℝ} (hR : max (2 * M) 1 ≤ R) :
    ‖(1 / (2 * Real.pi)) *
      ∫ t in (0 : ℝ)..(2 * Real.pi), ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (deriv u t * Complex.exp (-(θ : ℂ) * Complex.I)).im *
          (Real.sqrt (R ^ 2 - (u t * Complex.exp (-(θ : ℂ) * Complex.I)).im ^ 2) - R)‖
      ≤ 2 * Real.pi * M ^ 3 / R := by
  have h2M : 2 * M ≤ R := le_trans (le_max_left _ _) hR
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hR)
  -- pointwise bound on the integrand
  have hpt : ∀ t ∈ Set.uIoc (0 : ℝ) (2 * Real.pi), ∀ θ ∈ Set.uIoc (0 : ℝ) (2 * Real.pi),
      ‖(deriv u t * Complex.exp (-(θ : ℂ) * Complex.I)).im *
        (Real.sqrt (R ^ 2 - (u t * Complex.exp (-(θ : ℂ) * Complex.I)).im ^ 2) - R)‖
        ≤ M ^ 3 / R := by
    intro t ht θ hθ
    have htI : t ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
      rw [Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)] at ht
      exact Set.Ioc_subset_Icc_self ht
    have hθI : θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
      rw [Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)] at hθ
      exact Set.Ioc_subset_Icc_self hθ
    have hexp : ‖Complex.exp (-(θ : ℂ) * Complex.I)‖ = 1 := by
      have : -(θ : ℂ) * Complex.I = ((-θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    have hf1 : |(deriv u t * Complex.exp (-(θ : ℂ) * Complex.I)).im| ≤ M := by
      calc |(deriv u t * Complex.exp (-(θ : ℂ) * Complex.I)).im|
          ≤ ‖deriv u t * Complex.exp (-(θ : ℂ) * Complex.I)‖ := Complex.abs_im_le_norm _
        _ = ‖deriv u t‖ * ‖Complex.exp (-(θ : ℂ) * Complex.I)‖ := norm_mul _ _
        _ = ‖deriv u t‖ := by rw [hexp, mul_one]
        _ ≤ M := hMd t htI
    have hy : |(u t * Complex.exp (-(θ : ℂ) * Complex.I)).im| ≤ M := by
      calc |(u t * Complex.exp (-(θ : ℂ) * Complex.I)).im|
          ≤ ‖u t * Complex.exp (-(θ : ℂ) * Complex.I)‖ := Complex.abs_im_le_norm _
        _ = ‖u t‖ * ‖Complex.exp (-(θ : ℂ) * Complex.I)‖ := norm_mul _ _
        _ = ‖u t‖ := by rw [hexp, mul_one]
        _ ≤ M := hMu t htI
    have hf2 : |Real.sqrt (R ^ 2 - (u t * Complex.exp (-(θ : ℂ) * Complex.I)).im ^ 2) - R|
        ≤ M ^ 2 / R :=
      sqrt_rem_bound hM0 h2M hy
    rw [Real.norm_eq_abs, abs_mul]
    calc |(deriv u t * Complex.exp (-(θ : ℂ) * Complex.I)).im| *
            |Real.sqrt (R ^ 2 - (u t * Complex.exp (-(θ : ℂ) * Complex.I)).im ^ 2) - R|
        ≤ M * (M ^ 2 / R) := mul_le_mul hf1 hf2 (abs_nonneg _) hM0
      _ = M ^ 3 / R := by rw [← mul_div_assoc]; ring
  -- inner integral
  have hinner : ∀ t ∈ Set.uIoc (0 : ℝ) (2 * Real.pi),
      ‖∫ θ in (0 : ℝ)..(2 * Real.pi),
        (deriv u t * Complex.exp (-(θ : ℂ) * Complex.I)).im *
          (Real.sqrt (R ^ 2 - (u t * Complex.exp (-(θ : ℂ) * Complex.I)).im ^ 2) - R)‖
        ≤ M ^ 3 / R * (2 * Real.pi) := by
    intro t ht
    have hthis := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ))
      (b := 2 * Real.pi) (C := M ^ 3 / R)
      (f := fun θ => (deriv u t * Complex.exp (-(θ : ℂ) * Complex.I)).im *
          (Real.sqrt (R ^ 2 - (u t * Complex.exp (-(θ : ℂ) * Complex.I)).im ^ 2) - R))
      (fun θ hθ => hpt t ht θ hθ)
    rwa [sub_zero, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at hthis
  -- outer integral
  have houter := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ))
    (b := 2 * Real.pi) (C := M ^ 3 / R * (2 * Real.pi))
    (f := fun t => ∫ θ in (0 : ℝ)..(2 * Real.pi),
      (deriv u t * Complex.exp (-(θ : ℂ) * Complex.I)).im *
        (Real.sqrt (R ^ 2 - (u t * Complex.exp (-(θ : ℂ) * Complex.I)).im ^ 2) - R))
    (fun t ht => hinner t ht)
  rw [sub_zero, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at houter
  rw [norm_mul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))]
  exact le_trans (mul_le_mul_of_nonneg_left houter (by positivity))
    (le_of_eq (by field_simp))

theorem remainderTendsto (u : ℝ → ℂ) (hu : ContDiff ℝ 1 u) :
    Filter.Tendsto
      (fun R : ℝ => (1 / (2 * Real.pi)) *
        ∫ t in (0 : ℝ)..(2 * Real.pi), ∫ θ in (0 : ℝ)..(2 * Real.pi),
          (deriv u t * Complex.exp (-(θ : ℂ) * Complex.I)).im *
            (Real.sqrt (R ^ 2 - (u t * Complex.exp (-(θ : ℂ) * Complex.I)).im ^ 2) - R))
      Filter.atTop (nhds 0) := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_u_deriv u hu
  have hMu : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), ‖u t‖ ≤ M := fun t ht => (hM t ht).1
  have hMd : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), ‖deriv u t‖ ≤ M := fun t ht => (hM t ht).2
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (h := fun R : ℝ => 2 * Real.pi * M ^ 3 / R) tendsto_const_nhds ?_ ?_ ?_
  · have hfun : (fun R : ℝ => 2 * Real.pi * M ^ 3 / R)
        = fun R : ℝ => (2 * Real.pi * M ^ 3) * R⁻¹ := by
      funext R; rw [div_eq_mul_inv]
    rw [hfun]
    have h := tendsto_inv_atTop_zero.const_mul (2 * Real.pi * M ^ 3)
    rw [mul_zero] at h
    exact h
  · filter_upwards with R
    exact norm_nonneg _
  · filter_upwards [Filter.eventually_ge_atTop (max (2 * M) 1)] with R hR
    exact remainder_integral_bound u hM0 hMu hMd hR

end Work.RPB.B1
