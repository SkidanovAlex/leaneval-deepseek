import Mathlib
import Submission.Commons.Analysis.Fourier.exists_ball_bump_fourier_scaled_measurable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.Fourier

open MeasureTheory

set_option autoImplicit false

/-- **A Schwartz bump adapted to any ball, with a decay constant uniform in the radius.**

For every dimension `d ≥ 1` and every exponent `A ≥ 0` there is a *single* constant `C > 0` such
that for every radius `R ≥ 1` there are a function `ψ : ℝ^d → ℂ` and a measurable density
`Φ : ℝ^d → ℂ` with:

* `Φ` is integrable and vanishes outside the closed ball of radius `σ`, where `σ R ≤ 1`;
* `ψ x = ∫ η, Φ η * exp (2πi ⟪x,η⟫)` (the inverse Fourier transform of `Φ`);
* `‖ψ x‖ ≥ 1/2` on the ball of radius `R`;
* `‖ψ x‖ ≤ C (1 + ‖x‖/R)^{-A}` — the point is that `C` does *not* depend on `R`.

RECIPE.  This is
`Commons.Analysis.Fourier.exists_ball_bump_fourier_scaled_measurable` with the constant made
uniform by *rescaling*: take the case `R = 1` to get `(ψ₁, Φ₁, σ₁)`, `σ₁ ≤ 1`, `Φ₁`
measurable/integrable/supported in `B(0,σ₁)`, `‖ψ₁ y‖ ≥ 1/2` for `‖y‖ ≤ 1`, and
`‖ψ₁ y‖ ≤ C₀ (1+‖y‖)^{-A}`.  Then for `R ≥ 1` set `ψ x := ψ₁ (x / R)` and
`Φ η := R^d * Φ₁ (R η)`; the change of variables `η = R η'` (with `volume` scaling by `R^d`)
turns the representation for `ψ₁` into the representation for `ψ`, the support scales to
`B(0,σ₁/R)`, the lower bound holds on `B(0,R)`, and the decay bound is the *same* `C₀`
applied at `y = x/R`.  (Use `MeasureTheory.Measure.integral_comp_smul`-type scaling lemmas, or
`MeasureTheory.measurePreserving_smul` / the add-Haar behaviour of `volume` on `EuclideanSpace`.) -/
theorem exists_ball_bump_uniform (d : ℕ) (hd : 1 ≤ d) (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R → ∃ (σ : ℝ) (ψ Φ : EuclideanSpace ℝ (Fin d) → ℂ),
      0 < σ ∧ σ * R ≤ 1 ∧ Measurable Φ ∧ MeasureTheory.Integrable Φ ∧
      (∀ η, Φ η ≠ 0 → η ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) σ) ∧
      (∀ x, ψ x = ∫ η, Φ η * Complex.exp (2 * Real.pi * Complex.I * ((∑ i, x i * η i : ℝ) : ℂ))) ∧
      (∀ x, ‖x‖ ≤ R → (1 / 2 : ℝ) ≤ ‖ψ x‖) ∧
      (∀ x, ‖ψ x‖ ≤ C * (1 + ‖x‖ / R) ^ (-A)) := by
  classical
  obtain ⟨ψ₁, Φ₁, σ₁, C₀, hσ₁pos, hσ₁le, hC₀pos, hΦ₁meas, _hΦ₁re, hΦ₁int, hΦ₁supp, hψ₁rep,
    hψ₁lb, hψ₁dec⟩ :=
    exists_ball_bump_fourier_scaled_measurable d hd A hA 1 le_rfl
  refine ⟨C₀, hC₀pos, fun R hR => ?_⟩
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hRne : R ≠ 0 := ne_of_gt hRpos
  let ψ : EuclideanSpace ℝ (Fin d) → ℂ := fun x => ψ₁ (R⁻¹ • x)
  let Φ : EuclideanSpace ℝ (Fin d) → ℂ := fun η => ((R ^ d : ℝ) : ℂ) * Φ₁ (R • η)
  refine ⟨σ₁ / R, ψ, Φ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · positivity
  · rw [div_mul_cancel₀ σ₁ hRne]
    simpa using hσ₁le
  · have hcont : Continuous (fun η : EuclideanSpace ℝ (Fin d) => R • η) := by fun_prop
    exact (hΦ₁meas.comp hcont.measurable).const_mul _
  · have h1 : MeasureTheory.Integrable
        (fun η : EuclideanSpace ℝ (Fin d) => Φ₁ (R • η))
        (volume : Measure (EuclideanSpace ℝ (Fin d))) := hΦ₁int.comp_smul hRne
    exact h1.const_mul _
  · intro η hη
    have hΦ₁ne : Φ₁ (R • η) ≠ 0 := by
      intro h0
      exact hη (by simp [Φ, h0])
    have hmem : R • η ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) σ₁ :=
      hΦ₁supp (R • η) hΦ₁ne
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hmem ⊢
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hRpos] at hmem
    rw [le_div_iff₀ hRpos]
    linarith
  · intro x
    have hinner : ∀ (y η : EuclideanSpace ℝ (Fin d)),
        ((∑ i, y i * η i : ℝ) : ℂ) = ((inner ℝ y η : ℝ) : ℂ) := by
      intro y η
      congr 1
      rw [PiLp.inner_apply]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    set g : EuclideanSpace ℝ (Fin d) → ℂ := fun u =>
      Φ₁ u * Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ (R⁻¹ • x) u : ℝ) : ℂ)) with hg
    have hg1 : ∫ u, g u = ψ₁ (R⁻¹ • x) := by
      rw [hψ₁rep (R⁻¹ • x)]
      apply integral_congr_ae
      filter_upwards with u
      simp only [hg]
      rw [hinner (R⁻¹ • x) u]
    have hgcomp : ∀ u : EuclideanSpace ℝ (Fin d), g (R • u) = Φ₁ (R • u) *
        Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ x u : ℝ) : ℂ)) := by
      intro u
      simp only [hg]
      have harg : inner ℝ (R⁻¹ • x) (R • u) = inner ℝ x u := by
        rw [real_inner_smul_left, real_inner_smul_right]
        field_simp
      rw [harg]
    have hcv : ∫ u, g (R • u) = (R ^ d)⁻¹ • ∫ u, g u := by
      have h := Measure.integral_comp_smul_of_nonneg
        (volume : Measure (EuclideanSpace ℝ (Fin d))) g R (hR := hRpos.le)
      rwa [finrank_euclideanSpace_fin] at h
    calc ψ x = ψ₁ (R⁻¹ • x) := rfl
      _ = ∫ u, g u := hg1.symm
      _ = (R ^ d) • ∫ u, g (R • u) := by
            rw [hcv, smul_smul, mul_inv_cancel₀ (pow_ne_zero d hRne), one_smul]
      _ = ∫ u, ((R ^ d : ℝ) : ℂ) * (Φ₁ (R • u) *
            Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ x u : ℝ) : ℂ))) := by
            rw [Complex.real_smul, ← integral_const_mul]
            apply integral_congr_ae
            filter_upwards with u
            rw [hgcomp u]
      _ = ∫ η, (((R ^ d : ℝ) : ℂ) * Φ₁ (R • η)) *
            Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ x η : ℝ) : ℂ)) := by
            apply integral_congr_ae
            filter_upwards with η
            ring
      _ = ∫ η, Φ η * Complex.exp (2 * Real.pi * Complex.I * ((∑ i, x i * η i : ℝ) : ℂ)) := by
            apply integral_congr_ae
            filter_upwards with η
            simp only [Φ]
            rw [hinner x η]
  · intro x hx
    have hu : ‖R⁻¹ • x‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hRpos), inv_mul_eq_div]
      rw [div_le_iff₀ hRpos]
      linarith
    simpa only [ψ] using hψ₁lb (R⁻¹ • x) hu
  · intro x
    have h1 := hψ₁dec (R⁻¹ • x)
    have h2 : ‖R⁻¹ • x‖ = ‖x‖ / R := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hRpos), inv_mul_eq_div]
    rw [h2] at h1
    simpa [ψ] using h1

end Commons.Analysis.Fourier
