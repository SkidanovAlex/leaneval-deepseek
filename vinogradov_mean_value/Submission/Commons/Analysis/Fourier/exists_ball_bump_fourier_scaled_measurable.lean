import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Submission.Commons.Analysis.Fourier.half_integral_le_re_fourierInv
import Submission.Commons.Analysis.Distribution.schwartzMap_decay_one_add_norm

namespace Commons.Analysis.Fourier

open MeasureTheory FourierTransform Metric
open scoped FourierTransform RealInnerProductSpace

set_option autoImplicit false

/-- **A Schwartz bump adapted to a ball, with Fourier support in a small ball, with a
measurable density.**

This is `Commons.Analysis.Fourier.exists_ball_bump_fourier_scaled`
(`Submission/Commons/Analysis/Fourier/exists_ball_bump_fourier_scaled.lean`) with the extra
conclusion that the density `Φ` is *measurable* (not merely integrable).  That measurability
is needed to use the density as an integrand in the explicit "Fourier representation"
formalism (`IsFourierRep`), where the datum is a finite measure together with a measurable
density supported in the frequency set.

RECIPE.  Copy the proof of `exists_ball_bump_fourier_scaled` verbatim: there
`Φ η = R^d * χ (R η)` with `χ = b.normed volume` a `C^∞` compactly supported bump, hence
`Φ` is continuous (it is `(R^d) • (χ ∘ (R • ·))`, a composition of the continuous `χ` with a
continuous linear map), and a continuous function on a second countable space is measurable:
`hΦ_cont.measurable`. -/
theorem exists_ball_bump_fourier_scaled_measurable (d : ℕ) (hd : 1 ≤ d) (A : ℝ) (hA : 0 ≤ A)
    (R : ℝ) (hR : 1 ≤ R) :
    ∃ (ψ Φ : EuclideanSpace ℝ (Fin d) → ℂ) (σ C : ℝ),
      0 < σ ∧ σ * R ≤ 1 ∧ 0 < C ∧
      Measurable Φ ∧ (∀ η, 0 ≤ (Φ η).re) ∧ MeasureTheory.Integrable Φ ∧
      (∀ η, Φ η ≠ 0 → η ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) σ) ∧
      (∀ x, ψ x = ∫ η, Φ η * Complex.exp (2 * Real.pi * Complex.I * ((∑ i, x i * η i : ℝ) : ℂ))) ∧
      (∀ x, ‖x‖ ≤ R → (1 / 2 : ℝ) ≤ ‖ψ x‖) ∧
      (∀ x, ‖ψ x‖ ≤ C * (1 + ‖x‖ / R) ^ (-A)) := by
  classical
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hRne : R ≠ 0 := ne_of_gt hRpos
  -- ## The bump function `χ`
  let b : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) := ⟨1 / 16, 1 / 8, by norm_num, by norm_num⟩
  let χ : EuclideanSpace ℝ (Fin d) → ℝ :=
    b.normed (volume : Measure (EuclideanSpace ℝ (Fin d)))
  have hχ_diff : ContDiff ℝ (↑(⊤ : ℕ∞)) χ := b.contDiff_normed
  have hχ_cs : HasCompactSupport χ := b.hasCompactSupport_normed
  have hχ_nn : ∀ x, 0 ≤ χ x := fun x => b.nonneg_normed x
  have hχ_int : Integrable χ (volume : Measure (EuclideanSpace ℝ (Fin d))) := b.integrable_normed
  have hχ_intval : ∫ x, χ x = 1 := b.integral_normed
  have hχ_supp : ∀ w, 1 / 8 < ‖w‖ → χ w = 0 := by
    intro w hw
    have hdist : b.rOut ≤ dist w 0 := by
      rw [dist_eq_norm, show b.rOut = 1 / 8 from rfl]
      simpa using hw.le
    have hb0 : (b : EuclideanSpace ℝ (Fin d) → ℝ) w = 0 := ContDiffBump.zero_of_le_dist b hdist
    rw [show χ = b.normed (volume : Measure (EuclideanSpace ℝ (Fin d))) from rfl,
      ContDiffBump.normed_def, hb0, zero_div]
  -- ## The complexified bump, as a Schwartz function, and its inverse Fourier transform
  let χc : EuclideanSpace ℝ (Fin d) → ℂ := fun x => (χ x : ℂ)
  have hχc_diff : ContDiff ℝ (↑(⊤ : ℕ∞)) χc :=
    (Complex.ofRealCLM.contDiff (n := ↑(⊤ : ℕ∞))).comp hχ_diff
  have hχc_cs : HasCompactSupport χc :=
    hχ_cs.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  let χs : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ := hχc_cs.toSchwartzMap hχc_diff
  have hχs_coe : (χs : EuclideanSpace ℝ (Fin d) → ℂ) = χc :=
    funext (fun x => HasCompactSupport.toSchwartzMap_toFun hχc_cs hχc_diff x)
  let φ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ := 𝓕⁻ χs
  have hφ_coe : (φ : EuclideanSpace ℝ (Fin d) → ℂ) = 𝓕⁻ χc := by
    rw [show φ = 𝓕⁻ χs from rfl, SchwartzMap.fourierInv_coe, hχs_coe]
  -- ## The rescaled density `Φ` and its inverse Fourier transform `ψ`
  let Φ : EuclideanSpace ℝ (Fin d) → ℂ := fun η => ((R ^ d : ℝ) : ℂ) * (χ (R • η) : ℂ)
  let ψ : EuclideanSpace ℝ (Fin d) → ℂ := fun x =>
    ∫ η, Φ η * Complex.exp (2 * Real.pi * Complex.I * ((∑ i, x i * η i : ℝ) : ℂ))
  -- ## Measurability of `Φ` (it is continuous)
  have hΦ_meas : Measurable Φ := by
    have hχ_cont : Continuous χ := hχ_diff.continuous
    have hsmul : Continuous (fun η : EuclideanSpace ℝ (Fin d) => R • η) :=
      (continuous_const (y := R)).smul continuous_id
    have h1 : Continuous (fun η : EuclideanSpace ℝ (Fin d) => χ (R • η)) :=
      hχ_cont.comp hsmul
    have h2 : Continuous (fun η : EuclideanSpace ℝ (Fin d) => ((χ (R • η) : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp h1
    have h3 : Continuous (fun η : EuclideanSpace ℝ (Fin d) =>
        ((R ^ d : ℝ) : ℂ) * ((χ (R • η) : ℝ) : ℂ)) :=
      continuous_const.mul h2
    exact h3.measurable
  -- ## Positivity of the real part
  have hΦ_re : ∀ η, 0 ≤ (Φ η).re := by
    intro η
    rw [show Φ η = ((R ^ d : ℝ) : ℂ) * (χ (R • η) : ℂ) from rfl]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_nonneg (by positivity) (hχ_nn _)
  -- ## Integrability
  have hΦ_int : Integrable Φ (volume : Measure (EuclideanSpace ℝ (Fin d))) := by
    have h1 : Integrable (fun η : EuclideanSpace ℝ (Fin d) => χ (R • η))
        (volume : Measure (EuclideanSpace ℝ (Fin d))) := hχ_int.comp_smul hRne
    have h2 : Integrable (fun η : EuclideanSpace ℝ (Fin d) => ((χ (R • η) : ℝ) : ℂ))
        (volume : Measure (EuclideanSpace ℝ (Fin d))) := h1.ofReal
    have h3 := h2.const_mul ((R ^ d : ℝ) : ℂ)
    simpa only [Φ] using h3
  -- ## The support is contained in a ball of radius `1/(8R)`
  have hΦ_supp : ∀ η, Φ η ≠ 0 →
      η ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (1 / (8 * R)) := by
    intro η hη
    have hχne : χ (R • η) ≠ 0 := by
      intro h0
      apply hη
      simp [Φ, h0]
    have hnorm : ‖R • η‖ ≤ 1 / 8 := le_of_not_gt (fun hlt => hχne (hχ_supp _ hlt))
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hRpos] at hnorm
    have h8R : 0 < 8 * R := by positivity
    rw [le_div_iff₀ h8R]
    nlinarith [hnorm, hRpos]
  -- ## The main identity: `ψ x = φ (x / R)`
  have hψ_eq : ∀ x, ψ x = (φ : EuclideanSpace ℝ (Fin d) → ℂ) (R⁻¹ • x) := by
    intro x
    have hinner_eq : ∀ η : EuclideanSpace ℝ (Fin d),
        ((∑ i, x i * η i : ℝ) : ℂ) = ((inner ℝ x η : ℝ) : ℂ) := by
      intro η
      congr 1
      rw [PiLp.inner_apply]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    -- step 1: rewrite the phase with the inner product
    have hψ1 : ψ x = ∫ η, Φ η *
        Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ x η : ℝ) : ℂ)) := by
      rw [show ψ x = ∫ η, Φ η *
        Complex.exp (2 * Real.pi * Complex.I * ((∑ i, x i * η i : ℝ) : ℂ)) from rfl]
      apply integral_congr_ae
      filter_upwards with η
      rw [hinner_eq η]
    -- step 2: expand `Φ` and pull out the constant
    have hψ2 : ψ x = ((R ^ d : ℝ) : ℂ) *
        ∫ η, (χ (R • η) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ x η : ℝ) : ℂ)) := by
      rw [hψ1]
      rw [show (fun η : EuclideanSpace ℝ (Fin d) => Φ η *
            Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ x η : ℝ) : ℂ)))
          = fun η : EuclideanSpace ℝ (Fin d) => ((R ^ d : ℝ) : ℂ) * ((χ (R • η) : ℂ) *
            Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ x η : ℝ) : ℂ))) by
        funext η
        rw [show Φ η = ((R ^ d : ℝ) : ℂ) * (χ (R • η) : ℂ) from rfl]
        ring]
      rw [integral_const_mul]
    -- change of variables: the rescaled integrand
    set g : EuclideanSpace ℝ (Fin d) → ℂ := fun u => (χ u : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ (R⁻¹ • x) u : ℝ) : ℂ)) with hg
    have hgcomp : ∀ η : EuclideanSpace ℝ (Fin d), g (R • η) = (χ (R • η) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ x η : ℝ) : ℂ)) := by
      intro η
      rw [hg]
      simp only
      have harg : inner ℝ (R⁻¹ • x) (R • η) = inner ℝ x η := by
        rw [real_inner_smul_left, real_inner_smul_right]
        field_simp
      rw [harg]
    have hcv : ∫ η, g (R • η) = (R ^ d)⁻¹ • ∫ u, g u := by
      have h := Measure.integral_comp_smul_of_nonneg (volume : Measure (EuclideanSpace ℝ (Fin d)))
        g R (hR := hRpos.le)
      rwa [finrank_euclideanSpace_fin] at h
    have hψ3 : ∫ η, (χ (R • η) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ x η : ℝ) : ℂ))
        = (R ^ d)⁻¹ • ∫ u, g u := by
      rw [← hcv]
      apply integral_congr_ae
      filter_upwards with η
      exact (hgcomp η).symm
    -- step 4: cancel the scaling
    have hψ4 : ψ x = ∫ u, g u := by
      rw [hψ2, hψ3, Complex.real_smul, Complex.ofReal_inv]
      rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (pow_ne_zero d hRne)),
        one_mul]
    -- step 5: identify with the inverse Fourier transform
    have hψ5 : ∫ u, g u = (φ : EuclideanSpace ℝ (Fin d) → ℂ) (R⁻¹ • x) := by
      rw [hφ_coe, Real.fourierInv_eq']
      apply integral_congr_ae
      filter_upwards with u
      rw [hg]
      have hχcu : χc u = (χ u : ℂ) := rfl
      rw [hχcu, smul_eq_mul]
      have harg : ((2 * Real.pi * inner ℝ u (R⁻¹ • x) : ℝ) : ℂ) * Complex.I
          = 2 * Real.pi * Complex.I * ((inner ℝ (R⁻¹ • x) u : ℝ) : ℂ) := by
        rw [(real_inner_comm u (R⁻¹ • x)).symm]
        push_cast
        ring
      rw [harg]
      ring
    rw [hψ4, hψ5]
  -- ## Lower bound on the ball of radius `R`
  have hψ_lb : ∀ x, ‖x‖ ≤ R → (1 / 2 : ℝ) ≤ ‖ψ x‖ := by
    intro x hx
    have hu : ‖R⁻¹ • x‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hRpos), inv_mul_eq_div]
      rw [div_le_iff₀ hRpos]
      linarith
    have hlow := half_integral_le_re_fourierInv hχ_nn hχ_int hχ_supp (R⁻¹ • x) hu
    rw [hχ_intval, mul_one] at hlow
    rw [hψ_eq x, hφ_coe]
    exact le_trans hlow (Complex.re_le_norm _)
  -- ## Decay
  obtain ⟨C, hCpos, hCdec⟩ :=
      Commons.Analysis.Distribution.schwartzMap_decay_one_add_norm φ (Nat.ceil A)
  have hψ_dec : ∀ x, ‖ψ x‖ ≤ C * (1 + ‖x‖ / R) ^ (-A) := by
    intro x
    have h1 : ‖(φ : EuclideanSpace ℝ (Fin d) → ℂ) (R⁻¹ • x)‖
        ≤ C * (1 + ‖R⁻¹ • x‖) ^ (-((Nat.ceil A : ℕ) : ℝ)) := hCdec (R⁻¹ • x)
    have h2 : ‖R⁻¹ • x‖ = ‖x‖ / R := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hRpos), inv_mul_eq_div]
    rw [h2] at h1
    rw [hψ_eq x]
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hCpos.le)
    apply Real.rpow_le_rpow_of_exponent_le
    · have h3 : 0 ≤ ‖x‖ / R := div_nonneg (norm_nonneg x) hRpos.le
      linarith
    · have h4 : A ≤ ((Nat.ceil A : ℕ) : ℝ) := Nat.le_ceil A
      linarith
  -- ## Assembly
  refine ⟨ψ, Φ, 1 / (8 * R), C, ?_, ?_, hCpos, hΦ_meas, hΦ_re, hΦ_int, hΦ_supp, ?_, hψ_lb, hψ_dec⟩
  · positivity
  · have h8 : (8 : ℝ) * R ≠ 0 := by positivity
    field_simp
    linarith [hRpos, hR]
  · intro x
    rfl

end Commons.Analysis.Fourier
