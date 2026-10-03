import Mathlib
import Submission.Work.Fatou.Analysis.norm_sub_le_lintegral_speed
import Submission.Work.Fatou.Analysis.norm_deriv_circle_le

/-!
# A slice lower bound for a `C¹` map on a circle (Shishikura, length–area)

Let `g : ℂ → ℂ` be `C¹` and let `r ≥ 1`.  If two points `z₁`, `z₂` of the circle of radius `r`
have images under `g` at distance at least `d`, then

`d ^ 2 / (2 * π * r) ≤ ∫⁻ θ in [-π, π], r * ‖fderiv ℝ g (r * e^{iθ})‖ ^ 2`.

This is the "length–area" (arc-length + Cauchy–Schwarz) estimate used to rule out the upper
half-plane in the uniformization step of the construction of perturbed Fatou coordinates
(Shishikura, Prop. A.2.1); see `NOTES_LEAD_fatou.md` and `qcLiouville.lean`.

Proof sketch: write `zᵢ = r e^{i θᵢ}` with `θᵢ = arg zᵢ ∈ [-π, π]` and let `γ θ = g (r e^{iθ})`.
The fundamental theorem of calculus for `γ` gives `‖γ b - γ a‖ ≤ ∫_a^b ‖γ'‖`, and
`‖γ' θ‖ ≤ r ‖fderiv ℝ g (r e^{iθ})‖`, so `d ≤ ∫_a^b w` where `w θ = r ‖fderiv ℝ g (r e^{iθ})‖`
and `[a, b]` is the interval spanned by `θ₁, θ₂`.  Cauchy–Schwarz for `ℝ≥0∞`-valued integrals,
`(∫ w)² ≤ (2π) ∫ w²`, then yields the claim after inserting `w² = r (r ‖fderiv‖²)`.

The two measure-theoretic inputs (the arc-length estimate in `ℝ≥0∞` form and the chain-rule
bound for `‖γ'‖`) are proved in the sibling files imported above.
-/

namespace Work.Fatou.Analysis

open MeasureTheory Set Complex
open scoped ENNReal Topology

/-- **Cauchy–Schwarz** for `ℝ≥0∞`-valued integrals: `(∫⁻ f) ^ 2 ≤ μ univ * ∫⁻ f ^ 2`. -/
lemma sq_lintegral_le_measure_mul {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    (∫⁻ x, f x ∂μ) ^ (2 : ℝ) ≤ μ Set.univ * ∫⁻ x, f x ^ (2 : ℝ) ∂μ := by
  have hpq : (2 : ℝ).HolderConjugate (2 : ℝ) := by
    rw [Real.holderConjugate_iff]; norm_num
  have h1 : ∫⁻ x, f x ∂μ ≤
      (∫⁻ x, f x ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) * (μ Set.univ) ^ ((1 : ℝ) / 2) := by
    have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ := μ) (p := 2) (q := 2) hpq (f := f)
      (g := fun _ => (1 : ℝ≥0∞)) hf aemeasurable_const
    simpa only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_one] using hh
  have h2 := ENNReal.rpow_le_rpow h1 (by norm_num : (0 : ℝ) ≤ 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)] at h2
  rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at h2
  norm_num at h2
  simpa [mul_comm] using h2

/-- `ENNReal.ofReal d ≤ ‖x‖ₑ` whenever `d ≤ ‖x‖`. -/
lemma ofReal_le_enorm_of_le {x : ℂ} {d : ℝ} (h : d ≤ ‖x‖) : ENNReal.ofReal d ≤ ‖x‖ₑ := by
  simpa [enorm_eq_nnnorm] using ENNReal.ofReal_le_ofReal h

/-- The Cauchy–Schwarz finishing step: from `ofReal d ≤ ∫⁻ w` over `[-π, π]` and the identity
`w θ ^ 2 = r * (r * ‖fderiv θ‖ ^ 2)`, deduce
`ofReal (d ^ 2) ≤ ofReal (2 π r) * ∫⁻ r * ‖fderiv θ‖ ^ 2`. -/
lemma slice_core (g : ℂ → ℂ) (d r : ℝ) (hr0 : 0 ≤ r) (hd : 0 ≤ d)
    (hw_meas : Measurable
      (fun θ : ℝ => ENNReal.ofReal (r * ‖fderiv ℝ g (r * Complex.exp (θ * Complex.I))‖)))
    (hstep : ENNReal.ofReal d ≤ ∫⁻ θ in Set.Icc (-Real.pi) Real.pi,
        ENNReal.ofReal (r * ‖fderiv ℝ g (r * Complex.exp (θ * Complex.I))‖)) :
    ENNReal.ofReal (d ^ 2) ≤ ENNReal.ofReal (2 * Real.pi * r) *
      (∫⁻ θ in Set.Icc (-Real.pi) Real.pi,
        ENNReal.ofReal (r * ‖fderiv ℝ g (r * Complex.exp (θ * Complex.I))‖ ^ 2)) := by
  have hCS := sq_lintegral_le_measure_mul (volume.restrict (Set.Icc (-Real.pi) Real.pi))
    (f := fun θ : ℝ => ENNReal.ofReal (r * ‖fderiv ℝ g (r * Complex.exp (θ * Complex.I))‖))
    hw_meas.aemeasurable
  have hvol : (volume.restrict (Set.Icc (-Real.pi) Real.pi)) Set.univ
      = ENNReal.ofReal (2 * Real.pi) := by
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    congr 1
    ring
  rw [hvol] at hCS
  have hsq : Set.EqOn
      (fun θ : ℝ =>
        (ENNReal.ofReal (r * ‖fderiv ℝ g (r * Complex.exp (θ * Complex.I))‖)) ^ (2 : ℝ))
      (fun θ : ℝ => ENNReal.ofReal r *
        ENNReal.ofReal (r * ‖fderiv ℝ g (r * Complex.exp (θ * Complex.I))‖ ^ 2))
      (Set.Icc (-Real.pi) Real.pi) := by
    intro θ _
    dsimp only
    rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hr0 (norm_nonneg _))
      (by norm_num : (0 : ℝ) ≤ 2)]
    rw [Real.rpow_two]
    rw [show (r * ‖fderiv ℝ g (r * Complex.exp (θ * Complex.I))‖) ^ 2
        = r * (r * ‖fderiv ℝ g (r * Complex.exp (θ * Complex.I))‖ ^ 2) by ring]
    rw [ENNReal.ofReal_mul hr0]
  rw [setLIntegral_congr_fun measurableSet_Icc hsq] at hCS
  rw [lintegral_const_mul' (ENNReal.ofReal r) _ (ENNReal.ofReal_ne_top (r := r))] at hCS
  calc ENNReal.ofReal (d ^ 2)
      = (ENNReal.ofReal d) ^ (2 : ℝ) := by
        rw [← Real.rpow_two d,
          ← ENNReal.ofReal_rpow_of_nonneg hd (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ (∫⁻ θ in Set.Icc (-Real.pi) Real.pi,
          ENNReal.ofReal (r * ‖fderiv ℝ g (r * Complex.exp (θ * Complex.I))‖)) ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow hstep (by norm_num : (0 : ℝ) ≤ 2)
    _ ≤ ENNReal.ofReal (2 * Real.pi) *
          (ENNReal.ofReal r *
            ∫⁻ θ in Set.Icc (-Real.pi) Real.pi,
              ENNReal.ofReal (r * ‖fderiv ℝ g (r * Complex.exp (θ * Complex.I))‖ ^ 2)) := hCS
    _ = ENNReal.ofReal (2 * Real.pi * r) *
          (∫⁻ θ in Set.Icc (-Real.pi) Real.pi,
            ENNReal.ofReal (r * ‖fderiv ℝ g (r * Complex.exp (θ * Complex.I))‖ ^ 2)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]

theorem slice_lower_bound (g : ℂ → ℂ) (d r : ℝ) (hr : 1 ≤ r) (hd : 0 ≤ d)
    (hC1 : ContDiff ℝ 1 g)
    (hB : ∃ z₁ ∈ Metric.sphere (0:ℂ) r, ∃ z₂ ∈ Metric.sphere (0:ℂ) r, d ≤ dist (g z₁) (g z₂)) :
    ENNReal.ofReal (d ^ 2 / (2 * Real.pi * r)) ≤
      ∫⁻ θ in Set.Icc (-Real.pi) Real.pi,
        ENNReal.ofReal (r * ‖fderiv ℝ g (r * Complex.exp (θ * Complex.I))‖ ^ 2) := by
  obtain ⟨z₁, hz₁, z₂, hz₂, hdz⟩ := hB
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hrne : (2 * Real.pi * r) ≠ 0 := by positivity
  -- the sphere points and their arguments
  have hn₁ : ‖z₁‖ = r := by simpa [Metric.mem_sphere, dist_eq_norm] using hz₁
  have hn₂ : ‖z₂‖ = r := by simpa [Metric.mem_sphere, dist_eq_norm] using hz₂
  have hrep₁ : r * Complex.exp (z₁.arg * Complex.I) = z₁ := by
    have h := Complex.norm_mul_exp_arg_mul_I z₁
    rw [hn₁] at h; exact h
  have hrep₂ : r * Complex.exp (z₂.arg * Complex.I) = z₂ := by
    have h := Complex.norm_mul_exp_arg_mul_I z₂
    rw [hn₂] at h; exact h
  have harg₁ : z₁.arg ∈ Set.Icc (-Real.pi) Real.pi :=
    ⟨(Complex.arg_mem_Ioc z₁).1.le, (Complex.arg_mem_Ioc z₁).2⟩
  have harg₂ : z₂.arg ∈ Set.Icc (-Real.pi) Real.pi :=
    ⟨(Complex.arg_mem_Ioc z₂).1.le, (Complex.arg_mem_Ioc z₂).2⟩
  -- the density `w θ = r * ‖fderiv ℝ g (r e^{iθ})‖` is continuous, hence measurable
  have hc : Continuous (fun θ : ℝ => r * Complex.exp (θ * Complex.I)) :=
    continuous_const.mul (Complex.continuous_exp.comp
      (Complex.continuous_ofReal.mul continuous_const))
  have hw_cont : Continuous
      (fun θ : ℝ => r * ‖fderiv ℝ g (r * Complex.exp (θ * Complex.I))‖) :=
    continuous_const.mul (continuous_norm.comp
      ((hC1.continuous_fderiv one_ne_zero).comp hc))
  have hw_meas : Measurable
      (fun θ : ℝ => ENNReal.ofReal (r * ‖fderiv ℝ g (r * Complex.exp (θ * Complex.I))‖)) :=
    ENNReal.measurable_ofReal.comp hw_cont.measurable
  -- main estimate
  have key : ENNReal.ofReal (d ^ 2) ≤ ENNReal.ofReal (2 * Real.pi * r) *
      (∫⁻ θ in Set.Icc (-Real.pi) Real.pi,
        ENNReal.ofReal (r * ‖fderiv ℝ g (r * Complex.exp (θ * Complex.I))‖ ^ 2)) := by
    rcases le_total z₁.arg z₂.arg with hle | hle
    · -- θ₁ ≤ θ₂ : the interval spanned is `[θ₁, θ₂]` and `γ θ₂ - γ θ₁ = g z₂ - g z₁`
      have hdist : d ≤ ‖g z₂ - g z₁‖ := by simpa [dist_eq_norm, norm_sub_rev] using hdz
      have hchord : ‖g z₂ - g z₁‖ₑ ≤ ∫⁻ θ in Set.Icc z₁.arg z₂.arg,
          ENNReal.ofReal (r * ‖fderiv ℝ g (r * Complex.exp (θ * Complex.I))‖) := by
        have h := norm_sub_le_lintegral_speed g r z₁.arg z₂.arg hle hr0 hC1
        simpa only [hrep₁, hrep₂] using h
      have hsub : Set.Icc z₁.arg z₂.arg ⊆ Set.Icc (-Real.pi) Real.pi := fun x hx =>
        ⟨le_trans harg₁.1 hx.1, le_trans hx.2 harg₂.2⟩
      have hstep : ENNReal.ofReal d ≤ ∫⁻ θ in Set.Icc (-Real.pi) Real.pi,
          ENNReal.ofReal (r * ‖fderiv ℝ g (r * Complex.exp (θ * Complex.I))‖) :=
        (ofReal_le_enorm_of_le hdist).trans (hchord.trans (lintegral_mono_set hsub))
      exact slice_core g d r hr0 hd hw_meas hstep
    · -- θ₂ ≤ θ₁ : the interval spanned is `[θ₂, θ₁]` and `γ θ₁ - γ θ₂ = g z₁ - g z₂`
      have hdist : d ≤ ‖g z₁ - g z₂‖ := by simpa [dist_eq_norm] using hdz
      have hchord : ‖g z₁ - g z₂‖ₑ ≤ ∫⁻ θ in Set.Icc z₂.arg z₁.arg,
          ENNReal.ofReal (r * ‖fderiv ℝ g (r * Complex.exp (θ * Complex.I))‖) := by
        have h := norm_sub_le_lintegral_speed g r z₂.arg z₁.arg hle hr0 hC1
        simpa only [hrep₁, hrep₂] using h
      have hsub : Set.Icc z₂.arg z₁.arg ⊆ Set.Icc (-Real.pi) Real.pi := fun x hx =>
        ⟨le_trans harg₂.1 hx.1, le_trans hx.2 harg₁.2⟩
      have hstep : ENNReal.ofReal d ≤ ∫⁻ θ in Set.Icc (-Real.pi) Real.pi,
          ENNReal.ofReal (r * ‖fderiv ℝ g (r * Complex.exp (θ * Complex.I))‖) :=
        (ofReal_le_enorm_of_le hdist).trans (hchord.trans (lintegral_mono_set hsub))
      exact slice_core g d r hr0 hd hw_meas hstep
  -- divide by `2 π r`
  have hc0 : ENNReal.ofReal (2 * Real.pi * r) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    positivity
  refine (ENNReal.mul_le_mul_iff_left hc0 ENNReal.ofReal_ne_top).mp ?_
  calc ENNReal.ofReal (d ^ 2 / (2 * Real.pi * r)) * ENNReal.ofReal (2 * Real.pi * r)
      = ENNReal.ofReal ((d ^ 2 / (2 * Real.pi * r)) * (2 * Real.pi * r)) := by
        rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ d ^ 2 / (2 * Real.pi * r) by positivity)]
    _ = ENNReal.ofReal (d ^ 2) := by rw [div_mul_cancel₀ _ hrne]
    _ ≤ ENNReal.ofReal (2 * Real.pi * r) *
          (∫⁻ θ in Set.Icc (-Real.pi) Real.pi,
            ENNReal.ofReal (r * ‖fderiv ℝ g (r * Complex.exp (θ * Complex.I))‖ ^ 2)) := key
    _ = (∫⁻ θ in Set.Icc (-Real.pi) Real.pi,
            ENNReal.ofReal (r * ‖fderiv ℝ g (r * Complex.exp (θ * Complex.I))‖ ^ 2)) *
          ENNReal.ofReal (2 * Real.pi * r) := mul_comm _ _

end Work.Fatou.Analysis
