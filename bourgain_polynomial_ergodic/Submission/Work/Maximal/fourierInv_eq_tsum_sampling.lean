/-
# Sampling identity for band-limited amplitudes, from the Poisson hypothesis

For `0 < c0 < 1/2`, a Schwartz window `ψ` whose lattice translates satisfy the Poisson
(partition-of-unity) identity
`∑_m ψ (x - m) e^{2πi ξ m} = e^{2πi ξ x}`   for `|ξ| ≤ c0`,
and an integrable amplitude `F` vanishing (a.e.) off the band `[-c0, c0]`, the band-limited
function `𝓕⁻F` is reproduced from its lattice samples:

`𝓕⁻F y = ∑'_m ψ (y - m) · 𝓕⁻F m`   for every `y`.

The proof is a Fubini computation on the amplitude side.  Writing
`charP t ξ = e^{2πi ξ t}`, the Poisson hypothesis gives, for a.e. `ξ`,
`charP y ξ * F ξ = ∑'_m F ξ * (ψ (y - m) * charP m ξ)`
(the identity is used on the band, and both sides vanish off it, where `F = 0` a.e.).
The lattice series is absolutely summable against `F`: its `L¹`-norms are
`(∫ ‖F‖) · ‖ψ (y - m)‖`, summable by Schwartz decay, and
`MeasureTheory.integral_tsum_of_summable_integral_norm` interchanges
`∫` and `∑'`.  Each inner integral is
`ψ (y - m) · ∫ ξ, charP m ξ * F ξ = ψ (y - m) · 𝓕⁻F m`.
-/

import Mathlib
import Submission.Commons.Analysis.Fourier.band_limited_reproducing_kernel
import Submission.Commons.Analysis.Fourier.finset_bracket_lattice_le

open MeasureTheory
open scoped ENNReal FourierTransform

namespace Work.Maximal

noncomputable section

/-- The phase `t ↦ e^{2πi ξ t}`, in the exact shape in which both the Poisson hypothesis and
`Real.fourierInv_eq'` present it. -/
private def charP (t ξ : ℝ) : ℂ := Complex.exp (↑(2 * Real.pi * ξ * t) * Complex.I)

private lemma norm_charP (t ξ : ℝ) : ‖charP t ξ‖ = 1 := by
  rw [charP]
  exact Complex.norm_exp_ofReal_mul_I _

private lemma continuous_charP (t : ℝ) : Continuous (fun ξ : ℝ => charP t ξ) := by
  unfold charP
  fun_prop

/-- `𝓕⁻f` as the explicit integral against the phase `charP`. -/
private lemma fourierInv_eq_charP (f : ℝ → ℂ) (y : ℝ) :
    FourierTransformInv.fourierInv f y = ∫ ξ : ℝ, charP y ξ * f ξ := by
  rw [Real.fourierInv_eq']
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [Real.inner_apply, smul_eq_mul]
  congr 1
  rw [charP]
  congr 1
  push_cast
  ring

/-- The shifted lattice weight `∑_m (1 + (m - t)²)⁻¹` converges. -/
private lemma summable_inv_one_add_sq_sub (t : ℝ) :
    Summable (fun m : ℤ => (1 + ((m : ℝ) - t) ^ 2)⁻¹) := by
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
    ((Commons.Analysis.Fourier.summable_one_add_sq_int).mul_left (2 * (1 + t ^ 2)))
  have hkey : 1 + (m : ℝ) ^ 2 ≤ (2 * (1 + t ^ 2)) * (1 + ((m : ℝ) - t) ^ 2) := by
    nlinarith [sq_nonneg ((m : ℝ) - 2 * t), sq_nonneg t]
  rw [show (2 * (1 + t ^ 2)) * (1 + (m : ℝ) ^ 2)⁻¹
      = ((1 + (m : ℝ) ^ 2) / (2 * (1 + t ^ 2)))⁻¹ by rw [inv_div, div_eq_mul_inv]]
  rw [inv_le_inv₀ (by positivity) (by positivity), div_le_iff₀ (by positivity)]
  nlinarith [hkey]

/-- The lattice norms `m ↦ ‖ψ (y - m)‖` of a Schwartz function are summable. -/
private lemma summable_norm_schwartz_lattice (ψ : SchwartzMap ℝ ℂ) (y : ℝ) :
    Summable (fun m : ℤ => ‖ψ (y - (m : ℝ))‖) := by
  obtain ⟨C, hCpos, hC⟩ := Commons.Analysis.Fourier.schwartzMap_decay_one_add_sq ψ
  refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_)
    ((summable_inv_one_add_sq_sub y).mul_left C)
  have h := hC (y - (m : ℝ))
  rw [div_eq_mul_inv] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ hCpos.le)
  rw [inv_le_inv₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg (y - (m : ℝ)), sq_nonneg ((m : ℝ) - y)]

theorem fourierInv_eq_tsum_sampling
    {c0 : ℝ} (hc0 : 0 < c0) (hc01 : c0 < 1 / 2) (ψ : SchwartzMap ℝ ℂ)
    (hpoisson : ∀ ξ ∈ Set.Icc (-c0) c0, ∀ x : ℝ,
      tsum (fun m : ℤ => ψ (x - (m : ℝ)) * Complex.exp (↑(2 * Real.pi * ξ * (m : ℝ)) * Complex.I))
        = Complex.exp (↑(2 * Real.pi * ξ * x) * Complex.I))
    {F : ℝ → ℂ} (hF : MeasureTheory.Integrable F)
    (hFs : ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), ξ ∉ Set.Icc (-c0) c0 → F ξ = 0) :
    ∀ y : ℝ, FourierTransformInv.fourierInv F y
      = tsum (fun m : ℤ => ψ (y - (m : ℝ)) * FourierTransformInv.fourierInv F (m : ℝ)) := by
  intro y
  -- the Poisson hypothesis, in the `charP` shape
  have hpoisson' : ∀ ξ ∈ Set.Icc (-c0) c0, ∀ x : ℝ,
      tsum (fun m : ℤ => ψ (x - (m : ℝ)) * charP (m : ℝ) ξ) = charP x ξ := by
    intro ξ hξ x
    simpa only [charP] using hpoisson ξ hξ x
  -- summability of the lattice values of `ψ`
  have hsum_norm : Summable (fun m : ℤ => ‖ψ (y - (m : ℝ))‖) :=
    summable_norm_schwartz_lattice ψ y
  -- (1) the pointwise identity, a.e. in the frequency variable
  have hpt_ae : ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      charP y ξ * F ξ
        = ∑' m : ℤ, F ξ * (ψ (y - (m : ℝ)) * charP (m : ℝ) ξ) := by
    filter_upwards [hFs] with ξ hF0
    by_cases hξ : ξ ∈ Set.Icc (-c0) c0
    · rw [mul_comm (charP y ξ) (F ξ), ← hpoisson' ξ hξ y, tsum_mul_left]
    · rw [hF0 hξ]
      simp
  have hstep : (∫ ξ : ℝ, charP y ξ * F ξ)
      = ∫ ξ : ℝ, ∑' m : ℤ, F ξ * (ψ (y - (m : ℝ)) * charP (m : ℝ) ξ) :=
    integral_congr_ae hpt_ae
  -- (2) integrability of the summands and summability of their `L¹`-norms
  have hInt : ∀ m : ℤ, Integrable (fun ξ : ℝ => F ξ * (ψ (y - (m : ℝ)) * charP (m : ℝ) ξ)) := by
    intro m
    have hcont : Continuous (fun ξ : ℝ => ψ (y - (m : ℝ)) * charP (m : ℝ) ξ) :=
      continuous_const.mul (continuous_charP _)
    refine hF.mul_bdd hcont.aestronglyMeasurable (c := ‖ψ (y - (m : ℝ))‖)
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [norm_mul, norm_charP, mul_one]
  have hSum : Summable (fun m : ℤ => ∫ ξ : ℝ, ‖F ξ * (ψ (y - (m : ℝ)) * charP (m : ℝ) ξ)‖) := by
    have heq : ∀ m : ℤ, (∫ ξ : ℝ, ‖F ξ * (ψ (y - (m : ℝ)) * charP (m : ℝ) ξ)‖)
        = (∫ ξ : ℝ, ‖F ξ‖) * ‖ψ (y - (m : ℝ))‖ := by
      intro m
      have hpt : ∀ ξ : ℝ, ‖F ξ * (ψ (y - (m : ℝ)) * charP (m : ℝ) ξ)‖
          = ‖F ξ‖ * ‖ψ (y - (m : ℝ))‖ := by
        intro ξ
        rw [norm_mul, norm_mul, norm_charP, mul_one]
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_mul_const]
    exact (hsum_norm.mul_left (∫ ξ : ℝ, ‖F ξ‖)).congr (fun m => (heq m).symm)
  -- (3) assemble
  calc FourierTransformInv.fourierInv F y
      = ∫ ξ : ℝ, charP y ξ * F ξ := fourierInv_eq_charP F y
    _ = ∫ ξ : ℝ, ∑' m : ℤ, F ξ * (ψ (y - (m : ℝ)) * charP (m : ℝ) ξ) := hstep
    _ = ∑' m : ℤ, ∫ ξ : ℝ, F ξ * (ψ (y - (m : ℝ)) * charP (m : ℝ) ξ) :=
        (integral_tsum_of_summable_integral_norm hInt hSum).symm
    _ = ∑' m : ℤ, ψ (y - (m : ℝ)) * FourierTransformInv.fourierInv F (m : ℝ) := by
        apply tsum_congr
        intro m
        rw [fourierInv_eq_charP F (m : ℝ), ← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with ξ
        ring

end

end Work.Maximal
