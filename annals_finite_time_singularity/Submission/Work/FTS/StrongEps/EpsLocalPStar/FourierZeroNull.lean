import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Real.Pi.Bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Fourier transform of a compactly supported `L¹` function is a.e. nonzero

If `ρ : ℝ → ℂ` is integrable, vanishes off `[-1, 1]` and has nonzero total mass `∫ ρ ≠ 0`,
then its Fourier transform `𝓕 ρ` does not vanish on a set of positive measure.

The proof is the classical one.  Since `ρ` is supported in the compact set `[-1, 1]`, the
parametric integral
`F z = ∫ a, exp ((-2πi a) * z) * ρ a`
is an entire function of `z : ℂ` (differentiation under the integral sign; the domination is
supplied by the compact support and `Integrable ρ`).  On the real line `F` restricts to `𝓕 ρ`,
and `F 0 = ∫ ρ ≠ 0`, so `F` is not identically zero.  By the identity theorem the zero set of
an analytic function on `ℂ` (or `ℝ`) is *discrete* (`AnalyticOnNhd.preimage_zero_mem_codiscrete`),
hence countable (a discrete subset of a Lindelöf space is countable,
`IsLindelof.countable_of_isDiscrete`), and a countable subset of `ℝ` has measure zero. -/

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology FourierTransform
open MeasureTheory Set Filter

/-- The frequency factor of the plane wave `a ↦ exp (epsK a * z)`. -/
private noncomputable def epsK (a : ℝ) : ℂ := (↑(-2 * Real.pi * a) : ℂ) * Complex.I

/-- The entire extension of the Fourier transform of `ρ`:
`fourierCont ρ z = ∫ a, exp ((-2πi a) z) ρ a`. -/
noncomputable def fourierCont (ρ : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ a : ℝ, Complex.exp (epsK a * z) * ρ a

private lemma continuous_epsK : Continuous epsK :=
  (Complex.continuous_ofReal.comp (by continuity)).mul continuous_const

private lemma continuous_exp_epsK (z : ℂ) : Continuous fun a : ℝ => Complex.exp (epsK a * z) :=
  Complex.continuous_exp.comp (continuous_epsK.mul continuous_const)

private lemma norm_epsK_mul_le (a : ℝ) (z : ℂ) : ‖epsK a * z‖ ≤ 2 * Real.pi * |a| * ‖z‖ := by
  refine (norm_mul_le _ _).trans ?_
  simp only [epsK, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_neg,
    abs_of_pos Real.pi_pos, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  ring_nf
  exact le_refl _

private lemma norm_epsK (a : ℝ) : ‖epsK a‖ = 2 * Real.pi * |a| := by
  simp only [epsK, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_neg,
    abs_of_pos Real.pi_pos, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]

/-- Domination of the plane wave on the unit ball of frequencies, using `|a| ≤ 1` on the
support of `ρ`. -/
private lemma norm_exp_epsK_le (a : ℝ) (z z₀ : ℂ) (ha : |a| ≤ 1) (hz : ‖z‖ ≤ ‖z₀‖ + 1) :
    ‖Complex.exp (epsK a * z)‖ ≤ Real.exp (2 * Real.pi * (‖z₀‖ + 1)) := by
  refine (Complex.norm_exp_le_exp_norm _).trans ?_
  apply Real.exp_le_exp.mpr
  refine (norm_epsK_mul_le a z).trans ?_
  calc 2 * Real.pi * |a| * ‖z‖ ≤ (2 * Real.pi * 1) * (‖z₀‖ + 1) := by
        apply mul_le_mul
        · apply mul_le_mul_of_nonneg_left ha (by positivity)
        · exact hz
        · positivity
        · positivity
    _ = 2 * Real.pi * (‖z₀‖ + 1) := by ring

private lemma norm_le_of_mem_ball (z₀ z : ℂ) (hz : z ∈ Metric.ball z₀ 1) :
    ‖z‖ ≤ ‖z₀‖ + 1 := by
  have hd : dist z z₀ < 1 := Metric.mem_ball.mp hz
  calc ‖z‖ = dist z 0 := by rw [dist_zero_right]
    _ ≤ dist z z₀ + dist z₀ 0 := dist_triangle z z₀ 0
    _ ≤ 1 + ‖z₀‖ := by rw [dist_zero_right]; linarith
    _ = ‖z₀‖ + 1 := by ring

/-- On the real line, the entire extension restricts to the Fourier transform. -/
lemma fourierCont_ofReal (ρ : ℝ → ℂ) (ξ : ℝ) : fourierCont ρ (ξ : ℂ) = 𝓕 ρ ξ := by
  rw [Real.fourier_eq']
  simp only [fourierCont, smul_eq_mul]
  congr 1
  ext a
  congr 1
  rw [Real.inner_apply, epsK]
  push_cast
  ring

/-- The value at the origin is the total mass. -/
lemma fourierCont_zero (ρ : ℝ → ℂ) : fourierCont ρ 0 = ∫ a, ρ a := by
  simp [fourierCont]

/-- `fourierCont ρ` is entire. -/
lemma fourierCont_differentiable {ρ : ℝ → ℂ} (h : Integrable ρ)
    (hs : ∀ x ∉ Set.Icc (-1 : ℝ) 1, ρ x = 0) : Differentiable ℂ (fourierCont ρ) := by
  have hsupp : ∀ a : ℝ, ρ a ≠ 0 → |a| ≤ 1 := by
    intro a ha
    by_contra hcon
    exact ha (hs a fun hmem => hcon (abs_le.mpr hmem))
  intro z₀
  set C : ℝ := 2 * Real.pi * Real.exp (2 * Real.pi * (‖z₀‖ + 1)) with hC
  have h2π : (1:ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hbnd_int : Integrable (fun a : ℝ => C * ‖ρ a‖) volume := h.norm.const_mul C
  have hmeas : ∀ᶠ z in 𝓝 z₀,
      AEStronglyMeasurable (fun a : ℝ => Complex.exp (epsK a * z) * ρ a) volume := by
    filter_upwards with z
    exact (continuous_exp_epsK z).aestronglyMeasurable.mul h.1
  have hint : Integrable (fun a : ℝ => Complex.exp (epsK a * z₀) * ρ a) volume := by
    apply Integrable.mono' hbnd_int
    · exact (continuous_exp_epsK z₀).aestronglyMeasurable.mul h.1
    · filter_upwards with a
      rcases eq_or_ne (ρ a) 0 with h0 | h0
      · simp [h0]
      · have he : ‖Complex.exp (epsK a * z₀)‖ ≤ Real.exp (2 * Real.pi * (‖z₀‖ + 1)) :=
          norm_exp_epsK_le a z₀ z₀ (hsupp a h0) (by linarith [norm_nonneg z₀])
        calc ‖Complex.exp (epsK a * z₀) * ρ a‖ = ‖Complex.exp (epsK a * z₀)‖ * ‖ρ a‖ :=
              norm_mul _ _
          _ ≤ Real.exp (2 * Real.pi * (‖z₀‖ + 1)) * ‖ρ a‖ := by gcongr
          _ ≤ C * ‖ρ a‖ := by
              rw [hC]
              gcongr
              exact le_mul_of_one_le_left (Real.exp_nonneg _) h2π
  have hF'meas : AEStronglyMeasurable
      (fun a : ℝ => (Complex.exp (epsK a * z₀) * epsK a) * ρ a) volume := by
    exact (((continuous_exp_epsK z₀).mul continuous_epsK).aestronglyMeasurable).mul h.1
  have hbnd : ∀ᵐ a ∂volume, ∀ z ∈ Metric.ball z₀ 1,
      ‖(Complex.exp (epsK a * z) * epsK a) * ρ a‖ ≤ C * ‖ρ a‖ := by
    filter_upwards with a z hz
    rcases eq_or_ne (ρ a) 0 with h0 | h0
    · simp [h0]
    · have ha1 : |a| ≤ 1 := hsupp a h0
      have hz1 : ‖z‖ ≤ ‖z₀‖ + 1 := norm_le_of_mem_ball z₀ z hz
      have he : ‖Complex.exp (epsK a * z)‖ ≤ Real.exp (2 * Real.pi * (‖z₀‖ + 1)) :=
        norm_exp_epsK_le a z z₀ ha1 hz1
      have hK : ‖epsK a‖ ≤ 2 * Real.pi := by
        rw [norm_epsK]
        nlinarith [Real.pi_pos, abs_nonneg a, ha1]
      calc ‖(Complex.exp (epsK a * z) * epsK a) * ρ a‖
          = ‖Complex.exp (epsK a * z)‖ * ‖epsK a‖ * ‖ρ a‖ := by rw [norm_mul, norm_mul]
        _ ≤ Real.exp (2 * Real.pi * (‖z₀‖ + 1)) * (2 * Real.pi) * ‖ρ a‖ := by gcongr
        _ = C * ‖ρ a‖ := by rw [hC]; ring_nf
  have hdiff : ∀ᵐ a ∂volume, ∀ z ∈ Metric.ball z₀ 1,
      HasDerivAt (fun x : ℂ => Complex.exp (epsK a * x) * ρ a)
        ((Complex.exp (epsK a * z) * epsK a) * ρ a) z := by
    filter_upwards with a z _
    exact ((hasDerivAt_const_mul (epsK a)).cexp).mul_const (ρ a)
  have key : Integrable (fun a : ℝ => (Complex.exp (epsK a * z₀) * epsK a) * ρ a) volume ∧
      HasDerivAt (fun z => ∫ a, Complex.exp (epsK a * z) * ρ a)
        (∫ a, (Complex.exp (epsK a * z₀) * epsK a) * ρ a) z₀ :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Metric.ball z₀ 1)
      (bound := fun a => C * ‖ρ a‖) (Metric.ball_mem_nhds z₀ one_pos)
      hmeas hint hF'meas hbnd hbnd_int hdiff
  change DifferentiableAt ℂ (fun z => ∫ a, Complex.exp (epsK a * z) * ρ a) z₀
  exact key.2.differentiableAt

theorem FourierZeroNull {ρ : ℝ → ℂ} (h : MeasureTheory.Integrable ρ)
    (hs : ∀ x ∉ Set.Icc (-1 : ℝ) 1, ρ x = 0) (h0 : (∫ x, ρ x) ≠ 0) :
    ∀ᵐ ξ ∂MeasureTheory.volume, 𝓕 ρ ξ ≠ 0 := by
  have hdiff : Differentiable ℂ (fourierCont ρ) := fourierCont_differentiable h hs
  have h0' : fourierCont ρ (0 : ℂ) ≠ 0 := by
    rw [fourierCont_zero]
    exact h0
  -- `ξ ↦ fourierCont ρ ↑ξ` is real analytic, being the restriction of an entire function
  have hanR : AnalyticOnNhd ℝ (fun ξ : ℝ => fourierCont ρ (ξ : ℂ)) Set.univ := by
    intro ξ _
    have h1 : AnalyticAt ℝ (fourierCont ρ) ((ξ : ℂ)) :=
      (hdiff.analyticAt (ξ : ℂ)).restrictScalars
    have h2 : AnalyticAt ℝ (fun y : ℝ => (y : ℂ)) ξ := Complex.ofRealCLM.analyticAt ξ
    simpa only [Function.comp_def] using h1.comp h2
  -- the zero set is closed and discrete, hence countable, hence null
  have hcod : (fun ξ : ℝ => fourierCont ρ (ξ : ℂ)) ⁻¹' {0}ᶜ ∈ Filter.codiscrete ℝ :=
    hanR.preimage_zero_mem_codiscrete h0'
  have hcl : IsClosed ((fun ξ : ℝ => fourierCont ρ (ξ : ℂ)) ⁻¹' {0}) :=
    (compl_mem_codiscrete_iff.mp hcod).1
  have hdisc : IsDiscrete ((fun ξ : ℝ => fourierCont ρ (ξ : ℂ)) ⁻¹' {0}) :=
    (compl_mem_codiscrete_iff.mp hcod).2
  have hcnt : ((fun ξ : ℝ => fourierCont ρ (ξ : ℂ)) ⁻¹' {0}).Countable :=
    IsLindelof.countable_of_isDiscrete (isLindelof_univ.of_isClosed_subset hcl (subset_univ _))
      hdisc
  rw [MeasureTheory.ae_iff]
  have hset : {ξ : ℝ | ¬ (𝓕 ρ ξ ≠ 0)} = (fun ξ : ℝ => fourierCont ρ (ξ : ℂ)) ⁻¹' {0} := by
    ext ξ
    simp [fourierCont_ofReal]
  rw [hset]
  exact hcnt.measure_zero volume

end Work.FTS.StrongEps.EpsLocalPStar
