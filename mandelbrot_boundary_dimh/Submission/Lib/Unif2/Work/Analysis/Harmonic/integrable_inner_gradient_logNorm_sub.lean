import Mathlib
import Submission.Lib.Unif2.Work.Analysis.Harmonic.integral_inner_gradient_eq_zero
import Submission.Lib.Unif2.Work.Drive.integral_inner_gradient_logNorm_eq
import Submission.Lib.Unif2.Work.Analysis.integrable_inv_norm_mul

/-!
# Integrability of the logarithmic-pole Dirichlet pairing

For a `C¹` compactly supported `ψ : ℂ → ℝ` the pairing `z ↦ ⟪∇(−log‖·−a‖)(z), ∇ψ(z)⟫` is
integrable.

The point is the size of the singularity: off `a`,
`∇(−log‖·−a‖)(z) = −(‖z − a‖²)⁻¹ • (z − a)` (`Work.Drive.gradient_neg_log_norm_sub`), whose norm is
exactly `‖z − a‖⁻¹`.  Since `∇ψ` is continuous with compact support, hence bounded, the integrand is
dominated by `C · ‖z − a‖⁻¹`, which is integrable in two dimensions
(`Work.Analysis.integrable_inv_norm_mul_of_hasCompactSupport`).  The passage to the actual integrand
uses that it agrees with the (Borel measurable) expression `z ↦ ⟪−(‖z − a‖²)⁻¹ • (z − a), ∇ψ(z)⟫`
away from the null set `{a}`.
-/

open MeasureTheory

namespace Work.Analysis.Harmonic

/-- The gradient of `−log‖·−a‖` has norm `‖z − a‖⁻¹` wherever it exists, i.e. away from `a`; the
formula `−(‖z − a‖²)⁻¹ • (z − a)` also makes sense at `a` and has norm `(0)⁻¹ = 0` there. -/
lemma norm_smul_inv_sq_sub (a z : ℂ) :
    ‖(-(‖z - a‖ ^ 2)⁻¹ : ℝ) • (z - a)‖ = (‖z - a‖)⁻¹ := by
  rw [norm_smul, norm_neg, Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
  rcases eq_or_ne ‖z - a‖ 0 with h | h
  · rw [h]; simp
  · rw [← inv_pow, pow_two, mul_assoc, inv_mul_cancel₀ h, mul_one]

theorem integrable_inner_gradient_logNorm_sub {ψ : ℂ → ℝ} {a : ℂ} (hψ : ContDiff ℝ 1 ψ)
    (hψc : HasCompactSupport ψ) :
    MeasureTheory.Integrable (fun z : ℂ =>
      inner (𝕜 := ℝ) (gradient (fun y : ℂ => -Real.log ‖y - a‖) z) (gradient ψ z))
      MeasureTheory.volume := by
  -- `∇ψ` is continuous and compactly supported
  have hgcont : Continuous (gradient ψ) := by
    have h1 : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv (by norm_num)
    have h2 : Continuous fun z : ℂ => (InnerProductSpace.toDual ℝ ℂ).symm (fderiv ℝ ψ z) :=
      (InnerProductSpace.toDual ℝ ℂ).symm.continuous.comp h1
    exact h2
  have hgcs : HasCompactSupport (gradient ψ) :=
    IsCompact.of_isClosed_subset hψc (isClosed_tsupport _)
      (Work.Analysis.Harmonic.tsupport_gradient_subset ψ)
  -- measurability of the explicit representative of the integrand
  have hmeas : Measurable
      (fun z : ℂ => inner (𝕜 := ℝ) (-(‖z - a‖ ^ 2)⁻¹ • (z - a)) (gradient ψ z)) := by
    refine Measurable.inner ?_ hgcont.measurable
    have h1 : Measurable (fun z : ℂ => ((‖z - a‖ : ℝ) ^ 2)⁻¹) :=
      ((continuous_norm.comp (continuous_id.sub continuous_const)).pow 2).measurable.inv
    have h2 : Measurable (fun z : ℂ => z - a) :=
      (continuous_id.sub continuous_const).measurable
    exact h1.neg.smul h2
  -- the dominating `L¹` function
  have hmaj : MeasureTheory.Integrable (fun z : ℂ => (‖z - a‖)⁻¹ * ‖gradient ψ z‖) :=
    Work.Analysis.integrable_inv_norm_mul_of_hasCompactSupport a (fun z => ‖gradient ψ z‖)
      hgcont.norm hgcs.norm
  -- pointwise domination
  have hbound : ∀ z : ℂ, ‖inner (𝕜 := ℝ) (-(‖z - a‖ ^ 2)⁻¹ • (z - a)) (gradient ψ z)‖
      ≤ (‖z - a‖)⁻¹ * ‖gradient ψ z‖ := by
    intro z
    calc ‖inner (𝕜 := ℝ) (-(‖z - a‖ ^ 2)⁻¹ • (z - a)) (gradient ψ z)‖
        ≤ ‖(-(‖z - a‖ ^ 2)⁻¹ : ℝ) • (z - a)‖ * ‖gradient ψ z‖ := norm_inner_le_norm _ _
      _ = (‖z - a‖)⁻¹ * ‖gradient ψ z‖ := by rw [norm_smul_inv_sq_sub]
  -- the actual integrand agrees with the explicit representative off the null set `{a}`
  have hae : (fun z : ℂ => inner (𝕜 := ℝ) (gradient (fun y : ℂ => -Real.log ‖y - a‖) z)
        (gradient ψ z))
      =ᵐ[MeasureTheory.volume]
      fun z : ℂ => inner (𝕜 := ℝ) (-(‖z - a‖ ^ 2)⁻¹ • (z - a)) (gradient ψ z) := by
    filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr (MeasureTheory.measure_singleton a)] with z hz
    have hz' : z ≠ a := by simpa using hz
    rw [Work.Drive.gradient_neg_log_norm_sub hz']
  have hint : MeasureTheory.Integrable
      (fun z : ℂ => inner (𝕜 := ℝ) (-(‖z - a‖ ^ 2)⁻¹ • (z - a)) (gradient ψ z)) :=
    hmaj.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  exact hint.congr hae.symm

end Work.Analysis.Harmonic
