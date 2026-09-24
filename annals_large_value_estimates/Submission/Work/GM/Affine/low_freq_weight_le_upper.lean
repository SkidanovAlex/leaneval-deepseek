import Mathlib
import Submission.Work.GM.Affine.low_freq_defs

/-!
# The low-frequency triangle weight is bounded by the low-frequency mass

For `T ≥ 1` and `f` continuous with compact support, the triangle-kernel weight
`θ(ξ) = tri (ξ/(T/3))` is nonnegative, is at most `1`, and vanishes as soon as
`|ξ| ≥ T/3`.  Since `T/3 < T/2`, the weighted frequency integral of `‖Fhat f‖²` is
therefore dominated by the unweighted integral over `(-T/2, T/2]`:

  `∫ ξ, tri (ξ/(T/3)) * ‖Fhat f ξ‖² ≤ ∫ ξ in Set.Ioc (-(T/2)) (T/2), ‖Fhat f ξ‖²`.

This is the first step in the proof of the §9 local-mass lower bound
(`Work.GM.Affine.low_freq_ge_local_mass`): it replaces the weighted frequency integral
produced by the weighted Plancherel identity by the low-frequency mass.
-/

open Complex MeasureTheory Set
open scoped ENNReal FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- The triangle kernel is nonnegative. -/
private lemma tri_weight_nonneg (x : ℝ) : 0 ≤ Commons.Analysis.Fourier.tri x := by
  unfold Commons.Analysis.Fourier.tri
  exact le_max_right _ _

/-- The triangle kernel is at most `1`. -/
private lemma tri_weight_le_one (x : ℝ) : Commons.Analysis.Fourier.tri x ≤ 1 := by
  unfold Commons.Analysis.Fourier.tri
  exact max_le (by linarith [abs_nonneg x]) zero_le_one

theorem low_freq_weight_le_upper {T : ℝ} (hT : 1 ≤ T) {f : ℝ → ℝ}
    (hf : Continuous f) (hcs : HasCompactSupport f) :
    ∫ ξ : ℝ, (Commons.Analysis.Fourier.tri (ξ / (T / 3)) * ‖Fhat f ξ‖ ^ 2)
      ≤ ∫ ξ in Set.Ioc (-(T / 2)) (T / 2), ‖Fhat f ξ‖ ^ 2 := by
  have hTpos : (0 : ℝ) < T := by linarith
  have hT3pos : (0 : ℝ) < T / 3 := by linarith
  set s : Set ℝ := Set.Ioc (-(T / 2)) (T / 2) with hsdef
  have hsmeas : MeasurableSet s := measurableSet_Ioc
  -- `Fhat f` is continuous (Fourier transform of an `L¹` function).
  have hFcont : Continuous (Fhat f) := by
    unfold Fhat
    have hint : Integrable (fun u : ℝ => ((f u : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.comp hf).integrable_of_hasCompactSupport
        (hcs.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp))
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hint
  have hhcont : Continuous (fun ξ : ℝ => ‖Fhat f ξ‖ ^ 2) := by fun_prop
  have hgcont : Continuous
      (fun ξ : ℝ => Commons.Analysis.Fourier.tri (ξ / (T / 3)) * ‖Fhat f ξ‖ ^ 2) :=
    (Commons.Analysis.Fourier.tri_continuous.comp
      (continuous_id.div_const (T / 3))).mul hhcont
  -- Pointwise comparison: the weight is `≤ 1` inside `s` and `0` outside `s`.
  have hpt : ∀ ξ : ℝ,
      ENNReal.ofReal (Commons.Analysis.Fourier.tri (ξ / (T / 3)) * ‖Fhat f ξ‖ ^ 2)
        ≤ s.indicator (fun ξ => ENNReal.ofReal (‖Fhat f ξ‖ ^ 2)) ξ := by
    intro ξ
    by_cases hξ : ξ ∈ s
    · rw [Set.indicator_of_mem hξ]
      refine ENNReal.ofReal_le_ofReal ?_
      calc Commons.Analysis.Fourier.tri (ξ / (T / 3)) * ‖Fhat f ξ‖ ^ 2
          ≤ 1 * ‖Fhat f ξ‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (tri_weight_le_one _) (sq_nonneg _)
        _ = ‖Fhat f ξ‖ ^ 2 := one_mul _
    · rw [Set.indicator_of_notMem hξ]
      have hz : Commons.Analysis.Fourier.tri (ξ / (T / 3)) = 0 := by
        apply Commons.Analysis.Fourier.tri_eq_zero_of_one_le_abs
        rw [abs_div, abs_of_pos hT3pos, le_div_iff₀ hT3pos]
        have hcase : ξ ≤ -(T / 2) ∨ T / 2 < ξ := by
          by_contra h
          rw [not_or] at h
          exact hξ ⟨lt_of_not_ge h.1, le_of_not_gt h.2⟩
        have habs : T / 2 ≤ |ξ| := by
          rcases hcase with h | h
          · rw [abs_of_nonpos (by linarith)]; linarith
          · rw [abs_of_pos (by linarith)]; linarith
        linarith
      rw [hz, zero_mul, ENNReal.ofReal_zero]
  -- Pass both integrals to their `ℝ≥0∞`-valued counterparts.
  have hL : ∫ ξ : ℝ, (Commons.Analysis.Fourier.tri (ξ / (T / 3)) * ‖Fhat f ξ‖ ^ 2)
      = (∫⁻ ξ : ℝ,
          ENNReal.ofReal (Commons.Analysis.Fourier.tri (ξ / (T / 3)) * ‖Fhat f ξ‖ ^ 2)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (μ := volume)
      (Filter.Eventually.of_forall (fun ξ : ℝ => mul_nonneg (tri_weight_nonneg _) (sq_nonneg _)))
      hgcont.aestronglyMeasurable
  have hR : (∫ ξ in s, ‖Fhat f ξ‖ ^ 2)
      = (∫⁻ ξ in s, ENNReal.ofReal (‖Fhat f ξ‖ ^ 2)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (μ := volume.restrict s)
      (Filter.Eventually.of_forall (fun ξ : ℝ => sq_nonneg _))
      (hhcont.aestronglyMeasurable.restrict)
  -- Monotonicity of the `ℝ≥0∞`-valued integral, via the indicator.
  have hmono : (∫⁻ ξ,
        ENNReal.ofReal (Commons.Analysis.Fourier.tri (ξ / (T / 3)) * ‖Fhat f ξ‖ ^ 2))
      ≤ ∫⁻ ξ in s, ENNReal.ofReal (‖Fhat f ξ‖ ^ 2) := by
    calc (∫⁻ ξ,
            ENNReal.ofReal (Commons.Analysis.Fourier.tri (ξ / (T / 3)) * ‖Fhat f ξ‖ ^ 2))
        ≤ ∫⁻ ξ, s.indicator (fun ξ => ENNReal.ofReal (‖Fhat f ξ‖ ^ 2)) ξ :=
          MeasureTheory.lintegral_mono hpt
      _ = ∫⁻ ξ in s, ENNReal.ofReal (‖Fhat f ξ‖ ^ 2) :=
          MeasureTheory.lintegral_indicator hsmeas _
  -- `s` has finite measure and `‖Fhat f‖` is bounded, so the right-hand side is finite.
  have hsfin : volume s < ⊤ := by
    rw [hsdef, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  have hbound : ∀ ξ : ℝ, ‖Fhat f ξ‖ ≤ ∫ u, ‖((f u : ℝ) : ℂ)‖ := by
    intro ξ
    unfold Fhat
    rw [Real.fourier_eq]
    calc ‖∫ v, 𝐞 (-inner ℝ v ξ) • ((f v : ℝ) : ℂ)‖
        ≤ ∫ v, ‖𝐞 (-inner ℝ v ξ) • ((f v : ℝ) : ℂ)‖ :=
          MeasureTheory.norm_integral_le_integral_norm _
      _ = ∫ v, ‖((f v : ℝ) : ℂ)‖ := by simp_rw [Circle.norm_smul]
  have hIntOn : Integrable (fun ξ : ℝ => ‖Fhat f ξ‖ ^ 2) (volume.restrict s) := by
    refine MeasureTheory.IntegrableOn.of_bound hsfin (hhcont.aestronglyMeasurable.restrict)
      ((∫ u, ‖((f u : ℝ) : ℂ)‖) ^ 2) ?_
    filter_upwards with ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hbound ξ) 2
  have hfin : (∫⁻ ξ in s, ENNReal.ofReal (‖Fhat f ξ‖ ^ 2)) ≠ ⊤ := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (μ := volume.restrict s) hIntOn
      (Filter.Eventually.of_forall (fun ξ : ℝ => sq_nonneg _))]
    exact ENNReal.ofReal_ne_top
  rw [hL, hR]
  exact ENNReal.toReal_mono hfin hmono

end

end Work.GM.Affine
