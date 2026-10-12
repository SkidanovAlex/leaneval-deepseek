import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB3.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixB3/CS/highSlot_bound_of_pos`

Uniform boundedness on the box of the high-momentum part
`highSlot fc κ ℓ j Ψ = Ψ − lowSlot fc κ ℓ j Ψ` of a continuous `n`-body state.

`lowMult fc κ ℓ ψ y` is the free-space Fourier multiplier
`(2π)⁻³ ∫_p e^{i⟪p,y⟫} f(‖p‖/κ) FT(1_{Λ}ψ)(p) dp`; for `κ > 0` the symbol
`f(‖p‖/κ)` is supported in `‖p‖ ≤ 2κ` (`LowCut.zero`), so the integral is
dominated by `(2π)⁻³ · ‖1_Λψ‖_{L¹} · |B(0,2κ)|`, while the `L¹`-mass of the
box-localised fibre `1_Λψ` is at most `M ℓ³` whenever `|ψ| ≤ M` on `Λ`.
Combined with the boundedness of `Ψ` on the compact box this gives the claim.

## Main results

* `integral_indicator_norm_le` — `∫ ‖1_{Λ(ℓ)}ψ‖ ≤ M ℓ³` if `|ψ| ≤ M` on `Λ(ℓ)`;
* `kinFT_indicator_norm_le` — `‖kinFT (1_{Λ(ℓ)}ψ) p‖ ≤ M ℓ³`;
* `lowMult_abs_le_bound` — `|lowMult fc κ ℓ ψ y| ≤ (2π)⁻³ (Mℓ³) |B(0,2κ)|` for
  `κ > 0`;
* `highSlot_bound_of_pos` — the target.
-/

noncomputable section

open MeasureTheory Filter Metric
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseFixB3.CS

set_option linter.unusedVariables false

open Work.BoseBoxFix

/-! ## 1. The range of the cut-off function -/

private lemma lowCut_nonneg (fc : LowCut) (s : ℝ) : 0 ≤ fc.f s := by
  by_cases hs : s ≤ 2
  · have h := fc.anti hs
    rwa [fc.zero 2 le_rfl] at h
  · rw [fc.zero s (le_of_not_ge hs)]

private lemma lowCut_le_one (fc : LowCut) (s : ℝ) : fc.f s ≤ 1 := by
  by_cases hs : s ≤ 1
  · rw [fc.one s hs]
  · have h := fc.anti (le_of_not_ge hs)
    rwa [fc.one 1 le_rfl] at h

private lemma lowCut_abs_le_one (fc : LowCut) (s : ℝ) : |fc.f s| ≤ 1 := by
  rw [abs_le]
  exact ⟨by linarith [lowCut_nonneg fc s], lowCut_le_one fc s⟩

/-! ## 2. The `L¹`-mass of the box-localised fibre -/

private lemma integral_indicator_norm_le {ℓ M : ℝ} (hℓ : 0 ≤ ℓ) (hM : 0 ≤ M)
    {ψ : ℝ³ → ℝ} (hψ : ∀ z ∈ Submission.BoseGases.acube ℓ, |ψ z| ≤ M) :
    ∫ z, ‖(((Submission.BoseGases.acube ℓ).indicator ψ z : ℝ) : ℂ)‖ ≤ M * ℓ ^ 3 := by
  have hpt : ∀ z : ℝ³, ‖(((Submission.BoseGases.acube ℓ).indicator ψ z : ℝ) : ℂ)‖
      ≤ (Submission.BoseGases.acube ℓ).indicator (fun _ => M) z := by
    intro z
    by_cases hz : z ∈ Submission.BoseGases.acube ℓ
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
      simpa using hψ z hz
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
      simp
  have hint : Integrable (fun z : ℝ³ =>
      (Submission.BoseGases.acube ℓ).indicator (fun _ => M) z) volume := by
    rw [MeasureTheory.integrable_indicator_iff (Submission.BoseGases.acube_measurable ℓ)]
    refine MeasureTheory.IntegrableOn.of_bound (Submission.BoseGases.acube_lt_top ℓ hℓ)
      aestronglyMeasurable_const M ?_
    filter_upwards with z
    rw [Real.norm_of_nonneg hM]
  calc ∫ z, ‖(((Submission.BoseGases.acube ℓ).indicator ψ z : ℝ) : ℂ)‖
      ≤ ∫ z, (Submission.BoseGases.acube ℓ).indicator (fun _ => M) z :=
        MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun z => norm_nonneg _)
          hint (Eventually.of_forall hpt)
    _ = M * ℓ ^ 3 := by
        rw [MeasureTheory.integral_indicator_const M (Submission.BoseGases.acube_measurable ℓ),
          MeasureTheory.Measure.real_def, smul_eq_mul, Submission.BoseGases.acube_volume ℓ hℓ,
          ENNReal.toReal_ofReal (by positivity)]
        ring

/-- The Fourier transform of a box-localised bounded fibre is bounded by its
`L¹`-mass, hence by `M ℓ³`. -/
private lemma kinFT_indicator_norm_le {ℓ M : ℝ} (hℓ : 0 ≤ ℓ) (hM : 0 ≤ M)
    {ψ : ℝ³ → ℝ} (hψ : ∀ z ∈ Submission.BoseGases.acube ℓ, |ψ z| ≤ M) (p : ℝ³) :
    ‖Submission.BoseGases.kinFT
        (fun z : ℝ³ => (((Submission.BoseGases.acube ℓ).indicator ψ z : ℝ) : ℂ)) p‖
      ≤ M * ℓ ^ 3 := by
  have hnorm : ∀ y : ℝ³, ‖Complex.exp (-(Complex.I * (inner ℝ p y : ℂ)))‖ = 1 := by
    intro y
    have h : -(Complex.I * ((inner ℝ p y : ℝ) : ℂ))
        = (((-(inner ℝ p y)) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h, Complex.norm_exp_ofReal_mul_I]
  have h1 : ‖Submission.BoseGases.kinFT
      (fun z : ℝ³ => (((Submission.BoseGases.acube ℓ).indicator ψ z : ℝ) : ℂ)) p‖
      ≤ ∫ y, ‖(((Submission.BoseGases.acube ℓ).indicator ψ y : ℝ) : ℂ)‖ := by
    simp only [Submission.BoseGases.kinFT]
    refine le_trans (MeasureTheory.norm_integral_le_integral_norm (μ := volume)
      (fun y : ℝ³ => Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) *
        ((((Submission.BoseGases.acube ℓ).indicator ψ y : ℝ) : ℂ)))) ?_
    exact le_of_eq (MeasureTheory.integral_congr_ae (Eventually.of_forall fun y => by
      simp only [norm_mul, hnorm y, one_mul]))
  exact le_trans h1 (integral_indicator_norm_le hℓ hM hψ)

/-! ## 3. The `p`-integral bound for `lowMult` -/

private lemma lowMult_abs_le_bound {fc : LowCut} {κ ℓ : ℝ} (hκ : 0 < κ) (hℓ : 0 ≤ ℓ)
    {ψ : ℝ³ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hψ : ∀ z ∈ Submission.BoseGases.acube ℓ, |ψ z| ≤ M) (y : ℝ³) :
    |Work.BoseBoxFix.lowMult fc κ ℓ ψ y|
      ≤ ((2 * Real.pi) ^ 3)⁻¹ * (M * ℓ ^ 3)
          * (volume (Metric.closedBall (0 : ℝ³) (2 * κ))).toReal := by
  have hD0 : 0 ≤ M * ℓ ^ 3 := mul_nonneg hM (pow_nonneg hℓ 3)
  have hcinv : (0 : ℝ) ≤ ((2 * Real.pi) ^ 3)⁻¹ := by positivity
  set u : ℝ³ → ℂ := fun z => (((Submission.BoseGases.acube ℓ).indicator ψ z : ℝ) : ℂ) with hu
  set Z : ℂ := ∫ p : ℝ³, Complex.exp (Complex.I * (inner ℝ p y : ℂ)) *
      (((fc.f (‖p‖ / κ) : ℝ)) : ℂ) * Submission.BoseGases.kinFT u p with hZdef
  have hkin : ∀ p : ℝ³, ‖Submission.BoseGases.kinFT u p‖ ≤ M * ℓ ^ 3 := by
    intro p
    simpa only [hu] using kinFT_indicator_norm_le (ℓ := ℓ) (M := M) hℓ hM hψ p
  have hZn : ‖Z‖ ≤ (M * ℓ ^ 3) * (volume (Metric.closedBall (0 : ℝ³) (2 * κ))).toReal := by
    rw [hZdef]
    have hZ := MeasureTheory.norm_integral_le_integral_norm (μ := volume)
      (fun p : ℝ³ => Complex.exp (Complex.I * (inner ℝ p y : ℂ)) *
        (((fc.f (‖p‖ / κ) : ℝ)) : ℂ) * Submission.BoseGases.kinFT u p)
    have hpt : ∀ p : ℝ³, ‖Complex.exp (Complex.I * (inner ℝ p y : ℂ)) *
        (((fc.f (‖p‖ / κ) : ℝ)) : ℂ) * Submission.BoseGases.kinFT u p‖
        ≤ (Metric.closedBall (0 : ℝ³) (2 * κ)).indicator (fun _ => M * ℓ ^ 3) p := by
      intro p
      by_cases hp : p ∈ Metric.closedBall (0 : ℝ³) (2 * κ)
      · rw [Set.indicator_of_mem hp]
        have he : ‖Complex.exp (Complex.I * (inner ℝ p y : ℂ))‖ = 1 :=
          Complex.norm_exp_I_mul_ofReal _
        have hf : ‖(((fc.f (‖p‖ / κ) : ℝ)) : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact lowCut_abs_le_one fc _
        have hgp : ‖Complex.exp (Complex.I * (inner ℝ p y : ℂ)) *
            (((fc.f (‖p‖ / κ) : ℝ)) : ℂ) * Submission.BoseGases.kinFT u p‖
            = ‖(((fc.f (‖p‖ / κ) : ℝ)) : ℂ)‖ * ‖Submission.BoseGases.kinFT u p‖ := by
          rw [norm_mul, norm_mul, he, one_mul]
        rw [hgp]
        have h1 : ‖(((fc.f (‖p‖ / κ) : ℝ)) : ℂ)‖ * ‖Submission.BoseGases.kinFT u p‖
            ≤ 1 * (M * ℓ ^ 3) :=
          mul_le_mul hf (hkin p) (norm_nonneg _) (by norm_num)
        simpa using h1
      · rw [Set.indicator_of_notMem hp]
        have hlt : 2 * κ < ‖p‖ := by
          have h1 : ¬ (dist p (0 : ℝ³) ≤ 2 * κ) := fun h =>
            hp (by simpa [Metric.mem_closedBall] using h)
          have h2 := lt_of_not_ge h1
          rwa [dist_eq_norm, sub_zero] at h2
        have h2 : 2 < ‖p‖ / κ := by
          rw [lt_div_iff₀ hκ]
          exact hlt
        have hf0 : fc.f (‖p‖ / κ) = 0 := fc.zero _ h2.le
        simp only [hf0, Complex.ofReal_zero, mul_zero, zero_mul, norm_zero, le_refl]
    have hint : Integrable (fun p : ℝ³ =>
        (Metric.closedBall (0 : ℝ³) (2 * κ)).indicator (fun _ => M * ℓ ^ 3) p) volume := by
      rw [MeasureTheory.integrable_indicator_iff measurableSet_closedBall]
      refine MeasureTheory.IntegrableOn.of_bound
        (isCompact_closedBall (0 : ℝ³) (2 * κ)).measure_lt_top
        aestronglyMeasurable_const (M * ℓ ^ 3) ?_
      filter_upwards with p
      rw [Real.norm_of_nonneg hD0]
    have h2 : ∫ p, ‖Complex.exp (Complex.I * (inner ℝ p y : ℂ)) *
        (((fc.f (‖p‖ / κ) : ℝ)) : ℂ) * Submission.BoseGases.kinFT u p‖
        ≤ ∫ p, (Metric.closedBall (0 : ℝ³) (2 * κ)).indicator (fun _ => M * ℓ ^ 3) p :=
      MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun p => norm_nonneg _) hint
        (Eventually.of_forall hpt)
    have h3 : ∫ p, (Metric.closedBall (0 : ℝ³) (2 * κ)).indicator (fun _ => M * ℓ ^ 3) p
        = (M * ℓ ^ 3) * (volume (Metric.closedBall (0 : ℝ³) (2 * κ))).toReal := by
      rw [MeasureTheory.integral_indicator_const _ measurableSet_closedBall,
        MeasureTheory.Measure.real_def, smul_eq_mul]
      ring
    linarith [hZ, h2, h3]
  have hLM : Work.BoseBoxFix.lowMult fc κ ℓ ψ y
      = ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : ℝ³,
          Complex.exp (Complex.I * (inner ℝ p y : ℂ)) *
            (((fc.f (‖p‖ / κ) : ℝ)) : ℂ) * Submission.BoseGases.kinFT u p).re := by
    simp only [Work.BoseBoxFix.lowMult, hu, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
  have hLM' : Work.BoseBoxFix.lowMult fc κ ℓ ψ y = ((2 * Real.pi) ^ 3)⁻¹ * Z.re := by
    rw [hLM, hZdef]
  calc |Work.BoseBoxFix.lowMult fc κ ℓ ψ y|
      = ((2 * Real.pi) ^ 3)⁻¹ * |Z.re| := by rw [hLM', abs_mul, abs_of_nonneg hcinv]
    _ ≤ ((2 * Real.pi) ^ 3)⁻¹ * ‖Z‖ :=
        mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm Z) hcinv
    _ ≤ ((2 * Real.pi) ^ 3)⁻¹ * ((M * ℓ ^ 3)
          * (volume (Metric.closedBall (0 : ℝ³) (2 * κ))).toReal) :=
        mul_le_mul_of_nonneg_left hZn hcinv
    _ = ((2 * Real.pi) ^ 3)⁻¹ * (M * ℓ ^ 3)
          * (volume (Metric.closedBall (0 : ℝ³) (2 * κ))).toReal := by ring

/-! ## 4. The target -/

theorem highSlot_bound_of_pos {fc : Work.BoseBoxFix.LowCut} {κ ℓ : ℝ} (hκ : 0 < κ) (hℓ : 0 < ℓ)
    {n : ℕ} (j : Fin n) {Ψ : Submission.BoseGases.X n → ℝ} (hΨ : Continuous Ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Submission.BoseGases.abox n ℓ,
      |Work.BoseFixB3.highSlot fc κ ℓ j Ψ x| ≤ C := by
  obtain ⟨C₀, hC₀⟩ :=
    (Work.UBBInputs9.B.abox_isCompact n ℓ).exists_bound_of_continuousOn hΨ.continuousOn
  have hbound : ∀ x ∈ Submission.BoseGases.abox n ℓ, |Ψ x| ≤ max C₀ 0 := by
    intro x hx
    have h := hC₀ x hx
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)
  have hM : (0 : ℝ) ≤ max C₀ 0 := le_max_right _ _
  refine ⟨max C₀ 0 + ((2 * Real.pi) ^ 3)⁻¹ * (max C₀ 0 * ℓ ^ 3)
      * (volume (Metric.closedBall (0 : ℝ³) (2 * κ))).toReal, ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ ((2 * Real.pi) ^ 3)⁻¹ * (max C₀ 0 * ℓ ^ 3)
        * (volume (Metric.closedBall (0 : ℝ³) (2 * κ))).toReal :=
      mul_nonneg (mul_nonneg (by positivity) (mul_nonneg hM (pow_nonneg hℓ.le 3)))
        ENNReal.toReal_nonneg
    linarith
  · intro x hx
    have hfib : ∀ z ∈ Submission.BoseGases.acube ℓ,
        |Ψ (Function.update x j z)| ≤ max C₀ 0 := by
      intro z hz
      apply hbound
      intro i
      by_cases hi : i = j
      · rw [hi, Function.update_self]
        exact hz
      · rw [Function.update_of_ne hi]
        exact (Submission.BoseGases.mem_abox_iff n ℓ x).mp hx i
    have hLM := lowMult_abs_le_bound (fc := fc) hκ hℓ.le hM hfib (x j)
    have hlow : Work.BoseBoxFix.lowSlot fc κ ℓ j Ψ x
        = Work.BoseBoxFix.lowMult fc κ ℓ (fun z => Ψ (Function.update x j z)) (x j) := rfl
    calc |Work.BoseFixB3.highSlot fc κ ℓ j Ψ x|
        = |Ψ x - Work.BoseBoxFix.lowSlot fc κ ℓ j Ψ x| := by
          simp only [Work.BoseFixB3.highSlot]
      _ ≤ |Ψ x| + |Work.BoseBoxFix.lowSlot fc κ ℓ j Ψ x| := abs_sub _ _
      _ = |Ψ x| + |Work.BoseBoxFix.lowMult fc κ ℓ
            (fun z => Ψ (Function.update x j z)) (x j)| := by rw [hlow]
      _ ≤ max C₀ 0 + ((2 * Real.pi) ^ 3)⁻¹ * (max C₀ 0 * ℓ ^ 3)
            * (volume (Metric.closedBall (0 : ℝ³) (2 * κ))).toReal :=
          add_le_add (hbound x hx) hLM

end Work.BoseFixB3.CS
