import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Submission.Work.BoseFixB3.Steps
import Submission.Work.BoseKinLoc.Momentum.memLp_kinFT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB3.Split

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal

/-! ## Two estimates behind `lowSlotBound`

`Work.BoseBoxFix.lowMult fc κ ℓ ψ y = (2π)⁻³ ∫_p Re(e^{i⟪p,y⟫} f(‖p‖/κ) (1_{acube ℓ}ψ)^(p))`
(`Submission/Work/BoseBoxFix/Defs.lean`), with `kinFT u p = ∫_z e^{−i⟪p,z⟫} u z`.

* `lowMult_abs_le`: for `κ > 0` the factor `f(‖p‖/κ)` is bounded by `1` and vanishes for
  `‖p‖ ≥ 2κ` (`LowCut.zero`), while `‖kinFT u p‖ ≤ ∫_z ‖u z‖ ≤ D`
  (`MeasureTheory.norm_integral_le_integral_norm`).  Hence the whole `p`-integral is dominated
  by `(2π)⁻³ D vol(B(0, 2κ))`.
* `integral_indicator_norm_le`: the `L¹`-mass of the box-localised fibre of a function bounded
  by `M` on `acube ℓ` is at most `M ℓ³` (`acube_volume`). -/

/-- **The multiplier bound.**  If the box-localised fibre `1_{acube ℓ}ψ` has `L¹`-mass at most
`D ≥ 0`, then `|lowMult fc κ ℓ ψ y|` is bounded by `(2π)⁻³ D` times the volume of the momentum
cutoff ball of radius `2κ` — uniformly in `y`. -/
lemma lowMult_abs_le {fc : Work.BoseBoxFix.LowCut} {κ ℓ D : ℝ} (hκ : 0 < κ)
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hD0 : 0 ≤ D)
    (hD : ∫ z, ‖(((Submission.BoseGases.acube ℓ).indicator ψ z : ℝ) : ℂ)‖ ≤ D)
    (y : EuclideanSpace ℝ (Fin 3)) :
    |Work.BoseBoxFix.lowMult fc κ ℓ ψ y|
      ≤ ((2 * π) ^ 3)⁻¹ * D
          * (MeasureTheory.volume
              (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (2 * κ))).toReal := by
  set c : ℝ := ((2 * π) ^ 3)⁻¹ with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  set u : EuclideanSpace ℝ (Fin 3) → ℂ :=
    fun z => (((Submission.BoseGases.acube ℓ).indicator ψ z : ℝ) : ℂ) with hu
  set F : EuclideanSpace ℝ (Fin 3) → ℂ := fun p =>
    Complex.exp (Complex.I * (inner ℝ p y : ℂ)) * ((fc.f (‖p‖ / κ) : ℝ) : ℂ)
      * Submission.BoseGases.kinFT u p with hF
  have hlow : Work.BoseBoxFix.lowMult fc κ ℓ ψ y
      = ((c : ℂ) * ∫ p : EuclideanSpace ℝ (Fin 3), F p).re := by
    rw [Work.BoseBoxFix.lowMult, ← hc, ← hu, ← hF]
  have hFp : ∀ p, F p = Complex.exp (Complex.I * (inner ℝ p y : ℂ))
      * ((fc.f (‖p‖ / κ) : ℝ) : ℂ) * Submission.BoseGases.kinFT u p := fun p => by rw [hF]
  have hunorm : (∫ z, ‖u z‖)
      = ∫ z, ‖(((Submission.BoseGases.acube ℓ).indicator ψ z : ℝ) : ℂ)‖ := by
    apply integral_congr_ae
    filter_upwards with z
    simp [hu]
  -- `‖kinFT u p‖ ≤ ∫_z ‖u z‖ ≤ D`
  have hkin : ∀ p, ‖Submission.BoseGases.kinFT u p‖ ≤ D := by
    intro p
    have hbase : ‖Submission.BoseGases.kinFT u p‖ ≤ ∫ z, ‖u z‖ := by
      refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) (le_of_eq ?_)
      apply integral_congr_ae
      filter_upwards with z
      rw [norm_mul,
        show -(Complex.I * (inner ℝ p z : ℂ)) = ((-(inner ℝ p z)) : ℂ) * Complex.I by ring,
        Complex.norm_exp,
        show (((-(inner ℝ p z)) : ℂ) * Complex.I).re = 0 by simp [Complex.mul_re],
        Real.exp_zero, one_mul]
    rw [hunorm] at hbase
    exact le_trans hbase hD
  -- `|f| ≤ 1` everywhere
  have habs : ∀ s : ℝ, |fc.f s| ≤ 1 := by
    intro s
    have h1 : fc.f s ≤ 1 := by
      rcases le_or_gt s 1 with h | h
      · rw [fc.one s h]
      · exact le_trans (fc.anti h.le) (le_of_eq (fc.one 1 le_rfl))
    have h0 : 0 ≤ fc.f s := by
      rcases le_or_gt 2 s with h | h
      · rw [fc.zero s h]
      · exact le_trans (le_of_eq (fc.zero 2 le_rfl).symm) (fc.anti h.le)
    rw [abs_le]
    exact ⟨by linarith, h1⟩
  -- pointwise domination of the `p`-integrand by `D·1_{B(0,2κ)}`
  have hpt : ∀ p, ‖F p‖ ≤ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (2 * κ)).indicator
      (fun _ => D) p := by
    intro p
    by_cases hp : p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (2 * κ)
    · rw [Set.indicator_of_mem hp, hFp p, norm_mul, norm_mul]
      have h1 : ‖Complex.exp (Complex.I * (inner ℝ p y : ℂ))‖ = 1 := by
        rw [mul_comm Complex.I ((inner ℝ p y : ℂ)), Complex.norm_exp_ofReal_mul_I]
      have h2 : ‖(((fc.f (‖p‖ / κ) : ℝ)) : ℂ)‖ ≤ 1 := by
        simpa using habs (‖p‖ / κ)
      rw [h1, one_mul]
      have := mul_le_mul h2 (hkin p) (norm_nonneg _) zero_le_one
      linarith
    · rw [Set.indicator_of_notMem hp]
      have hp' : 2 * κ < ‖p‖ := by
        have h1 : ¬ (dist p (0 : EuclideanSpace ℝ (Fin 3)) ≤ 2 * κ) :=
          fun hc => hp (Metric.mem_closedBall.mpr hc)
        rw [dist_eq_norm, sub_zero] at h1
        exact not_le.mp h1
      have h2 : (2 : ℝ) ≤ ‖p‖ / κ := (le_div_iff₀ hκ).mpr (le_of_lt hp')
      rw [hFp p, fc.zero (‖p‖ / κ) h2]
      simp
  have hInt : Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (2 * κ)).indicator (fun _ => D) p)
      volume := by
    rw [MeasureTheory.integrable_indicator_iff measurableSet_closedBall]
    refine MeasureTheory.IntegrableOn.of_bound ?_ aestronglyMeasurable_const D ?_
    · exact (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) (2 * κ)).measure_lt_top
    · filter_upwards with z
      rw [Real.norm_of_nonneg hD0]
  have hstep : ‖∫ p : EuclideanSpace ℝ (Fin 3), F p‖
      ≤ ∫ p, (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (2 * κ)).indicator (fun _ => D) p :=
    le_trans (MeasureTheory.norm_integral_le_integral_norm _)
      (integral_mono_of_nonneg (Eventually.of_forall (fun p => norm_nonneg _)) hInt
        (Eventually.of_forall hpt))
  have hval : (∫ p : EuclideanSpace ℝ (Fin 3),
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (2 * κ)).indicator (fun _ => D) p)
      = (MeasureTheory.volume
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (2 * κ))).toReal * D := by
    rw [MeasureTheory.integral_indicator_const D measurableSet_closedBall,
      MeasureTheory.Measure.real, smul_eq_mul]
  calc |Work.BoseBoxFix.lowMult fc κ ℓ ψ y|
      = |((c : ℂ) * ∫ p : EuclideanSpace ℝ (Fin 3), F p).re| := by rw [hlow]
    _ ≤ ‖(c : ℂ) * ∫ p : EuclideanSpace ℝ (Fin 3), F p‖ := Complex.abs_re_le_norm _
    _ = c * ‖∫ p : EuclideanSpace ℝ (Fin 3), F p‖ := by
        rw [norm_mul]
        congr 1
        exact (RCLike.norm_ofReal c).trans (abs_of_pos hcpos)
    _ ≤ c * (∫ p,
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (2 * κ)).indicator (fun _ => D) p) :=
        mul_le_mul_of_nonneg_left hstep hcpos.le
    _ = c * ((MeasureTheory.volume
            (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (2 * κ))).toReal * D) := by
        rw [hval]
    _ = c * D * (MeasureTheory.volume
            (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (2 * κ))).toReal := by
        ring

/-- The `L¹`-mass of the box-localised version of `ψ` over the cube `acube ℓ` is at most
`M ℓ³` when `|ψ| ≤ M` on the cube. -/
lemma integral_indicator_norm_le {ℓ M : ℝ} (hℓ : 0 < ℓ) (hM : 0 ≤ M)
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψ : ∀ z ∈ Submission.BoseGases.acube ℓ, |ψ z| ≤ M) :
    ∫ z, ‖(((Submission.BoseGases.acube ℓ).indicator ψ z : ℝ) : ℂ)‖ ≤ M * ℓ ^ 3 := by
  have hpt : ∀ z : EuclideanSpace ℝ (Fin 3),
      ‖(((Submission.BoseGases.acube ℓ).indicator ψ z : ℝ) : ℂ)‖
        ≤ (Submission.BoseGases.acube ℓ).indicator (fun _ => M) z := by
    intro z
    by_cases hz : z ∈ Submission.BoseGases.acube ℓ
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
      simpa using hψ z hz
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
      simp
  have hint : Integrable (fun z : EuclideanSpace ℝ (Fin 3) =>
      (Submission.BoseGases.acube ℓ).indicator (fun _ => M) z) volume := by
    rw [MeasureTheory.integrable_indicator_iff (Submission.BoseGases.acube_measurable ℓ)]
    refine MeasureTheory.IntegrableOn.of_bound (Submission.BoseGases.acube_lt_top ℓ hℓ.le)
      aestronglyMeasurable_const M ?_
    filter_upwards with z
    rw [Real.norm_of_nonneg hM]
  calc ∫ z, ‖(((Submission.BoseGases.acube ℓ).indicator ψ z : ℝ) : ℂ)‖
      ≤ ∫ z, (Submission.BoseGases.acube ℓ).indicator (fun _ => M) z :=
        integral_mono_of_nonneg (Eventually.of_forall (fun z => norm_nonneg _)) hint
          (Eventually.of_forall hpt)
    _ = M * ℓ ^ 3 := by
        rw [MeasureTheory.integral_indicator_const M (Submission.BoseGases.acube_measurable ℓ)]
        rw [MeasureTheory.Measure.real, Submission.BoseGases.acube_volume ℓ hℓ.le,
          ENNReal.toReal_ofReal (by positivity)]
        ring

/-! `lowSlot fc κ ℓ j Ψ x = lowMult fc κ ℓ (fun z => Ψ (update x j z)) (x j)` and
`lowMult` is the p-integral `(2π)⁻³ ∫_p e^{i⟨p,y⟩} f(‖p‖/κ) kinFT(1_{acube ℓ}·fibre) p dp`.
For `κ > 0` the factor `f(‖p‖/κ)` vanishes for `‖p‖ ≥ 2κ` (`LowCut.zero`), so the p-integrand is
compactly supported; with `‖kinFT u p‖ ≤ ∫_z ‖u z‖` (`MeasureTheory.norm_integral_le_integral_norm`)
and `‖u‖ ≤ M` on `acube ℓ` (from continuity of `Ψ` and `update x j z ∈ abox n ℓ` for `x ∈ abox n ℓ`,
`z ∈ acube ℓ`) the bound is uniform on the box. -/
theorem lowSlotBound {fc : Work.BoseBoxFix.LowCut} {κ ℓ : ℝ} (hκ : 0 < κ) (hℓ : 0 < ℓ)
    {n : ℕ} (j : Fin n) {Ψ : Submission.BoseGases.X n → ℝ} (hΨ : Continuous Ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Submission.BoseGases.abox n ℓ,
      |Work.BoseBoxFix.lowSlot fc κ ℓ j Ψ x| ≤ C := by
  -- `Ψ` is bounded on the compact box
  obtain ⟨C₀, hC₀⟩ :=
    (Work.UBBInputs9.B.abox_isCompact n ℓ).exists_bound_of_continuousOn hΨ.continuousOn
  refine ⟨((2 * π) ^ 3)⁻¹ * (max C₀ 0 * ℓ ^ 3)
      * (MeasureTheory.volume
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (2 * κ))).toReal, ?_, ?_⟩
  · have h1 : (0 : ℝ) < ((2 * π) ^ 3)⁻¹ := by positivity
    have h2 : 0 ≤ max C₀ 0 * ℓ ^ 3 := mul_nonneg (le_max_right _ _) (by positivity)
    have h3 : 0 ≤ (MeasureTheory.volume
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (2 * κ))).toReal :=
      ENNReal.toReal_nonneg
    exact mul_nonneg (mul_nonneg h1.le h2) h3
  · intro x hx
    have hM : ∀ y ∈ Submission.BoseGases.abox n ℓ, |Ψ y| ≤ max C₀ 0 := fun y hy =>
      le_trans (by simpa [Real.norm_eq_abs] using hC₀ y hy) (le_max_left _ _)
    -- the slot-`j` fibre of `Ψ` at a box point is bounded by `max C₀ 0` on the cube
    have hψb : ∀ z ∈ Submission.BoseGases.acube ℓ,
        |Ψ (Function.update x j z)| ≤ max C₀ 0 := by
      intro z hz
      apply hM
      intro i
      by_cases hi : i = j
      · rw [hi, Function.update_self]
        exact hz
      · rw [Function.update_of_ne hi]
        exact (Submission.BoseGases.mem_abox_iff n ℓ x).mp hx i
    have hint := integral_indicator_norm_le hℓ (le_max_right C₀ 0)
      (ψ := fun z => Ψ (Function.update x j z)) hψb
    have h0D : 0 ≤ max C₀ 0 * ℓ ^ 3 := mul_nonneg (le_max_right _ _) (by positivity)
    have hfin := lowMult_abs_le (fc := fc) (κ := κ) (ℓ := ℓ)
      (D := max C₀ 0 * ℓ ^ 3) hκ h0D hint (x j)
    simpa [Work.BoseBoxFix.lowSlot] using hfin

end Work.BoseFixB3.Split
