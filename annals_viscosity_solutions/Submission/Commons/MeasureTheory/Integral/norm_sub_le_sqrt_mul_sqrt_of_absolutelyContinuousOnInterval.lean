import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Submission.Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_deriv_integral_vector

open MeasureTheory Set Filter
set_option linter.style.haveILetI false

open scoped ENNReal Topology

namespace Commons.MeasureTheory.Integral

/-- Auxiliary estimate: if `f` is absolutely continuous on `[a,b]`, `p ≤ q` lie in `[a,b]` and the
square integral of `‖deriv f‖` over `[a,b]` is bounded by `M²`, then
`‖f p - f q‖ ≤ M √(q - p)`. -/
private theorem norm_sub_le_sqrt_mul_sqrt_aux {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {f : ℝ → E} {a b M p q : ℝ} (hab : a ≤ b) (hM : 0 ≤ M) (hpq : p ≤ q)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hp : p ∈ Set.Icc a b) (hq : q ∈ Set.Icc a b)
    (h : ∫⁻ u in Set.Ioc a b, ENNReal.ofReal (‖deriv f u‖ ^ 2)
      ≤ ENNReal.ofReal (M ^ 2)) :
    ‖f p - f q‖ ≤ M * Real.sqrt (q - p) := by
  have hsub : Set.Ioc p q ⊆ Set.Ioc a b :=
    fun x hx => ⟨lt_of_le_of_lt hp.1 hx.1, le_trans hx.2 hq.2⟩
  have hac : AbsolutelyContinuousOnInterval f p q := by
    refine hf.mono ?_
    rw [Set.uIcc_of_le hpq, Set.uIcc_of_le hab]
    exact fun x hx => ⟨le_trans hp.1 hx.1, le_trans hx.2 hq.2⟩
  have hFTC : ∫ x in p..q, deriv f x = f q - f p :=
    absolutelyContinuousOnInterval_deriv_integral_vector hac
  have hstep1 : ‖f p - f q‖ ≤ ∫ x in Set.Ioc p q, ‖deriv f x‖ := by
    have h1 : ‖f p - f q‖ = ‖∫ x in p..q, deriv f x‖ := by
      rw [hFTC, norm_sub_rev]
    rw [h1]
    have h2 := intervalIntegral.norm_integral_le_integral_norm_uIoc (f := deriv f) (a := p) (b := q)
      (μ := volume)
    rw [Set.uIoc, min_eq_left hpq, max_eq_right hpq] at h2
    exact h2
  -- measurability of `deriv f` via the Borel measurable space on `E`
  have hmeas : Measurable (fun x : ℝ => ENNReal.ofReal ‖deriv f x‖) := by
    letI : MeasurableSpace E := borel E
    haveI : BorelSpace E := ⟨rfl⟩
    exact ENNReal.measurable_ofReal.comp (measurable_deriv f).norm
  have haesm : AEStronglyMeasurable (fun x : ℝ => ‖deriv f x‖)
      (volume.restrict (Set.Ioc p q)) := by
    letI : MeasurableSpace E := borel E
    haveI : BorelSpace E := ⟨rfl⟩
    exact ((measurable_deriv f).norm).aestronglyMeasurable
  have haemeas : AEMeasurable (fun x : ℝ => ENNReal.ofReal ‖deriv f x‖)
      (volume.restrict (Set.Ioc p q)) := hmeas.aemeasurable
  have hpq2 : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hHold := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Set.Ioc p q))
    (p := 2) (q := 2) hpq2 haemeas (aemeasurable_const (b := (1 : ℝ≥0∞)))
  have hcongr2 : ∫⁻ x in Set.Ioc p q, (ENNReal.ofReal ‖deriv f x‖) ^ (2 : ℝ)
      = ∫⁻ x in Set.Ioc p q, ENNReal.ofReal (‖deriv f x‖ ^ 2) := by
    refine lintegral_congr fun x => ?_
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (norm_nonneg _)]
  have hone : ∫⁻ x in Set.Ioc p q, (1 : ℝ≥0∞) ^ (2 : ℝ) = ENNReal.ofReal (q - p) := by
    simp_rw [ENNReal.one_rpow]
    rw [setLIntegral_one, Real.volume_Ioc]
  have hHold2 : ∫⁻ x in Set.Ioc p q, ENNReal.ofReal ‖deriv f x‖
      ≤ (∫⁻ x in Set.Ioc p q, ENNReal.ofReal (‖deriv f x‖ ^ 2)) ^ ((1:ℝ)/2)
        * (ENNReal.ofReal (q - p)) ^ ((1:ℝ)/2) := by
    have h' := hHold
    simp only [Pi.mul_apply, mul_one] at h'
    rw [hcongr2, hone] at h'
    exact h'
  -- bound the `L²` norm by `M`
  have hb2 : ∫⁻ x in Set.Ioc p q, ENNReal.ofReal (‖deriv f x‖ ^ 2) ≤ ENNReal.ofReal (M ^ 2) :=
    (lintegral_mono_set hsub).trans h
  have hstepA : (∫⁻ x in Set.Ioc p q, ENNReal.ofReal (‖deriv f x‖ ^ 2)) ^ ((1:ℝ)/2)
      ≤ ENNReal.ofReal M := by
    refine (ENNReal.rpow_le_rpow hb2 (by norm_num)).trans_eq ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg M) (by norm_num)]
    congr 1
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hM]
  have hstepB : (ENNReal.ofReal (q - p)) ^ ((1:ℝ)/2) = ENNReal.ofReal (Real.sqrt (q - p)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (sub_nonneg.mpr hpq) (by norm_num), ← Real.sqrt_eq_rpow]
  have hmain : ∫⁻ x in Set.Ioc p q, ENNReal.ofReal ‖deriv f x‖
      ≤ ENNReal.ofReal (M * Real.sqrt (q - p)) := by
    calc ∫⁻ x in Set.Ioc p q, ENNReal.ofReal ‖deriv f x‖
        ≤ (∫⁻ x in Set.Ioc p q, ENNReal.ofReal (‖deriv f x‖ ^ 2)) ^ ((1:ℝ)/2)
            * (ENNReal.ofReal (q - p)) ^ ((1:ℝ)/2) := hHold2
      _ ≤ ENNReal.ofReal M * ENNReal.ofReal (Real.sqrt (q - p)) := by
            rw [hstepB]
            exact mul_le_mul' hstepA le_rfl
      _ = ENNReal.ofReal (M * Real.sqrt (q - p)) := by
            rw [← ENNReal.ofReal_mul hM]
  have hint_eq : (∫ x in Set.Ioc p q, ‖deriv f x‖)
      = (∫⁻ x in Set.Ioc p q, ENNReal.ofReal ‖deriv f x‖).toReal :=
    integral_eq_lintegral_of_nonneg_ae (μ := volume.restrict (Set.Ioc p q))
      (Eventually.of_forall (fun x => norm_nonneg _)) haesm
  have hbound : ∫ x in Set.Ioc p q, ‖deriv f x‖ ≤ M * Real.sqrt (q - p) := by
    rw [hint_eq]
    calc (∫⁻ x in Set.Ioc p q, ENNReal.ofReal ‖deriv f x‖).toReal
        ≤ (ENNReal.ofReal (M * Real.sqrt (q - p))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hmain
      _ = M * Real.sqrt (q - p) :=
          ENNReal.toReal_ofReal (mul_nonneg hM (Real.sqrt_nonneg _))
  exact hstep1.trans hbound

theorem norm_sub_le_sqrt_mul_sqrt_of_absolutelyContinuousOnInterval {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {f : ℝ → E} {a b M s t : ℝ} (hab : a ≤ b) (hM : 0 ≤ M)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b)
    (h : ∫⁻ u in Set.Ioc a b, ENNReal.ofReal (‖deriv f u‖ ^ 2)
      ≤ ENNReal.ofReal (M ^ 2)) :
    ‖f s - f t‖ ≤ M * Real.sqrt |s - t| := by
  rcases le_total s t with hst | hts
  · have hk := norm_sub_le_sqrt_mul_sqrt_aux hab hM hst hf hs ht h
    have hsq : Real.sqrt |s - t| = Real.sqrt (t - s) := by
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hst)]
    rw [hsq]
    exact hk
  · have hk := norm_sub_le_sqrt_mul_sqrt_aux hab hM hts hf ht hs h
    have hsq : Real.sqrt |s - t| = Real.sqrt (s - t) := by
      rw [abs_of_nonneg (sub_nonneg.mpr hts)]
    rw [norm_sub_rev, hsq]
    exact hk

end Commons.MeasureTheory.Integral