import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Submission.Port.Aesm

open MeasureTheory ENNReal
open scoped ENNReal

namespace Commons.MeasureTheory.Function

variable {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}

/-- Hölder's inequality in the degenerate case where the first exponent is `∞`: for
`ℝ≥0∞`-valued functions `eLpNorm (F * G) p μ ≤ eLpNorm F ∞ μ * eLpNorm G p μ`. -/
private lemma eLpNorm_mul_le_eLpNorm_top_mul_eLpNorm_aux (F G : α → ENNReal) (p : ENNReal)
    (hf : AEMeasurable F μ) (hg : AEMeasurable G μ) :
    MeasureTheory.eLpNorm (fun x => F x * G x) p μ
      ≤ MeasureTheory.eLpNorm F ⊤ μ * MeasureTheory.eLpNorm G p μ := by
  obtain (rfl | rfl | hp) := ENNReal.trichotomy p
  · rw [eLpNorm_exponent_zero (hf := by pw_aesm)]; positivity
  · rw [eLpNorm_exponent_top (f := fun x => F x * G x) (hf.mul hg).aestronglyMeasurable,
      eLpNorm_exponent_top hf.aestronglyMeasurable, eLpNorm_exponent_top hg.aestronglyMeasurable]
    simp only [eLpNormEssSup, enorm_eq_self]
    exact ENNReal.essSup_mul_le F G
  · obtain ⟨hp0, hp_top⟩ := ENNReal.toReal_pos_iff.mp hp
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hp0.ne' hp_top.ne,
        eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hp0.ne' hp_top.ne,
        eLpNorm_exponent_top (hf := by pw_aesm), eLpNormEssSup]
    simp only [enorm_eq_self, one_div, ENNReal.rpow_inv_le_iff hp]
    rw [ENNReal.mul_rpow_of_nonneg (hz := hp.le), ENNReal.rpow_inv_rpow hp.ne',
        ← lintegral_const_mul'' _ (hg.pow_const _)]
    simp only [← ENNReal.mul_rpow_of_nonneg (hz := hp.le)]
    apply lintegral_mono_ae
    filter_upwards [ENNReal.ae_le_essSup F] with x hx
    exact ENNReal.rpow_le_rpow (mul_le_mul_left hx (G x)) hp.le

/-- Hölder's inequality in the degenerate case where the second exponent is `∞`. -/
private lemma eLpNorm_mul_le_eLpNorm_mul_eLpNorm_top_aux (F G : α → ENNReal) (p : ENNReal)
    (hf : AEMeasurable F μ) (hg : AEMeasurable G μ) :
    MeasureTheory.eLpNorm (fun x => F x * G x) p μ
      ≤ MeasureTheory.eLpNorm F p μ * MeasureTheory.eLpNorm G ⊤ μ := by
  simpa only [mul_comm] using eLpNorm_mul_le_eLpNorm_top_mul_eLpNorm_aux G F p hg hf

/-- Hölder's inequality for `ℝ≥0∞`-valued functions with all three exponents finite and
non-zero, obtained from the integral form `ENNReal.lintegral_Lp_mul_le_Lq_mul_Lr`. -/
private lemma eLpNorm_mul_le_eLpNorm_mul_eLpNorm_of_finite {p q r : ENNReal} (hp0 : p ≠ 0)
    (hp : p ≠ ⊤) (hq0 : q ≠ 0) (hq : q ≠ ⊤) (hr0 : r ≠ 0) (hr : r ≠ ⊤)
    (hpq : p⁻¹ = q⁻¹ + r⁻¹) {f g : α → ENNReal} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    MeasureTheory.eLpNorm (fun x => f x * g x) p μ
      ≤ MeasureTheory.eLpNorm f q μ * MeasureTheory.eLpNorm g r μ := by
  have hP : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hQ : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  have hR : 0 < r.toReal := ENNReal.toReal_pos hr0 hr
  have hrel : 1 / p.toReal = 1 / q.toReal + 1 / r.toReal := by
    have h := congrArg ENNReal.toReal hpq
    rw [ENNReal.toReal_add (ENNReal.inv_ne_top.mpr hq0) (ENNReal.inv_ne_top.mpr hr0),
        ENNReal.toReal_inv, ENNReal.toReal_inv, ENNReal.toReal_inv] at h
    rw [one_div, one_div, one_div]
    exact h
  have hlt : p.toReal < q.toReal := by
    have h1 : q.toReal⁻¹ < p.toReal⁻¹ := by
      rw [one_div, one_div, one_div] at hrel
      rw [hrel]
      exact lt_add_of_pos_right _ (inv_pos.mpr hR)
    rwa [inv_lt_inv₀ hQ hP] at h1
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hp0 hp,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hq0 hq,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hr0 hr]
  simpa only [enorm_eq_self, Pi.mul_apply] using
    ENNReal.lintegral_Lp_mul_le_Lq_mul_Lr hP hlt hrel μ hf hg

theorem eLpNorm_mul_le_eLpNorm_mul_eLpNorm {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {p q r : ENNReal} (hpq : p⁻¹ = q⁻¹ + r⁻¹)
    {f g : α → ENNReal} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    MeasureTheory.eLpNorm (fun x => f x * g x) p μ
      ≤ MeasureTheory.eLpNorm f q μ * MeasureTheory.eLpNorm g r μ := by
  obtain (rfl | rfl | hp) := ENNReal.trichotomy p
  · rw [eLpNorm_exponent_zero (hf := by pw_aesm)]; positivity
  · have h : q⁻¹ + r⁻¹ = 0 := by rw [← hpq, ENNReal.inv_top]
    have hq : q = ⊤ := ENNReal.inv_eq_zero.mp (add_eq_zero.mp h).1
    have hr : r = ⊤ := ENNReal.inv_eq_zero.mp (add_eq_zero.mp h).2
    rw [hq, hr, eLpNorm_exponent_top (f := fun x => f x * g x) (hf.mul hg).aestronglyMeasurable,
      eLpNorm_exponent_top hf.aestronglyMeasurable, eLpNorm_exponent_top hg.aestronglyMeasurable]
    simp only [eLpNormEssSup, enorm_eq_self]
    exact ENNReal.essSup_mul_le f g
  · obtain ⟨hp0, hp_top⟩ := ENNReal.toReal_pos_iff.mp hp
    rcases ENNReal.trichotomy q with hq_zero | hq_top | hq
    · exfalso
      have h : p⁻¹ = ⊤ := by rw [hpq, hq_zero, ENNReal.inv_zero, top_add]
      exact hp0.ne' (ENNReal.inv_eq_top.mp h)
    · have hr : r = p := by
        have h := hpq
        rw [hq_top, ENNReal.inv_top, zero_add] at h
        exact (inv_inj.mp h).symm
      rw [hq_top, hr]
      exact eLpNorm_mul_le_eLpNorm_top_mul_eLpNorm_aux f g p hf hg
    · obtain ⟨hq0, hq_top⟩ := ENNReal.toReal_pos_iff.mp hq
      rcases ENNReal.trichotomy r with hr_zero | hr_top | hr
      · exfalso
        have h : p⁻¹ = ⊤ := by rw [hpq, hr_zero, ENNReal.inv_zero, add_top]
        exact hp0.ne' (ENNReal.inv_eq_top.mp h)
      · have hqp : q = p := by
          have h := hpq
          rw [hr_top, ENNReal.inv_top, add_zero] at h
          exact (inv_inj.mp h).symm
        rw [hr_top, hqp]
        exact eLpNorm_mul_le_eLpNorm_mul_eLpNorm_top_aux f g p hf hg
      · obtain ⟨hr0, hr_top⟩ := ENNReal.toReal_pos_iff.mp hr
        exact eLpNorm_mul_le_eLpNorm_mul_eLpNorm_of_finite hp0.ne' hp_top.ne hq0.ne'
          hq_top.ne hr0.ne' hr_top.ne hpq hf hg

end Commons.MeasureTheory.Function
