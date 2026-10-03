import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

open MeasureTheory
open scoped ENNReal

namespace Commons.Analysis.MeasureTheory

theorem lintegral_mul_rpow_le_rpow_mul_lintegral {p : ℝ} (hp : 1 < p)
    {f w : ℝ → ENNReal} (hf : AEMeasurable f MeasureTheory.volume) (hw : AEMeasurable w MeasureTheory.volume) :
    (MeasureTheory.lintegral MeasureTheory.volume (fun t : ℝ => f t * w t)) ^ p
      ≤ (MeasureTheory.lintegral MeasureTheory.volume (fun t : ℝ => w t)) ^ (p - 1)
        * MeasureTheory.lintegral MeasureTheory.volume (fun t : ℝ => f t ^ p * w t) := by
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp
  set q : ℝ := Real.conjExponent p with hq
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  have hqpos : (0:ℝ) < q := hpq.symm.pos
  have h1p : 0 ≤ 1 / p := le_of_lt (one_div_pos.2 hp0)
  have h1q : 0 ≤ 1 / q := le_of_lt (one_div_pos.2 hqpos)
  have hsum : 1 / p + 1 / q = 1 := by
    have := hpq.one_div_add_one_div
    simpa using this
  have hqmul : (1 / q) * p = p - 1 := by
    rw [one_div, mul_comm, ← div_eq_mul_inv]
    exact hpq.div_conj_eq_sub_one
  have hpmul : (1 / p) * p = 1 := one_div_mul_cancel hp0.ne'
  have hA : AEMeasurable (fun t : ℝ => f t * w t ^ (1 / p)) volume :=
    hf.mul (hw.pow_const (1 / p))
  have hB : AEMeasurable (fun t : ℝ => w t ^ (1 / q)) volume := hw.pow_const (1 / q)
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq hA hB
  simp only [Pi.mul_apply] at hholder
  have hAint : ∀ t : ℝ, (f t * w t ^ (1 / p)) ^ p = f t ^ p * w t := by
    intro t
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, hpmul, ENNReal.rpow_one]
  have hBint : ∀ t : ℝ, (w t ^ (1 / q)) ^ q = w t := by
    intro t
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hpq.symm.ne_zero, ENNReal.rpow_one]
  have hCint : ∀ t : ℝ, (f t * w t ^ (1 / p)) * w t ^ (1 / q) = f t * w t := by
    intro t
    rw [mul_assoc,
      ← ENNReal.rpow_add_of_nonneg (x := w t) (1 / p) (1 / q) h1p h1q, hsum, ENNReal.rpow_one]
  rw [show (∫⁻ t, (f t * w t ^ (1 / p)) * w t ^ (1 / q)) = ∫⁻ t, f t * w t from
      lintegral_congr hCint] at hholder
  rw [show (∫⁻ t, (f t * w t ^ (1 / p)) ^ p) = ∫⁻ t, f t ^ p * w t from
      lintegral_congr hAint] at hholder
  rw [show (∫⁻ t, (w t ^ (1 / q)) ^ q) = ∫⁻ t, w t from
      lintegral_congr hBint] at hholder
  have hpow := ENNReal.rpow_le_rpow hholder hp0.le
  refine hpow.trans_eq ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    hpmul, hqmul, ENNReal.rpow_one]
  exact mul_comm _ _

end Commons.Analysis.MeasureTheory