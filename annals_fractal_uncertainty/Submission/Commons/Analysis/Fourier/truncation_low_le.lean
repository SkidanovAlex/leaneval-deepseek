import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Commons.Analysis.Norm.norm_le_sum_abs_coord

/-!
# Low-frequency truncation bound

This file proves `Commons.Analysis.Fourier.truncation_low_le`: on the region
`∑ᵢ |ξᵢ| ≤ R` the exponential growth factor together with the exponential decay of `Ψ`
is bounded by `1`, so that the truncated product is dominated (up to the weight
`(1 + R²)^d`) by the weighted `L²` mass of `G`.
-/

namespace Commons.Analysis.Fourier

open MeasureTheory
open scoped BigOperators ENNReal

set_option autoImplicit false

private lemma continuous_coordAbsSum {d : ℕ} :
    Continuous (fun ξ : EuclideanSpace ℝ (Fin d) => ∑ i : Fin d, |ξ i|) := by
  apply continuous_finsetSum
  intro i _
  exact continuous_abs.comp (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i)

/-- Auxiliary exponential inequality.  For `0 ≤ s ≤ R`, `c₃ ≥ 0` and `α ≥ 0`, the exponential
of the growing factor at frequency scale `R` compensates the decay exponent at scale `s`. -/
private lemma exp_growth_mul_decay_le_one {c₃ α R s : ℝ}
    (hc₃ : 0 ≤ c₃) (hα : 0 ≤ α) (hs : 0 ≤ s) (hsR : s ≤ R) :
    Real.exp (c₃ * (Real.log (2 + R)) ^ (-α) * s)
      * Real.exp (-(c₃ * s / (Real.log (2 + s)) ^ α)) ≤ 1 := by
  rw [← Real.exp_add, Real.exp_le_one_iff]
  have hRpos : 0 < Real.log (2 + R) := Real.log_pos (by linarith)
  have hspos : 0 < Real.log (2 + s) := Real.log_pos (by linarith)
  have hlog : Real.log (2 + s) ≤ Real.log (2 + R) :=
    Real.log_le_log (by linarith) (by linarith)
  have hrpow : (Real.log (2 + s)) ^ α ≤ (Real.log (2 + R)) ^ α :=
    Real.rpow_le_rpow (le_of_lt hspos) hlog hα
  have hpos' : 0 < (Real.log (2 + s)) ^ α := Real.rpow_pos_of_pos hspos α
  have hkey : (Real.log (2 + R)) ^ (-α) ≤ (Real.log (2 + s)) ^ (-α) := by
    rw [Real.rpow_neg (le_of_lt hRpos) α, Real.rpow_neg (le_of_lt hspos) α, inv_eq_one_div,
      inv_eq_one_div]
    exact one_div_le_one_div_of_le hpos' hrpow
  have hterm : c₃ * s / (Real.log (2 + s)) ^ α
      = c₃ * s * (Real.log (2 + s)) ^ (-α) := by
    rw [div_eq_mul_inv, Real.rpow_neg (le_of_lt hspos) α]
  rw [hterm]
  have hmain : c₃ * (Real.log (2 + R)) ^ (-α) * s + -(c₃ * s * (Real.log (2 + s)) ^ (-α))
      = c₃ * s * ((Real.log (2 + R)) ^ (-α) - (Real.log (2 + s)) ^ (-α)) := by ring
  rw [hmain]
  exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hc₃ hs) (by linarith)

/-- Pointwise bound on the low-frequency region. -/
private lemma low_pointwise_le {d : ℕ} {c₃ α R : ℝ} (hc₃ : 0 ≤ c₃) (hα : 0 ≤ α)
    (G Ψ : EuclideanSpace ℝ (Fin d) → ℂ) {ξ : EuclideanSpace ℝ (Fin d)}
    (hsR : (∑ i : Fin d, |ξ i|) ≤ R)
    (hψ : ‖Ψ ξ‖ ≤ Real.exp (-(c₃ * (∑ i : Fin d, |ξ i|)
      / (Real.log (2 + (∑ i : Fin d, |ξ i|))) ^ α))) :
    ‖(Real.exp (c₃ * (Real.log (2 + R)) ^ (-α) * (∑ i : Fin d, |ξ i|)) : ℂ)
        * (G ξ * Ψ ξ)‖ ^ 2
      ≤ (1 + R ^ 2) ^ (d : ℝ) * ((1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) * ‖G ξ‖ ^ 2) := by
  have hs0 : 0 ≤ ∑ i : Fin d, |ξ i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hξR : ‖ξ‖ ≤ R := le_trans (Commons.Analysis.Norm.norm_le_sum_abs_coord ξ) hsR
  have hbase : 1 + ‖ξ‖ ^ 2 ≤ 1 + R ^ 2 := by nlinarith [norm_nonneg ξ]
  have hCR : (1 + ‖ξ‖ ^ 2) ^ (d : ℝ) ≤ (1 + R ^ 2) ^ (d : ℝ) :=
    Real.rpow_le_rpow (by positivity) hbase (Nat.cast_nonneg d)
  have hAW : (1 + ‖ξ‖ ^ 2) ^ (d : ℝ) * (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) = 1 := by
    rw [← Real.rpow_add (by positivity : (0:ℝ) < 1 + ‖ξ‖ ^ 2), add_neg_cancel, Real.rpow_zero]
  have hge1 : 1 ≤ (1 + R ^ 2) ^ (d : ℝ) * (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) := by
    have h := mul_le_mul_of_nonneg_right hCR
      (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ 1 + ‖ξ‖ ^ 2) (-(d : ℝ)))
    rwa [hAW] at h
  have hexp1 : Real.exp (c₃ * (Real.log (2 + R)) ^ (-α) * (∑ i : Fin d, |ξ i|))
      * Real.exp (-(c₃ * (∑ i : Fin d, |ξ i|)
          / (Real.log (2 + (∑ i : Fin d, |ξ i|))) ^ α)) ≤ 1 :=
    exp_growth_mul_decay_le_one (s := ∑ i : Fin d, |ξ i|) hc₃ hα hs0 hsR
  have hnrm : ‖(Real.exp (c₃ * (Real.log (2 + R)) ^ (-α) * (∑ i : Fin d, |ξ i|)) : ℂ)
        * (G ξ * Ψ ξ)‖
      = Real.exp (c₃ * (Real.log (2 + R)) ^ (-α) * (∑ i : Fin d, |ξ i|))
        * (‖G ξ‖ * ‖Ψ ξ‖) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
  have hbnd : Real.exp (c₃ * (Real.log (2 + R)) ^ (-α) * (∑ i : Fin d, |ξ i|))
        * (‖G ξ‖ * ‖Ψ ξ‖) ≤ ‖G ξ‖ := by
    have h1 : Real.exp (c₃ * (Real.log (2 + R)) ^ (-α) * (∑ i : Fin d, |ξ i|))
        * ‖Ψ ξ‖ ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_left hψ (Real.exp_nonneg _)) hexp1
    calc Real.exp (c₃ * (Real.log (2 + R)) ^ (-α) * (∑ i : Fin d, |ξ i|))
          * (‖G ξ‖ * ‖Ψ ξ‖)
        = ‖G ξ‖ * (Real.exp (c₃ * (Real.log (2 + R)) ^ (-α) * (∑ i : Fin d, |ξ i|))
            * ‖Ψ ξ‖) := by ring
      _ ≤ ‖G ξ‖ * 1 := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = ‖G ξ‖ := by ring
  have hsq : ‖(Real.exp (c₃ * (Real.log (2 + R)) ^ (-α) * (∑ i : Fin d, |ξ i|)) : ℂ)
        * (G ξ * Ψ ξ)‖ ^ 2 ≤ ‖G ξ‖ ^ 2 := by
    have h := pow_le_pow_left₀
      (mul_nonneg (Real.exp_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))) hbnd 2
    rwa [← hnrm] at h
  have hfin : ‖G ξ‖ ^ 2
      ≤ (1 + R ^ 2) ^ (d : ℝ) * ((1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) * ‖G ξ‖ ^ 2) := by
    calc ‖G ξ‖ ^ 2 = 1 * ‖G ξ‖ ^ 2 := by ring
      _ ≤ ((1 + R ^ 2) ^ (d : ℝ) * (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ))) * ‖G ξ‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hge1 (sq_nonneg _)
      _ = (1 + R ^ 2) ^ (d : ℝ) * ((1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) * ‖G ξ‖ ^ 2) := by ring
  exact le_trans hsq hfin

theorem truncation_low_le (d : ℕ) {c₃ α R : ℝ} (hc₃ : 0 ≤ c₃) (hα : 0 ≤ α) (hR : 0 ≤ R)
    (G Ψ : EuclideanSpace ℝ (Fin d) → ℂ)
    (hG2 : MeasureTheory.MemLp G 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))))
    (hGP : MeasureTheory.MemLp (fun ξ => G ξ * Ψ ξ) 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))))
    (hPsi : ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))),
      G ξ ≠ 0 → ‖Ψ ξ‖ ≤ Real.exp (-(c₃ * (∑ i : Fin d, |ξ i|) / (Real.log (2 + (∑ i : Fin d, |ξ i|))) ^ α))) :
    MeasureTheory.integral MeasureTheory.volume
      (fun ξ : EuclideanSpace ℝ (Fin d) =>
        ‖(if (∑ i : Fin d, |ξ i|) ≤ R then
            (Real.exp (c₃ * (Real.log (2 + R)) ^ (-α) * (∑ i : Fin d, |ξ i|)) : ℂ) * (G ξ * Ψ ξ)
          else 0)‖ ^ 2)
      ≤ (1 + R ^ 2) ^ (d : ℝ) *
        MeasureTheory.integral MeasureTheory.volume
          (fun ξ : EuclideanSpace ℝ (Fin d) => (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) * ‖G ξ‖ ^ 2) := by
  -- ### the a.e. pointwise bound
  have hpoint : ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))),
      ‖(if (∑ i : Fin d, |ξ i|) ≤ R then
          (Real.exp (c₃ * (Real.log (2 + R)) ^ (-α) * (∑ i : Fin d, |ξ i|)) : ℂ) * (G ξ * Ψ ξ)
        else 0)‖ ^ 2
        ≤ (1 + R ^ 2) ^ (d : ℝ) * ((1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) * ‖G ξ‖ ^ 2) := by
    filter_upwards [hPsi] with ξ hξ
    by_cases hle : (∑ i : Fin d, |ξ i|) ≤ R
    · rw [if_pos hle]
      rcases eq_or_ne (G ξ) 0 with hG | hG
      · have hzero : ‖(Real.exp (c₃ * (Real.log (2 + R)) ^ (-α) * (∑ i : Fin d, |ξ i|)) : ℂ)
            * (G ξ * Ψ ξ)‖ ^ 2 = 0 := by
          rw [hG, zero_mul, mul_zero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
        rw [hzero]
        exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
          (mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _))
      · exact low_pointwise_le hc₃ hα G Ψ hle (hξ hG)
    · rw [if_neg hle, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _))
  -- ### integrability of the weighted G term
  have hG2int : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => ‖G ξ‖ ^ 2)
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) := by
    simpa [Real.rpow_two] using hG2.integrable_norm_rpow (by norm_num) (by norm_num)
  have hGPint : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => ‖G ξ * Ψ ξ‖ ^ 2)
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) := by
    simpa [Real.rpow_two] using hGP.integrable_norm_rpow (by norm_num) (by norm_num)
  have hw_aesm : AEStronglyMeasurable (fun ξ : EuclideanSpace ℝ (Fin d) => (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)))
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) := by
    have hcont : Continuous (fun ξ : EuclideanSpace ℝ (Fin d) => (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ))) :=
      (continuous_const.add (continuous_norm.pow 2)).rpow_const
        (fun x => Or.inl (by
          have h : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
          simpa only [Pi.add_apply, Pi.pow_apply] using ne_of_gt h))
    exact hcont.aestronglyMeasurable
  have hbase_int : Integrable
      (fun ξ : EuclideanSpace ℝ (Fin d) => (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) * ‖G ξ‖ ^ 2)
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) := by
    refine Integrable.mono' hG2int ?_ ?_
    · have h2 : AEStronglyMeasurable (fun ξ : EuclideanSpace ℝ (Fin d) => ‖G ξ‖ ^ 2)
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) := by
        convert hG2.aestronglyMeasurable.norm.mul hG2.aestronglyMeasurable.norm using 2 <;>
          first
            | rw [Pi.mul_apply, pow_two]
            | rfl
      exact hw_aesm.mul h2
    · filter_upwards with ξ
      have hw1 : (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) ≤ 1 := by
        have h1 : (1 : ℝ) ≤ 1 + ‖ξ‖ ^ 2 := by linarith [sq_nonneg ‖ξ‖]
        have h2 : (-(d : ℝ)) ≤ 0 := neg_nonpos.mpr (Nat.cast_nonneg d)
        have := Real.rpow_le_rpow_of_exponent_le h1 h2
        simpa using this
      have hnn : 0 ≤ (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) * ‖G ξ‖ ^ 2 :=
        mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      nlinarith [hw1, sq_nonneg ‖G ξ‖]
  -- ### integrability of the truncated term
  have hsum_meas : Measurable (fun ξ : EuclideanSpace ℝ (Fin d) => ∑ i : Fin d, |ξ i|) :=
    continuous_coordAbsSum.measurable
  have hset : MeasurableSet {ξ : EuclideanSpace ℝ (Fin d) | (∑ i : Fin d, |ξ i|) ≤ R} :=
    measurableSet_le hsum_meas measurable_const
  have hcont_inner : Continuous (fun ξ : EuclideanSpace ℝ (Fin d) =>
      c₃ * (Real.log (2 + R)) ^ (-α) * (∑ i : Fin d, |ξ i|)) :=
    continuous_const.mul continuous_coordAbsSum
  have hexp_meas : Measurable (fun ξ : EuclideanSpace ℝ (Fin d) =>
      (Real.exp (c₃ * (Real.log (2 + R)) ^ (-α) * (∑ i : Fin d, |ξ i|)) : ℂ)) :=
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp hcont_inner)).measurable
  have hind : (fun ξ : EuclideanSpace ℝ (Fin d) =>
        (if (∑ i : Fin d, |ξ i|) ≤ R then
          (Real.exp (c₃ * (Real.log (2 + R)) ^ (-α) * (∑ i : Fin d, |ξ i|)) : ℂ) * (G ξ * Ψ ξ)
         else 0))
      = {ξ : EuclideanSpace ℝ (Fin d) | (∑ i : Fin d, |ξ i|) ≤ R}.indicator
          (fun ξ => (Real.exp (c₃ * (Real.log (2 + R)) ^ (-α) * (∑ i : Fin d, |ξ i|)) : ℂ)
            * (G ξ * Ψ ξ)) := by
    funext ξ
    rw [Set.indicator_apply]
    by_cases h : (∑ i : Fin d, |ξ i|) ≤ R <;> simp [h]
  have hind_aesm : AEStronglyMeasurable (fun ξ : EuclideanSpace ℝ (Fin d) =>
      (if (∑ i : Fin d, |ξ i|) ≤ R then
        (Real.exp (c₃ * (Real.log (2 + R)) ^ (-α) * (∑ i : Fin d, |ξ i|)) : ℂ) * (G ξ * Ψ ξ)
       else 0)) (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) := by
    rw [hind]
    exact ((hexp_meas.aestronglyMeasurable).mul hGP.aestronglyMeasurable).indicator hset
  have hf_aesm : AEStronglyMeasurable (fun ξ : EuclideanSpace ℝ (Fin d) =>
      ‖(if (∑ i : Fin d, |ξ i|) ≤ R then
          (Real.exp (c₃ * (Real.log (2 + R)) ^ (-α) * (∑ i : Fin d, |ξ i|)) : ℂ) * (G ξ * Ψ ξ)
        else 0)‖ ^ 2) (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) :=
    (continuous_norm.pow 2).comp_aestronglyMeasurable hind_aesm
  have hMbound : ∀ ξ : EuclideanSpace ℝ (Fin d),
      ‖(if (∑ i : Fin d, |ξ i|) ≤ R then
          (Real.exp (c₃ * (Real.log (2 + R)) ^ (-α) * (∑ i : Fin d, |ξ i|)) : ℂ) * (G ξ * Ψ ξ)
        else 0)‖ ^ 2
      ≤ Real.exp (c₃ * (Real.log (2 + R)) ^ (-α) * R) ^ 2 * ‖G ξ * Ψ ξ‖ ^ 2 := by
    intro ξ
    by_cases h : (∑ i : Fin d, |ξ i|) ≤ R
    · rw [if_pos h]
      have hA : c₃ * (Real.log (2 + R)) ^ (-α) * (∑ i : Fin d, |ξ i|)
          ≤ c₃ * (Real.log (2 + R)) ^ (-α) * R :=
        mul_le_mul_of_nonneg_left h
          (mul_nonneg hc₃ (Real.rpow_nonneg (Real.log_nonneg (by linarith)) _))
      have hexp_le : Real.exp (c₃ * (Real.log (2 + R)) ^ (-α) * (∑ i : Fin d, |ξ i|))
          ≤ Real.exp (c₃ * (Real.log (2 + R)) ^ (-α) * R) := Real.exp_le_exp.mpr hA
      have hnrm : ‖(Real.exp (c₃ * (Real.log (2 + R)) ^ (-α) * (∑ i : Fin d, |ξ i|)) : ℂ)
            * (G ξ * Ψ ξ)‖
          = Real.exp (c₃ * (Real.log (2 + R)) ^ (-α) * (∑ i : Fin d, |ξ i|)) * ‖G ξ * Ψ ξ‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
      rw [hnrm]
      calc (Real.exp (c₃ * (Real.log (2 + R)) ^ (-α) * (∑ i : Fin d, |ξ i|))
              * ‖G ξ * Ψ ξ‖) ^ 2
          ≤ (Real.exp (c₃ * (Real.log (2 + R)) ^ (-α) * R) * ‖G ξ * Ψ ξ‖) ^ 2 := by
            apply pow_le_pow_left₀ (by positivity)
            exact mul_le_mul_of_nonneg_right hexp_le (norm_nonneg _)
        _ = Real.exp (c₃ * (Real.log (2 + R)) ^ (-α) * R) ^ 2 * ‖G ξ * Ψ ξ‖ ^ 2 := by ring
    · rw [if_neg h, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      positivity
  have hf_int : Integrable
      (fun ξ : EuclideanSpace ℝ (Fin d) =>
        ‖(if (∑ i : Fin d, |ξ i|) ≤ R then
            (Real.exp (c₃ * (Real.log (2 + R)) ^ (-α) * (∑ i : Fin d, |ξ i|)) : ℂ) * (G ξ * Ψ ξ)
          else 0)‖ ^ 2)
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) := by
    refine Integrable.mono'
      (hGPint.const_mul (Real.exp (c₃ * (Real.log (2 + R)) ^ (-α) * R) ^ 2)) hf_aesm ?_
    filter_upwards with ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hMbound ξ
  have hCg_int : Integrable
      (fun ξ : EuclideanSpace ℝ (Fin d) =>
        (1 + R ^ 2) ^ (d : ℝ) * ((1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) * ‖G ξ‖ ^ 2))
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) :=
    hbase_int.const_mul _
  calc MeasureTheory.integral MeasureTheory.volume
        (fun ξ : EuclideanSpace ℝ (Fin d) =>
          ‖(if (∑ i : Fin d, |ξ i|) ≤ R then
              (Real.exp (c₃ * (Real.log (2 + R)) ^ (-α) * (∑ i : Fin d, |ξ i|)) : ℂ) * (G ξ * Ψ ξ)
            else 0)‖ ^ 2)
      ≤ MeasureTheory.integral MeasureTheory.volume
          (fun ξ : EuclideanSpace ℝ (Fin d) =>
            (1 + R ^ 2) ^ (d : ℝ) * ((1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) * ‖G ξ‖ ^ 2)) :=
        integral_mono_ae hf_int hCg_int hpoint
    _ = (1 + R ^ 2) ^ (d : ℝ) * MeasureTheory.integral MeasureTheory.volume
          (fun ξ : EuclideanSpace ℝ (Fin d) => (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) * ‖G ξ‖ ^ 2) :=
        integral_const_mul _ _

end Commons.Analysis.Fourier