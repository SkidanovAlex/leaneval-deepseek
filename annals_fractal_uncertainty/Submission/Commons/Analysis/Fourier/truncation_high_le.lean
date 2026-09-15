import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Commons.Analysis.Inequalities.truncation_high_crux
import Submission.Commons.Analysis.Norm.norm_le_sum_abs_coord

/-!
# High-frequency truncation bound

This file proves `Commons.Analysis.Fourier.truncation_high_le`: on the region
`∑ᵢ |ξᵢ| > R` the product `G · Ψ` is controlled by the exponential decay of `Ψ`
against the weighted `L²` mass of `G`.
-/

namespace Commons.Analysis.Fourier

open MeasureTheory
open scoped BigOperators ENNReal

set_option autoImplicit false

/-- The `ℓ¹`-type weight `ξ ↦ ∑ i, |ξ i|` on `EuclideanSpace ℝ (Fin d)`. -/
private noncomputable def coordAbsSum {d : ℕ} (ξ : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i, |ξ i|

private lemma coordAbsSum_nonneg {d : ℕ} (ξ : EuclideanSpace ℝ (Fin d)) : 0 ≤ coordAbsSum ξ :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

private lemma coordAbsSum_measurable {d : ℕ} :
    Measurable (coordAbsSum (d := d)) := by
  apply Finset.measurable_sum
  intro i _
  exact (continuous_abs.comp (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i)).measurable

private lemma measurableSet_coordAbsSum_lt {d : ℕ} (R : ℝ) :
    MeasurableSet {ξ : EuclideanSpace ℝ (Fin d) | R < coordAbsSum ξ} :=
  measurableSet_lt measurable_const coordAbsSum_measurable

theorem truncation_high_le (d : ℕ) {c₃ α R : ℝ} (hc₃ : 0 < c₃) (hα : 0 < α) (hα1 : α ≤ 1)
    (hR : (2 * (d : ℝ) / c₃) ^ 2 ≤ R)
    (G Ψ : EuclideanSpace ℝ (Fin d) → ℂ)
    (hG2 : MeasureTheory.MemLp G 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))))
    (hGP : MeasureTheory.MemLp (fun ξ => G ξ * Ψ ξ) 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))))
    (hPsi : ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))),
      G ξ ≠ 0 → ‖Ψ ξ‖ ≤ Real.exp (-(c₃ * (∑ i : Fin d, |ξ i|) / (Real.log (2 + (∑ i : Fin d, |ξ i|))) ^ α))) :
    MeasureTheory.integral MeasureTheory.volume
        (fun ξ : EuclideanSpace ℝ (Fin d) =>
          ‖(if R < (∑ i : Fin d, |ξ i|) then G ξ * Ψ ξ else 0)‖ ^ 2)
      ≤ (Real.exp (-(c₃ * R / (Real.log (2 + R)) ^ α)) * (1 + R ^ 2) ^ ((d : ℝ) / 2)) ^ 2 *
        MeasureTheory.integral MeasureTheory.volume
          (fun ξ : EuclideanSpace ℝ (Fin d) =>
            (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) * ‖G ξ‖ ^ 2) := by
  set C : ℝ := (Real.exp (-(c₃ * R / (Real.log (2 + R)) ^ α)) * (1 + R ^ 2) ^ ((d : ℝ) / 2)) ^ 2
    with hCdef
  have hCnn : 0 ≤ C := by rw [hCdef]; positivity
  -- ### The a.e. pointwise bound
  have hpoint : ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))),
      ‖(if R < (∑ i : Fin d, |ξ i|) then G ξ * Ψ ξ else 0)‖ ^ 2
        ≤ C * ((1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) * ‖G ξ‖ ^ 2) := by
    filter_upwards [hPsi] with ξ hξ
    by_cases hRs : R < (∑ i : Fin d, |ξ i|)
    · rw [if_pos hRs]
      rcases eq_or_ne (G ξ) 0 with hG | hG
      · have hL : ‖G ξ * Ψ ξ‖ ^ 2 = 0 := by
          rw [hG, zero_mul, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
        rw [hL]
        exact mul_nonneg hCnn
          (mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _))
      · have hξb : ‖Ψ ξ‖ ≤
            Real.exp (-(c₃ * (∑ i : Fin d, |ξ i|) / (Real.log (2 + (∑ i : Fin d, |ξ i|))) ^ α)) :=
          hξ hG
        have hcr := Commons.Analysis.Inequalities.truncation_high_crux
          (c₃ := c₃) (α := α) (d := (d : ℝ)) (R := R) (t := ∑ i : Fin d, |ξ i|)
          hc₃ (by positivity) hα hα1 hR (le_of_lt hRs)
        have hnormξ : ‖ξ‖ ≤ ∑ i : Fin d, |ξ i| :=
          Commons.Analysis.Norm.norm_le_sum_abs_coord ξ
        have hkey : ((d : ℝ) / 2) * Real.log (1 + ‖ξ‖ ^ 2) - ((d : ℝ) / 2) * Real.log (1 + R ^ 2)
            ≤ c₃ * (∑ i : Fin d, |ξ i|) / (Real.log (2 + (∑ i : Fin d, |ξ i|))) ^ α
              - c₃ * R / (Real.log (2 + R)) ^ α := by
          have hlogdiv : Real.log ((1 + (∑ i : Fin d, |ξ i|) ^ 2) / (1 + R ^ 2))
              = Real.log (1 + (∑ i : Fin d, |ξ i|) ^ 2) - Real.log (1 + R ^ 2) :=
            Real.log_div (by positivity) (by positivity)
          have hsq : ‖ξ‖ ^ 2 ≤ (∑ i : Fin d, |ξ i|) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg ξ) hnormξ 2
          have hlogle : Real.log (1 + ‖ξ‖ ^ 2) ≤ Real.log (1 + (∑ i : Fin d, |ξ i|) ^ 2) :=
            Real.log_le_log (by positivity) (by linarith)
          have hfin : c₃ * ((∑ i : Fin d, |ξ i|) / (Real.log (2 + (∑ i : Fin d, |ξ i|))) ^ α
                - R / (Real.log (2 + R)) ^ α)
              = c₃ * (∑ i : Fin d, |ξ i|) / (Real.log (2 + (∑ i : Fin d, |ξ i|))) ^ α
                - c₃ * R / (Real.log (2 + R)) ^ α := by ring
          calc ((d : ℝ) / 2) * Real.log (1 + ‖ξ‖ ^ 2)
                - ((d : ℝ) / 2) * Real.log (1 + R ^ 2)
              = ((d : ℝ) / 2) * (Real.log (1 + ‖ξ‖ ^ 2) - Real.log (1 + R ^ 2)) := by ring
            _ ≤ ((d : ℝ) / 2)
                  * (Real.log (1 + (∑ i : Fin d, |ξ i|) ^ 2) - Real.log (1 + R ^ 2)) :=
                mul_le_mul_of_nonneg_left (by linarith) (by positivity)
            _ = ((d : ℝ) / 2) * Real.log ((1 + (∑ i : Fin d, |ξ i|) ^ 2) / (1 + R ^ 2)) := by
                rw [hlogdiv]
            _ ≤ c₃ * ((∑ i : Fin d, |ξ i|) / (Real.log (2 + (∑ i : Fin d, |ξ i|))) ^ α
                  - R / (Real.log (2 + R)) ^ α) := hcr
            _ = c₃ * (∑ i : Fin d, |ξ i|) / (Real.log (2 + (∑ i : Fin d, |ξ i|))) ^ α
                  - c₃ * R / (Real.log (2 + R)) ^ α := hfin
        -- exponential form of the weight comparison
        have hR2pos : (0 : ℝ) < 1 + R ^ 2 := by positivity
        have hx2pos : (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := by positivity
        have hle : -(c₃ * (∑ i : Fin d, |ξ i|) / (Real.log (2 + (∑ i : Fin d, |ξ i|))) ^ α)
            ≤ -(c₃ * R / (Real.log (2 + R)) ^ α)
              + ((d : ℝ) / 2) * Real.log (1 + R ^ 2)
              - ((d : ℝ) / 2) * Real.log (1 + ‖ξ‖ ^ 2) := by
          linarith [hkey]
        have heq : Real.exp (-(c₃ * R / (Real.log (2 + R)) ^ α)
              + ((d : ℝ) / 2) * Real.log (1 + R ^ 2)
              - ((d : ℝ) / 2) * Real.log (1 + ‖ξ‖ ^ 2))
            = Real.exp (-(c₃ * R / (Real.log (2 + R)) ^ α)) * (1 + R ^ 2) ^ ((d : ℝ) / 2)
              * (1 + ‖ξ‖ ^ 2) ^ (-((d : ℝ) / 2)) := by
          rw [Real.rpow_def_of_pos hR2pos, Real.rpow_def_of_pos hx2pos]
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        have hexp1 : Real.exp (-(c₃ * (∑ i : Fin d, |ξ i|) / (Real.log (2 + (∑ i : Fin d, |ξ i|))) ^ α))
            ≤ Real.exp (-(c₃ * R / (Real.log (2 + R)) ^ α)) * (1 + R ^ 2) ^ ((d : ℝ) / 2)
              * (1 + ‖ξ‖ ^ 2) ^ (-((d : ℝ) / 2)) := by
          calc Real.exp (-(c₃ * (∑ i : Fin d, |ξ i|) / (Real.log (2 + (∑ i : Fin d, |ξ i|))) ^ α))
              ≤ Real.exp (-(c₃ * R / (Real.log (2 + R)) ^ α)
                  + ((d : ℝ) / 2) * Real.log (1 + R ^ 2)
                  - ((d : ℝ) / 2) * Real.log (1 + ‖ξ‖ ^ 2)) :=
                Real.exp_le_exp.mpr hle
            _ = _ := heq
        have hGb : ‖G ξ * Ψ ξ‖ ≤ ‖G ξ‖ *
            (Real.exp (-(c₃ * R / (Real.log (2 + R)) ^ α)) * (1 + R ^ 2) ^ ((d : ℝ) / 2)
              * (1 + ‖ξ‖ ^ 2) ^ (-((d : ℝ) / 2))) := by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (le_trans hξb hexp1) (norm_nonneg _)
        have hsq2 : ‖G ξ * Ψ ξ‖ ^ 2 ≤ (‖G ξ‖ *
            (Real.exp (-(c₃ * R / (Real.log (2 + R)) ^ α)) * (1 + R ^ 2) ^ ((d : ℝ) / 2)
              * (1 + ‖ξ‖ ^ 2) ^ (-((d : ℝ) / 2)))) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hGb 2
        have hrpow : ((1 + ‖ξ‖ ^ 2) ^ (-((d : ℝ) / 2))) ^ 2 = (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) := by
          rw [← Real.rpow_natCast ((1 + ‖ξ‖ ^ 2) ^ (-((d : ℝ) / 2))) 2,
            ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1 + ‖ξ‖ ^ 2)]
          congr 1
          ring
        calc ‖G ξ * Ψ ξ‖ ^ 2
            ≤ (‖G ξ‖ * (Real.exp (-(c₃ * R / (Real.log (2 + R)) ^ α)) * (1 + R ^ 2) ^ ((d : ℝ) / 2)
                * (1 + ‖ξ‖ ^ 2) ^ (-((d : ℝ) / 2)))) ^ 2 := hsq2
          _ = ‖G ξ‖ ^ 2 * ((Real.exp (-(c₃ * R / (Real.log (2 + R)) ^ α)) * (1 + R ^ 2) ^ ((d : ℝ) / 2)) ^ 2
                * (((1 + ‖ξ‖ ^ 2) ^ (-((d : ℝ) / 2))) ^ 2)) := by ring
          _ = ‖G ξ‖ ^ 2 * ((Real.exp (-(c₃ * R / (Real.log (2 + R)) ^ α)) * (1 + R ^ 2) ^ ((d : ℝ) / 2)) ^ 2
                * ((1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)))) := by rw [hrpow]
          _ = C * ((1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) * ‖G ξ‖ ^ 2) := by rw [hCdef]; ring
    · rw [if_neg hRs]
      simp only [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      exact mul_nonneg hCnn
        (mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _))
  -- ### Integrability
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
  have hf_int : Integrable
      (fun ξ : EuclideanSpace ℝ (Fin d) => ‖(if R < (∑ i : Fin d, |ξ i|) then G ξ * Ψ ξ else 0)‖ ^ 2)
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) := by
    refine Integrable.mono' hGPint ?_ ?_
    · have hs : MeasurableSet {ξ : EuclideanSpace ℝ (Fin d) | R < (∑ i : Fin d, |ξ i|)} :=
        measurableSet_coordAbsSum_lt R
      have h := hGP.aestronglyMeasurable.indicator hs
      convert h.norm.mul h.norm using 2
      rw [Pi.mul_apply, pow_two]
      simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    · filter_upwards with ξ
      by_cases hRs : R < (∑ i : Fin d, |ξ i|)
      · rw [if_pos hRs]
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      · rw [if_neg hRs]
        simp only [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
        positivity
  -- ### Integrate the pointwise bound
  have hCg_int : Integrable
      (fun ξ : EuclideanSpace ℝ (Fin d) => C * ((1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) * ‖G ξ‖ ^ 2))
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) :=
    hbase_int.const_mul C
  calc MeasureTheory.integral MeasureTheory.volume
        (fun ξ : EuclideanSpace ℝ (Fin d) =>
          ‖(if R < (∑ i : Fin d, |ξ i|) then G ξ * Ψ ξ else 0)‖ ^ 2)
      ≤ MeasureTheory.integral MeasureTheory.volume
          (fun ξ : EuclideanSpace ℝ (Fin d) => C * ((1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) * ‖G ξ‖ ^ 2)) :=
        integral_mono_ae hf_int hCg_int hpoint
    _ = C * MeasureTheory.integral MeasureTheory.volume
          (fun ξ : EuclideanSpace ℝ (Fin d) => (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) * ‖G ξ‖ ^ 2) :=
        integral_const_mul C _

end Commons.Analysis.Fourier