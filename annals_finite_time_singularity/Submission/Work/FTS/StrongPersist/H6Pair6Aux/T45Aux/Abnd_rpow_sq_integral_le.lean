import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T45Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T45Aux

/-- Pointwise form of the angular bound.  For `i ≠ 0` the factor `Abnd α i θ` is
`(α + sin 2θ)·sin(2θ)^{α/5}`, hence
`sin(2θ)^{-q}·Abnd α i θ² ≤ 4·sin(2θ)^{2α/5 - q}`: the first factor contributes
`(α + sin 2θ)² ≤ 4` and the second `sin(2θ)^{2α/5}·sin(2θ)^{-q} = sin(2θ)^{2α/5-q}`. -/
private lemma Abnd_rpow_mul_sq_le {α q : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) {i : ℕ}
    (hi : i ≠ 0) (hq1 : 1 ≤ q) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Real.sin (2 * θ)) ^ (-q) * (Work.FTS.StrongPersist.H6Pair6Aux.Abnd α i θ) ^ 2
      ≤ 4 * (Real.sin (2 * θ)) ^ (2 * (α / 5) - q) := by
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hα5' : α / 5 + α / 5 ≠ 0 := by linarith
  have hAbnd : Work.FTS.StrongPersist.H6Pair6Aux.Abnd α i θ
      = (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) := by
    simp only [Work.FTS.StrongPersist.H6Pair6Aux.Abnd, hi, ↓reduceIte]
  have hpow : ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2
      = (Real.sin (2 * θ)) ^ (2 * (α / 5)) := by
    rw [pow_two, ← Real.rpow_add' hs hα5']
    congr 1
    ring
  have hab : (α + Real.sin (2 * θ)) ^ 2 ≤ 4 := by
    have h1 : α + Real.sin (2 * θ) ≤ 2 := by linarith
    have h0 : 0 ≤ α + Real.sin (2 * θ) := by linarith
    nlinarith [sq_nonneg (α + Real.sin (2 * θ) - 2)]
  have hne : -q + 2 * (α / 5) ≠ 0 := by
    have h2 : 2 * (α / 5) ≤ 2 / 5 := by linarith
    linarith
  have key : (Real.sin (2 * θ)) ^ (-q) * (4 * (Real.sin (2 * θ)) ^ (2 * (α / 5)))
      = 4 * (Real.sin (2 * θ)) ^ (2 * (α / 5) - q) := by
    rw [show 2 * (α / 5) - q = -q + 2 * (α / 5) by ring, Real.rpow_add' hs hne]
    ring
  rw [hAbnd, mul_pow, hpow]
  calc (Real.sin (2 * θ)) ^ (-q)
        * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * (α / 5)))
      ≤ (Real.sin (2 * θ)) ^ (-q) * (4 * (Real.sin (2 * θ)) ^ (2 * (α / 5))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hab (Real.rpow_nonneg hs _)) (Real.rpow_nonneg hs _)
    _ = 4 * (Real.sin (2 * θ)) ^ (2 * (α / 5) - q) := key

theorem Abnd_rpow_sq_integral_le {α q : ℝ} {i : ℕ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hi : i ≠ 0) (hq1 : 1 ≤ q) (hq2 : q < 1 + 2 * (α / 5)) :
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-q)
          * (Work.FTS.StrongPersist.H6Pair6Aux.Abnd α i θ) ^ 2) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
          * (Work.FTS.StrongPersist.H6Pair6Aux.Abnd α i θ) ^ 2)
        ≤ 4 * (100 / (2 * (α / 5) - q + 1)) := by
  have hp1 : -1 < 2 * (α / 5) - q := by linarith
  have hp0 : 2 * (α / 5) - q ≤ 0 := by
    have h2 : 2 * (α / 5) ≤ 2 / 5 := by linarith
    linarith
  obtain ⟨hint, hval⟩ := Work.Spaces.sin_two_rpow (2 * (α / 5) - q) hp1 hp0
  -- the majorant `4·sin(2θ)^{2α/5-q}` is integrable on `Iθ`
  have hmaj : MeasureTheory.Integrable
      (fun θ : ℝ => 4 * (Real.sin (2 * θ)) ^ (2 * (α / 5) - q))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    hint.const_mul 4
  -- measurability of the integrand
  have hsin : Measurable fun θ : ℝ => Real.sin (2 * θ) :=
    Real.measurable_sin.comp (measurable_const.mul measurable_id)
  have hAbnd : Measurable fun θ : ℝ => Work.FTS.StrongPersist.H6Pair6Aux.Abnd α i θ := by
    have hfun : (fun θ : ℝ => Work.FTS.StrongPersist.H6Pair6Aux.Abnd α i θ)
        = fun θ : ℝ => (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) := by
      funext θ
      simp only [Work.FTS.StrongPersist.H6Pair6Aux.Abnd, hi, ↓reduceIte]
    rw [hfun]
    exact (measurable_const.add hsin).mul (hsin.pow_const (α / 5))
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-q)
        * (Work.FTS.StrongPersist.H6Pair6Aux.Abnd α i θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    ((hsin.pow_const (-q)).mul (hAbnd.pow_const 2)).aestronglyMeasurable
  have hsin_nonneg : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      0 ≤ Real.sin (2 * θ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact Real.sin_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  constructor
  · refine hmaj.mono' hmeas ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Real.norm_of_nonneg (mul_nonneg
      (Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
        ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _) (sq_nonneg _))]
    exact Abnd_rpow_mul_sq_le hα0 hα1 hi hq1 hθ
  · have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-q)
          * (Work.FTS.StrongPersist.H6Pair6Aux.Abnd α i θ) ^ 2) := by
      filter_upwards [hsin_nonneg] with θ hs
      exact mul_nonneg (Real.rpow_nonneg hs _) (sq_nonneg _)
    have hle : (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-q)
          * (Work.FTS.StrongPersist.H6Pair6Aux.Abnd α i θ) ^ 2)
        ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun θ : ℝ => 4 * (Real.sin (2 * θ)) ^ (2 * (α / 5) - q)) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      exact Abnd_rpow_mul_sq_le hα0 hα1 hi hq1 hθ
    calc (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
          * (Work.FTS.StrongPersist.H6Pair6Aux.Abnd α i θ) ^ 2)
        = ∫ θ, (Real.sin (2 * θ)) ^ (-q)
            * (Work.FTS.StrongPersist.H6Pair6Aux.Abnd α i θ) ^ 2
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) := rfl
      _ ≤ ∫ θ, 4 * (Real.sin (2 * θ)) ^ (2 * (α / 5) - q)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
          MeasureTheory.integral_mono_of_nonneg hnn hmaj hle
      _ = 4 * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 * (α / 5) - q)) :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ 4 * (100 / (2 * (α / 5) - q + 1)) :=
          mul_le_mul_of_nonneg_left hval (by norm_num)

end Work.FTS.StrongPersist.H6Pair6Aux.T45Aux
