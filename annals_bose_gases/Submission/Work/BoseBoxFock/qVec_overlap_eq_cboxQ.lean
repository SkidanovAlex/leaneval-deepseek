import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.qVecFrameWeighted
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory

/-- The complex twin of `Work.BoseBoxFock.integral_star_thetaFun_mul`: for any `u : E3 → ℂ`,

    `∫ conj (θ_Λ) · u = ∫_Λ u`.

Since `θ_Λ = 1_Λ` is real, `conj θ_Λ = θ_Λ`, and `θ_Λ · u` is the ℂ-indicator of the box
against `u`. -/
theorem integral_star_thetaFun_mul_c {ℓ : ℝ} (u : EuclideanSpace ℝ (Fin 3) → ℂ) :
    (∫ x : EuclideanSpace ℝ (Fin 3),
        (starRingEnd ℂ) (Work.BoseK15.corpusBox.thetaFun ℓ x) * u x)
      = ∫ y in Work.BoseK15.corpusBox.boxL ℓ, u y := by
  rw [← MeasureTheory.integral_indicator (Work.BoseK15.corpusBox.boxL_measurableSet ℓ) (f := u)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  beta_reduce
  rw [star_thetaFun]
  by_cases hx : x ∈ Work.BoseK15.corpusBox.boxL ℓ
  · rw [Work.BoseB4.BoxData.thetaFun_apply, if_pos hx, Set.indicator_of_mem hx, one_mul]
  · rw [Work.BoseB4.BoxData.thetaFun_apply, if_neg hx, Set.indicator_of_notMem hx, zero_mul]

theorem qVec_overlap_eq_cboxQ {ℓ : ℝ} (hℓ : 0 < ℓ) (k : EuclideanSpace ℝ (Fin 3))
    {u : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hum : Measurable u) (hub : ∃ C : ℝ, ∀ x, ‖u x‖ ≤ C)
    (hus : Function.support u ⊆ Work.BoseK15.corpusBox.boxL ℓ) :
    (∫ x : EuclideanSpace ℝ (Fin 3),
        (starRingEnd ℂ) (Work.BoseK15.corpusBox.qVec ℓ k x) * u x)
      = ∫ x : EuclideanSpace ℝ (Fin 3),
          (starRingEnd ℂ) (Work.BoseK15.corpusBox.modeVec ℓ k x)
            * Work.BoseBoxFock.cboxQ ℓ u x := by
  classical
  have hu : Integrable u :=
    integrable_of_bounded_support (volume_boxL_lt_top ℓ hℓ) hum hub hus
  have hI1 : Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
      (starRingEnd ℂ) (Work.BoseK15.corpusBox.modeVec ℓ k x) * u x) :=
    Integrable.bdd_mul hu
      ((Complex.continuous_conj.comp (continuous_modeVec ℓ k)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by
        rw [starRingEnd_apply, norm_star]; exact norm_modeVec_le ℓ k x)
  have hI2 : Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
      (starRingEnd ℂ) (Work.BoseK15.corpusBox.thetaFun ℓ x) * u x) :=
    Integrable.bdd_mul hu
      ((Complex.continuous_conj.measurable.comp (measurable_thetaFun ℓ)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by
        rw [starRingEnd_apply, norm_star]; exact norm_thetaFun_le ℓ x)
  have hI0 : Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
      (starRingEnd ℂ) (Work.BoseK15.corpusBox.modeVec ℓ k x)) := by
    refine integrable_of_bounded_support (volume_boxL_lt_top ℓ hℓ)
      ((Complex.continuous_conj.comp (continuous_modeVec ℓ k)).measurable)
      ⟨(Real.sqrt Submission.BoseGases.chiNormSq)⁻¹, fun x => ?_⟩ ?_
    · rw [starRingEnd_apply, norm_star]; exact norm_modeVec_le ℓ k x
    · intro x hx
      rw [Function.mem_support] at hx
      by_contra hcon
      refine hx ?_
      rw [star_modeVec_eq, chiLam_eq_chiScale, chiScale_eq_zero_of_notMem hℓ hcon,
        Complex.ofReal_zero, mul_zero]
  have hI3 : Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
      (starRingEnd ℂ) (Work.BoseK15.corpusBox.modeVec ℓ k x)
        * Set.indicator (Work.BoseK15.corpusBox.boxL ℓ) (fun _ : EuclideanSpace ℝ (Fin 3) => (1 : ℂ)) x) :=
    hI0.congr (Filter.Eventually.of_forall fun x => (star_modeVec_mul_ind hℓ k x).symm)
  -- `qVec = modeVec − χ̂(ℓk)·θ`, so `conj(qVec)·u = conj(modeVec)·u − χ̂(ℓk)·(conj θ·u)`.
  have hA : (∫ x : EuclideanSpace ℝ (Fin 3),
        (starRingEnd ℂ) (Work.BoseK15.corpusBox.qVec ℓ k x) * u x)
      = (∫ x : EuclideanSpace ℝ (Fin 3),
          (starRingEnd ℂ) (Work.BoseK15.corpusBox.modeVec ℓ k x) * u x)
        - ((Work.BoseK15.corpusBox.hatChi (ℓ • k) : ℝ) : ℂ)
          * (∫ y in Work.BoseK15.corpusBox.boxL ℓ, u y) := by
    rw [show (∫ x : EuclideanSpace ℝ (Fin 3),
          (starRingEnd ℂ) (Work.BoseK15.corpusBox.qVec ℓ k x) * u x)
        = ∫ x : EuclideanSpace ℝ (Fin 3),
            ((starRingEnd ℂ) (Work.BoseK15.corpusBox.modeVec ℓ k x) * u x
              - ((Work.BoseK15.corpusBox.hatChi (ℓ • k) : ℝ) : ℂ)
                * ((starRingEnd ℂ) (Work.BoseK15.corpusBox.thetaFun ℓ x) * u x)) from
      integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)]
    · rw [integral_sub hI1 (hI2.const_mul _), integral_const_mul, integral_star_thetaFun_mul_c]
    · beta_reduce
      rw [Work.BoseB4.BoxData.qVec_apply, map_sub, map_mul, Complex.conj_ofReal]; ring
  -- The scalar bookkeeping `ℓ⁻³(∫_Λ u)·ℓ³χ̂(ℓk) = χ̂(ℓk)·∫_Λ u`.
  have hkey : (((ℓ : ℂ) ^ 3)⁻¹ * (∫ y in Work.BoseK15.corpusBox.boxL ℓ, u y))
      * ((ℓ ^ 3 * Work.BoseK15.corpusBox.hatChi (ℓ • k) : ℝ) : ℂ)
      = ((Work.BoseK15.corpusBox.hatChi (ℓ • k) : ℝ) : ℂ)
        * (∫ y in Work.BoseK15.corpusBox.boxL ℓ, u y) := by
    have hL3 : ((ℓ ^ 3 : ℝ) : ℂ) = ((ℓ : ℂ)) ^ 3 := by push_cast; ring
    have hne : ((ℓ : ℂ)) ^ 3 ≠ 0 :=
      pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr (ne_of_gt hℓ))
    have hinv : ((ℓ : ℂ) ^ 3)⁻¹ * ((ℓ ^ 3 : ℝ) : ℂ) = 1 := by
      rw [hL3, inv_mul_cancel₀ hne]
    calc (((ℓ : ℂ) ^ 3)⁻¹ * (∫ y in Work.BoseK15.corpusBox.boxL ℓ, u y))
          * ((ℓ ^ 3 * Work.BoseK15.corpusBox.hatChi (ℓ • k) : ℝ) : ℂ)
        = ((ℓ : ℂ) ^ 3)⁻¹ * (∫ y in Work.BoseK15.corpusBox.boxL ℓ, u y)
          * (((ℓ ^ 3 : ℝ) : ℂ) * ((Work.BoseK15.corpusBox.hatChi (ℓ • k) : ℝ) : ℂ)) := by
          rw [Complex.ofReal_mul]
      _ = (((ℓ : ℂ) ^ 3)⁻¹ * ((ℓ ^ 3 : ℝ) : ℂ))
          * ((∫ y in Work.BoseK15.corpusBox.boxL ℓ, u y)
              * ((Work.BoseK15.corpusBox.hatChi (ℓ • k) : ℝ) : ℂ)) := by ring
      _ = ((Work.BoseK15.corpusBox.hatChi (ℓ • k) : ℝ) : ℂ)
          * (∫ y in Work.BoseK15.corpusBox.boxL ℓ, u y) := by rw [hinv, one_mul]; ring
  -- `cboxQ u = u − ℓ⁻³(∫_Λ u)·1_Λ`, and `conj(modeVec)·1_Λ = conj(modeVec)`.
  have hB : (∫ x : EuclideanSpace ℝ (Fin 3),
        (starRingEnd ℂ) (Work.BoseK15.corpusBox.modeVec ℓ k x) * cboxQ ℓ u x)
      = (∫ x : EuclideanSpace ℝ (Fin 3),
          (starRingEnd ℂ) (Work.BoseK15.corpusBox.modeVec ℓ k x) * u x)
        - ((Work.BoseK15.corpusBox.hatChi (ℓ • k) : ℝ) : ℂ)
          * (∫ y in Work.BoseK15.corpusBox.boxL ℓ, u y) := by
    rw [show (∫ x : EuclideanSpace ℝ (Fin 3),
          (starRingEnd ℂ) (Work.BoseK15.corpusBox.modeVec ℓ k x) * cboxQ ℓ u x)
        = ∫ x : EuclideanSpace ℝ (Fin 3),
            ((starRingEnd ℂ) (Work.BoseK15.corpusBox.modeVec ℓ k x) * u x
              - (((ℓ : ℂ) ^ 3)⁻¹ * (∫ y in Work.BoseK15.corpusBox.boxL ℓ, u y))
                * ((starRingEnd ℂ) (Work.BoseK15.corpusBox.modeVec ℓ k x)
                    * Set.indicator (Work.BoseK15.corpusBox.boxL ℓ)
                        (fun _ : EuclideanSpace ℝ (Fin 3) => (1 : ℂ)) x)) from
      integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)]
    · rw [integral_sub hI1 (hI3.const_mul _), integral_const_mul,
        integral_star_modeVec_mul_ind hℓ k]
      exact congrArg (fun z => (∫ x : EuclideanSpace ℝ (Fin 3),
          (starRingEnd ℂ) (Work.BoseK15.corpusBox.modeVec ℓ k x) * u x) - z) hkey
    · beta_reduce
      simp only [cboxQ]
      ring
  rw [hA, hB]

end Work.BoseBoxFock
