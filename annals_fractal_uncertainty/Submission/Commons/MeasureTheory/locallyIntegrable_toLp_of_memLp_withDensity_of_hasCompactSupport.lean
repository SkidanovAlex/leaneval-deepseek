import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Submission.Commons.MeasureTheory.integrableOn_volume_of_memLp_withDensity_exp_neg

namespace Commons.MeasureTheory

theorem locallyIntegrable_toLp_of_memLp_withDensity_of_hasCompactSupport {d : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (Fin d → ℂ) → ℝ} (hFc : Continuous F) (hFpos : ∀ x, 0 < F x)
    {f : (Fin d → ℂ) → E}
    (hf : MeasureTheory.MemLp f 2
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)).withDensity
        (fun x => ENNReal.ofReal (F x))))
    (hfs : HasCompactSupport f) :
    MeasureTheory.LocallyIntegrable ((hf.toLp f) : (Fin d → ℂ) → E)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) := by
  -- The compact-support hypothesis is not needed for the conclusion, but we reference it
  -- to keep the statement's hypotheses explicit.
  have _hfs := hfs
  -- The weight `ENNReal.ofReal ∘ F` is positive everywhere, hence a.e. non-zero; therefore
  -- Lebesgue measure and the weighted measure have the same `ae` filter.
  have hdm : AEMeasurable (fun x : Fin d → ℂ => ENNReal.ofReal (F x))
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) :=
    (ENNReal.measurable_ofReal.comp hFc.measurable).aemeasurable
  have hdne : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)),
      ENNReal.ofReal (F x) ≠ 0 :=
    Filter.Eventually.of_forall fun x => ne_of_gt (ENNReal.ofReal_pos.mpr (hFpos x))
  have hae : (hf.toLp f : (Fin d → ℂ) → E)
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ))] f :=
    (MeasureTheory.withDensity_ae_eq hdm hdne).mp hf.coeFn_toLp
  -- `f` itself is locally integrable w.r.t. Lebesgue measure: on each compact set the density
  -- is bounded below by a positive constant.
  have hloc : MeasureTheory.LocallyIntegrable f
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) := by
    rw [MeasureTheory.locallyIntegrable_iff]
    intro K hK
    set φ : (Fin d → ℂ) → ℝ := fun z => -Real.log (F z) with hφdef
    have hφc : Continuous φ := (hFc.log (fun z => ne_of_gt (hFpos z))).neg
    have hden : (fun z : Fin d → ℂ => ENNReal.ofReal (Real.exp (-(φ z))))
        = (fun x : Fin d → ℂ => ENNReal.ofReal (F x)) := by
      funext z
      have h : Real.exp (-(φ z)) = F z := by
        rw [hφdef]
        simp only [neg_neg, Real.exp_log (hFpos z)]
      rw [h]
    have hV : MeasureTheory.MemLp f 2
        ((MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)).withDensity
          (fun z => ENNReal.ofReal (Real.exp (-(φ z))))) := by
      rw [hden]
      exact hf
    exact integrableOn_volume_of_memLp_withDensity_exp_neg hφc hV hK
  exact hloc.congr hae.symm

end Commons.MeasureTheory