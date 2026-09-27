import Mathlib
import Submission.Work.EKLContract.Defs

namespace Work.EKLProd

open MeasureTheory Filter

theorem condExp_mul_condExp_tower {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsFiniteMeasure μ]
    {mH mT : MeasurableSpace Work.EKLContract.X3}
    (halign : mH ≤ mT) (hmT : mT ≤ borel Work.EKLContract.X3)
    (g f : Work.EKLContract.X3 → ℝ)
    (hgmT : @Measurable Work.EKLContract.X3 ℝ mT (borel ℝ) g)
    (hf : @Measurable Work.EKLContract.X3 ℝ (borel Work.EKLContract.X3) (borel ℝ) f)
    (hfb : ∃ C, ∀ y, |f y| ≤ C) (hgb : ∃ C, ∀ y, |g y| ≤ C) :
    MeasureTheory.condExp mH μ (fun y => g y * MeasureTheory.condExp mT μ f y)
      =ᵐ[μ] MeasureTheory.condExp mH μ (fun y => g y * f y) := by
  obtain ⟨Cf, hCf⟩ := hfb
  obtain ⟨Cg, hCg⟩ := hgb
  -- g is strongly measurable with respect to mT
  have hg_sm : StronglyMeasurable[mT] g := hgmT.stronglyMeasurable
  -- f is integrable (bounded, measurable, finite measure)
  have hf_int : Integrable f μ :=
    Integrable.of_bound hf.aestronglyMeasurable (max Cf 0)
      (Filter.Eventually.of_forall (fun y => by
        rw [Real.norm_eq_abs]; exact le_trans (hCf y) (le_max_left _ _)))
  -- the product g * f is measurable and integrable
  have hgf_meas : @Measurable Work.EKLContract.X3 ℝ (borel Work.EKLContract.X3) (borel ℝ)
      (fun y => g y * f y) := (hgmT.mono hmT le_rfl).mul hf
  have hgf_int : Integrable (fun y => g y * f y) μ :=
    Integrable.of_bound hgf_meas.aestronglyMeasurable (max Cg 0 * max Cf 0)
      (Filter.Eventually.of_forall (fun y => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (le_trans (hCg y) (le_max_left _ _)) (le_trans (hCf y) (le_max_left _ _))
          (abs_nonneg _) (le_max_right _ _)))
  -- pull the mT-measurable factor g out of the mT-conditional expectation
  have hstep : condExp mT μ (fun y => g y * f y)
      =ᵐ[μ] fun y => g y * condExp mT μ f y :=
    condExp_mul_of_stronglyMeasurable_left hg_sm hgf_int hf_int
  -- replace g * condExp mT μ f by condExp mT μ (g * f), then apply the tower property
  calc condExp mH μ (fun y => g y * condExp mT μ f y)
      =ᵐ[μ] condExp mH μ (condExp mT μ (fun y => g y * f y)) :=
        condExp_congr_ae hstep.symm
    _ =ᵐ[μ] condExp mH μ (fun y => g y * f y) := condExp_condExp_of_le halign hmT

end Work.EKLProd
