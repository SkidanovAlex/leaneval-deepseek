import Mathlib
import Submission.Work.EKLC6Core.ent_le_HcondSig_of_gen
import Submission.Work.EKLC6Core.HcondSig_le_growth_plain
import Submission.Work.EKLC6Core.HcondSig_le_lintegral_atomInfo
import Submission.Work.EKLC6Core.growth_le_atomInfo
import Submission.Work.EKLC6Core.lintegral_atomInfo_le

namespace Work.EKLC6Core

theorem HcondSig_eq_growth_plaque {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3}
    (hL : Work.EKLContract.IsLeafwise μ (Work.EKLC6Core.Uminus t) ν X')
    (hcov : Work.EKLC6Core.ACovariant ν X'') (hX'' : μ (X''ᶜ) = 0)
    (hErg : Work.EKLContract.IsAErgodic μ)
    (hmeas : Measurable (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t))
    (hint : MeasureTheory.Integrable (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t) μ)
    {A : MeasurableSpace Work.EKLContract.X3} {Z : Set Work.EKLContract.X3}
    (hplq : Work.EKLContract.IsPlaqueAlgebra (Work.EKLC6Core.Uminus t) Z A) (hZ : μ Zᶜ = 0)
    (hdec : MeasurableSpace.comap (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A ≤ A)
    (hψ : MeasureTheory.Integrable (fun x : Work.EKLContract.X3 => Real.log
      ((ν x (Work.EKLContract.shape A (Work.EKLC6Core.Uminus t) x)).toReal)) μ) :
    @Work.EKLC6Core.HcondSig Work.EKLContract.X3 Work.EKLContract.instMeasurableSpaceX3 μ A
        (MeasurableSpace.comap (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A)
      = ENNReal.ofReal (∫ x, Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t x ∂μ) := by
  obtain ⟨hHoro, hcontr⟩ := Work.EKLC6Core.uminus_isHoro t
  refine le_antisymm ?_ ?_
  · -- `≤`: the shape-comparison half of Pisa 7.34/7.35
    exact Work.EKLC6Core.HcondSig_le_growth_plain (μ := μ) (ν := ν) (X' := X') (X'' := X'')
      t hErg hL hcov hX'' hmeas hint hplq hZ hdec
  · -- `≥`: the two halves `ofReal (∫ growthFun) ≤ ∫⁻ ofReal atomInfo ≤ HcondSig`
    calc ENNReal.ofReal (∫ x, Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t x ∂μ)
        ≤ ∫⁻ x, ENNReal.ofReal
            (Work.EKLC6Core.atomInfo A (Work.EKLC6Core.Uminus t) ν t x) ∂μ :=
          Work.EKLC6Core.growth_le_atomInfo (μ := μ) (U := Work.EKLC6Core.Uminus t)
            (ν := ν) (X' := X') (X'' := X'') hL hHoro hcov hX'' t hcontr hErg.1 hmeas hint
            hplq hdec hZ hψ
      _ ≤ @Work.EKLC6Core.HcondSig Work.EKLContract.X3 Work.EKLContract.instMeasurableSpaceX3 μ A
            (MeasurableSpace.comap (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A) :=
          Work.EKLC6Core.lintegral_atomInfo_le (μ := μ) (U := Work.EKLC6Core.Uminus t)
            (ν := ν) (X' := X') (X'' := X'') t hL hHoro hcov hX'' hErg.1 hplq hdec hZ

end Work.EKLC6Core
