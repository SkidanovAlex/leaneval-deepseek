import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.lintegral_atomInfo_le_nocov
import Submission.Work.EKLC6Core.ent_ge_HcondSig_le

namespace Work.EKLC6Core

open MeasureTheory Filter Topology
open scoped ENNReal

/-- `∫ atomInfo ≤ HcondSig μ A (comap T A) ≤ ent μ T < ⊤`. -/
theorem lintegral_atomInfo_ne_top_of_ent_ne_top
    {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    {U : Subgroup Work.EKLContract.SL3}
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hU : Work.EKLContract.IsHoro U)
    (hL : Work.EKLContract.IsLeafwise μ U ν X')
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    {A : MeasurableSpace Work.EKLContract.X3} {Z : Set Work.EKLContract.X3}
    (hplaq : Work.EKLContract.IsPlaqueAlgebra U Z A)
    (hZ : μ Zᶜ = 0)
    (hdec : MeasurableSpace.comap
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A ≤ A)
    (hfinent : @Work.EKLContract.ent Work.EKLContract.X3
      Work.EKLContract.instMeasurableSpaceX3 μ
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) ≠ ⊤) :
    ∫⁻ x, ENNReal.ofReal (Work.EKLC6Core.atomInfo A U ν t x) ∂μ ≠ ⊤ := by
  have hle :=
    lintegral_atomInfo_le_nocov (μ := μ) (U := U) (ν := ν) (X' := X') t hL hU hmp
      (A := A) (Z := Z) hplaq hdec hZ
  have hsig :=
    ent_ge_HcondSig_le (X := Work.EKLContract.X3)
      (mX := Work.EKLContract.instMeasurableSpaceX3) μ
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) hmp A hdec
  have hlt : MeasureTheory.lintegral μ
      (fun x => ENNReal.ofReal (Work.EKLC6Core.atomInfo A U ν t x)) < ⊤ :=
    lt_of_le_of_lt (le_trans hle hsig) (lt_top_iff_ne_top.mpr hfinent)
  exact ne_of_lt hlt

end Work.EKLC6Core
