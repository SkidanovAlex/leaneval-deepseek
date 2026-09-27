import Submission.Work.EKLC6Core.ent_le_growth_of_aerg
import Submission.Work.EKLC6Core.ent_le_growth_of_not_aerg
import Submission.Work.EKLC6Core.HcondSig_eq_growth_plaque

/-!
# The residual link `ofReal (hPart μ (aDiag t ·) P) ≤ HcondSig μ A (comap (aDiag t ·) A)`

This is the second half of the `c`-comparison (the first half is
`EKLC6Core.hPart_chain_le_of_atomSmall`).  Two ingredients are glued here.

* `ent_le_growth_of_growth`: `ent μ (aDiag t ·) ≤ ofReal (∫ growthFun)` for an `A`-ergodic `μ`,
  obtained by gluing the fleet's `T`-ergodic half (`ent_le_growth_of_aerg`) with its
  non-`T`-ergodic half (`ent_le_growth_of_not_aerg`, Pisa 7.19–7.24 ergodic-component reduction)
  by a case split — i.e. without going through the stale assembler `EKLC6Core/ent_le_growth.lean`.
* `EKLC6Core.HcondSig_eq_growth_plaque` (Pisa 7.34/7.35, shape comparison):
  `HcondSig μ A (comap (aDiag t ·) A) = ofReal (∫ growthFun)` for an `aDiag t`-descending plaque
  algebra `A`.

Together with `hPart μ T P ≤ ent μ T` (definitional, `ent` being the supremum over finite
partitions) this gives, for any finite partition `P`,

`ofReal (hPart μ (aDiag t ·) P) ≤ HcondSig μ A (comap (aDiag t ·) A)`.

For the atom-small `P` of EKL Prop. 9.2 the number `c := hPart μ (aDiag t ·) P` therefore meets
both hypotheses of `EKLC6Core.ent_le_ofReal_hPart_of_desc_subordinate_data`, yielding the target
for the `pastSig` presentation of `A`. -/

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- **The general (ergodic) inequality `ent ≤ ofReal (∫ growthFun)`, glued from the two halves.** -/
theorem ent_le_growth_of_growth {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hErg : Work.EKLContract.IsAErgodic μ)
    (hL : Work.EKLContract.IsLeafwise μ (Work.EKLC6Core.Uminus t) ν X')
    (hcov : Work.EKLC6Core.ACovariant ν X'') (hX'' : μ (X''ᶜ) = 0)
    (hmeas : Measurable (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t))
    (hint : MeasureTheory.Integrable (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t) μ) :
    Work.EKLContract.ent μ (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) ≤
      ENNReal.ofReal (∫ x, Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t x ∂μ) := by
  by_cases haerg : ∀ E : Set Work.EKLContract.X3, MeasurableSet E →
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) ⁻¹' E =ᵐ[μ] E →
      μ E = 0 ∨ μ Eᶜ = 0
  · exact Work.EKLC6Core.ent_le_growth_of_aerg t (hErg.1 t) haerg hL hcov hX'' hmeas hint
  · exact Work.EKLC6Core.ent_le_growth_of_not_aerg t hErg haerg hL hcov hX'' hmeas hint

/-- **The residual link.**  For any finite partition `P`,
`ofReal (hPart μ (aDiag t ·) P) ≤ HcondSig μ A (comap (aDiag t ·) A)`. -/
theorem ofReal_hPart_le_HcondSig_of_growth
    {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hErg : Work.EKLContract.IsAErgodic μ)
    (hL : Work.EKLContract.IsLeafwise μ (Work.EKLC6Core.Uminus t) ν X')
    (hcov : Work.EKLC6Core.ACovariant ν X'') (hX'' : μ (X''ᶜ) = 0)
    (hmeas : Measurable (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t))
    (hint : MeasureTheory.Integrable (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t) μ)
    {A : MeasurableSpace Work.EKLContract.X3} {Z : Set Work.EKLContract.X3}
    (hplq : Work.EKLContract.IsPlaqueAlgebra (Work.EKLC6Core.Uminus t) Z A) (hZ : μ Zᶜ = 0)
    (hdec : MeasurableSpace.comap
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A ≤ A)
    (hψ : MeasureTheory.Integrable (fun x : Work.EKLContract.X3 => Real.log
      ((ν x (Work.EKLContract.shape A (Work.EKLC6Core.Uminus t) x)).toReal)) μ)
    (P : @Work.EKLContract.FinPart Work.EKLContract.X3
      Work.EKLContract.instMeasurableSpaceX3) :
    ENNReal.ofReal (@Work.EKLContract.hPart Work.EKLContract.X3
        Work.EKLContract.instMeasurableSpaceX3 μ
        (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) P)
      ≤ @Work.EKLC6Core.HcondSig Work.EKLContract.X3
          Work.EKLContract.instMeasurableSpaceX3 μ A
          (MeasurableSpace.comap
            (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A) := by
  rw [HcondSig_eq_growth_plaque t (hErg.1 t) hL hcov hX'' hErg hmeas hint hplq hZ hdec hψ]
  have h1 : ENNReal.ofReal (@Work.EKLContract.hPart Work.EKLContract.X3
        Work.EKLContract.instMeasurableSpaceX3 μ
        (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) P)
      ≤ @Work.EKLContract.ent Work.EKLContract.X3
          Work.EKLContract.instMeasurableSpaceX3 μ
          (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) :=
    le_iSup (fun Q : @Work.EKLContract.FinPart Work.EKLContract.X3
      Work.EKLContract.instMeasurableSpaceX3 => ENNReal.ofReal
        (@Work.EKLContract.hPart Work.EKLContract.X3
          Work.EKLContract.instMeasurableSpaceX3 μ
          (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) Q)) P
  exact le_trans h1 (ent_le_growth_of_growth t hErg hL hcov hX'' hmeas hint)

end Work.EKLC6Core
