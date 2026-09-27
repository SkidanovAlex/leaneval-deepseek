import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.uminus_isHoro
import Submission.Work.EKLC6Core.covAlong
import Submission.Work.EKLC6Core.HcondSigFree.HcondSig_le_lintegral_atomInfo_mp
import Submission.Work.EKLC6Core.lintegral_atomInfo_le_ofReal_growth_along
import Submission.Work.EKLC6Core.growth_le_atomInfo_sandwich_along
import Submission.Work.EKLC6Core.lintegral_atomInfo_le_along
import Submission.Work.EKLC6Core.exists_good_set_plaque
import Submission.Work.EKLC6Core.aemeasurable_atomInfo

/-!
# `Work.EKLC6Core.HcondSig_eq_growth_along` — Pisa 7.34/7.35 with a single-`t` covariance

`Work.EKLC6Core.HcondSig_eq_growth_free` (Pisa 7.34/7.35, the shape comparison) takes
`hcov : ACovariant ν X''`, i.e. covariance at **every** `t : Fin 3 → ℝ`, which the frozen
contract `P_Leafwise` supplies only under `IsAInvariant μ`.  This is the same theorem with
`hcov` weakened to `Work.EKLC6Core.ACovariantAlong ν t X''` — the covariance at the integer
multiples of the *single* direction `t`, which `Work.EKLC6Core.acovariantAlong_of_leafwise`
produces from `MeasurePreserving (fun x => aDiag t • x) μ μ` + `IsLeafwise μ (Uminus t) ν X'`
alone.  The proof is the proof of `HcondSig_eq_growth_free` verbatim, with its four ingredients
replaced by their `_along` counterparts (all proved sorry-free):

* `HcondSigFree.HcondSig_le_lintegral_atomInfo_mp` (no covariance at all),
* `lintegral_atomInfo_le_ofReal_growth_along`,
* `growth_le_atomInfo_sandwich_along` (through `exists_good_set_plaque`),
* `lintegral_atomInfo_le_along`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

theorem HcondSig_eq_growth_along {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3}
    (hL : Work.EKLContract.IsLeafwise μ (Work.EKLC6Core.Uminus t) ν X')
    (hcov : Work.EKLC6Core.ACovariantAlong ν t X'') (hX'' : μ (X''ᶜ) = 0)
    (hmeas : Measurable (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t))
    (hint : MeasureTheory.Integrable (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t) μ)
    {A : MeasurableSpace Work.EKLContract.X3} {Z : Set Work.EKLContract.X3}
    (hplq : Work.EKLContract.IsPlaqueAlgebra (Work.EKLC6Core.Uminus t) Z A) (hZ : μ Zᶜ = 0)
    (hdec : MeasurableSpace.comap (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A ≤ A) :
    @Work.EKLC6Core.HcondSig Work.EKLContract.X3 Work.EKLContract.instMeasurableSpaceX3 μ A
        (MeasurableSpace.comap (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A)
      = ENNReal.ofReal (∫ x, Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t x ∂μ) := by
  have hU : IsHoro (Uminus t) := (uminus_isHoro t).1
  have hcontr : ∀ u ∈ Uminus t, Filter.Tendsto
      (fun n : ℕ => aDiag t ^ n * u * (aDiag t ^ n)⁻¹) Filter.atTop (nhds 1) :=
    (uminus_isHoro t).2
  refine le_antisymm ?_ ?_
  · -- Pisa 7.34/7.35: `HcondSig ≤ ∫⁻ ofReal atomInfo ≤ ofReal (∫ growthFun)`
    have h1 := HcondSigFree.HcondSig_le_lintegral_atomInfo_mp (μ := μ) (ν := ν) (X' := X')
      t hmp hL hplq hZ hdec
    have h2 := lintegral_atomInfo_le_ofReal_growth_along (μ := μ) (ν := ν)
      (X' := X') (X'' := X'') t hmp hL hcov hX'' hmeas hint ⟨A⟩ hplq hZ hdec
    exact le_trans h1 h2
  · -- Pisa 7.18/7.34 at the good times: `ofReal (∫ growthFun) ≤ ∫⁻ ofReal atomInfo ≤ HcondSig`
    obtain ⟨Y, δ, R, hYmeas, hδ, hR, hY, hvisit⟩ :=
      exists_good_set_plaque (μ := μ) t hmp hplq hZ
    have hmeas_atom : AEMeasurable (atomInfo A (Uminus t) ν t) μ :=
      atomInfo_aemeasurable (μ := μ) (U := Uminus t) (ν := ν) (X' := X') t hL hU hplq
    have h3 := growth_le_atomInfo_sandwich_along (μ := μ) (U := Uminus t) (ν := ν)
      (X' := X') (X'' := X'') t hL hU hcov hX'' hmp hint hcontr hplq hdec hZ hmeas_atom
      hYmeas hδ hR hY hvisit
    have h4 := lintegral_atomInfo_le_along (μ := μ) (U := Uminus t) (ν := ν)
      (X' := X') (X'' := X'') (t := t) hL hU hcov hX'' hmp hplq hdec hZ
    exact le_trans h3 h4

end Work.EKLC6Core

end
