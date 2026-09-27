import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.lintegral_atomInfo_le_mp
import Submission.Work.EKLC6Core.lintegral_growthFun_le_lintegral_atomInfo_uij
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLC6Core.uminus_isHoro
import Submission.Work.EKLC6Core.measurable_growthFun
import Submission.Work.EKLCompLeaf.fixRadon
import Submission.Work.EKLC6Core.lintegral_atomInfo_le_nocov
import Submission.Work.EKLC6Core.aeStronglyMeasurable_growthFun
import Submission.Work.EKLC6Core.ae_nonneg_growthFun_of_contracted
import Submission.Work.EKLC6Core.ent_ge_HcondSig_le
import Submission.Work.EKLC6Core.lintegral_atomInfo_ne_top_of_ent_ne_top

/-!
# `Work.EKLC6Core.integrable_growthFun_uminus_of_plaque`

**Integrability of the entropy contribution of the stable horospherical subgroup** (Pisa
7.6/7.18 together with Ruelle's bound for the diagonal element of `SL₃(ℝ)/SL₃(ℤ)`).

For a probability `μ` on `X3` preserved by `T = (aDiag t ·)`, a leaf-wise system `ν` for the
stable horospherical subgroup `Uminus t` (the join of the root groups `Uij` with `t i < t j`),
an `aDiag t ·`-descending plaque algebra `A` carried on a conull set `Z`, and the finiteness of
the KS entropy `ent μ (aDiag t ·)`, the pointwise information

`growthFun (Uminus t) ν t x = -log (ν x (conjBox (Uminus t) t))`

is `μ`-integrable.  This is the finiteness half of the identification of the Kolmogorov-Sinai
entropy with the Birkhoff average of `growthFun`; it is what allows the `ℝ≥0∞`-valued
computation to be converted into a Bochner integral
(`MeasureTheory.lintegral_ofReal_ne_top_iff_integrable`).

## The argument

Every step is an almost-everywhere statement, so no *global* measurability of `x ↦ ν x` is
needed -- and none is available, since `IsLeafwise` makes `ν` a Radon family only on the conull
domain `X'`.

1. *Finiteness of the entropy contribution of the plaque algebra.*  The `≤` half of the shape
   comparison (Pisa 7.34/7.35) in its covariance-free form
   `EKLC6Core.lintegral_atomInfo_le_nocov` gives

     `∫⁻ ofReal (atomInfo A (Uminus t) ν t) ≤ HcondSig μ A (comap T A)`,

   while `EKLC6Core.ent_ge_HcondSig_le` (Pisa 7.40) gives
   `HcondSig μ A (comap T A) ≤ ent μ T < ⊤`.  Packaged as
   `EKLC6Core.lintegral_atomInfo_ne_top_of_ent_ne_top`.

2. *Finiteness transfer* (Pisa 7.18/7.34; the lemma
   `lintegral_growthFun_le_lintegral_atomInfo_horo_ae` proved in this file below).  The
   a.e. coboundary identity of Pisa 7.34,

     `atomInfo x = ψ (T x) - ψ x + growthFun (T x)`,   `ψ = log (ν x (shape A (Uminus t) x))`,

   pushes the finiteness of the right hand side of step 1 back onto `growthFun`:

     `∫⁻ ofReal (growthFun (Uminus t) ν t) ≤ ∫⁻ ofReal (atomInfo A (Uminus t) ν t)`,

   hence `∫⁻ ofReal growthFun < ⊤`.  The single-`t` covariance required by the coboundary
   identity is not a hypothesis: it is produced from the leaf-wise system alone by
   `EKLC6Core.per_t_covariance_mp` (Pisa 7.16/7.17, the flower argument).  The only place where
   measurability enters is the invariance of `∫⁻` under the measure-preserving shift, and
   there the a.e. strong measurability of `growthFun`
   (`EKLC6Core.aeStronglyMeasurable_growthFun`, obtained by correcting `ν` off the conull set
   `X'`) suffices.  This is why the transfer lemma below needs no measurability hypothesis at
   all, strengthening `EKLC6Core.lintegral_growthFun_le_lintegral_atomInfo_horo`.

3. *Assembly.*  `growthFun` is a.e. non-negative for a contracted `U`
   (`EKLC6Core.ae_nonneg_growthFun_of_contracted`: `conjBox U t` ⊆ `Box1 U` and
   `ν x (Box1 U) = 1`), so `MeasureTheory.hasFiniteIntegral_iff_ofReal` converts the finiteness
   of the `ℝ≥0∞`-integral into `HasFiniteIntegral`, and
   `aeStronglyMeasurable_growthFun` supplies the other half of `Integrable`.

The covariance hypothesis `hcov : ACovariant ν X''` of the statement is not needed: the
covariance-free forms of steps 1 and 2 suffice.  Likewise `hX''` is unused.
-/

open MeasureTheory Filter Topology
open scoped ENNReal MeasureTheory

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- **Finiteness transfer for a contracted horospherical subgroup, with a.e. measurability only.**
If the leaf-wise system `ν` lives over the subgroup `U` contracted by `aDiag t` (so that
`conjBox U t` ⊆ `Box1 U`), the plaque algebra `A` is `T`-descending on a conull
set and `∫⁻ ofReal (atomInfo A U ν t) ≠ ⊤`, then the entropy contribution has no larger
`ℝ≥0∞`-integral:

  `∫⁻ ofReal (growthFun U ν t) ≤ ∫⁻ ofReal (atomInfo A U ν t)`.

This is `EKLC6Core.lintegral_growthFun_le_lintegral_atomInfo_horo` with the hypothesis
`Measurable (growthFun U ν t)` weakened to nothing: the only use of global measurability there is
the invariance of the `ℝ≥0∞`-integral under the measure-preserving shift `T`, for which a.e.
strong measurability (`EKLC6Core.aeStronglyMeasurable_growthFun`, available for every leaf-wise
system because `ν` is unconstrained only off the conull domain `X'`) is enough. -/
theorem lintegral_growthFun_le_lintegral_atomInfo_horo_ae
    {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    {U : Subgroup Work.EKLContract.SL3}
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hU : Work.EKLContract.IsHoro U)
    (hcontr : ∀ u ∈ U, Filter.Tendsto
      (fun n : ℕ => Work.EKLContract.aDiag t ^ n * u * (Work.EKLContract.aDiag t ^ n)⁻¹)
      Filter.atTop (nhds 1))
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    (hL : Work.EKLContract.IsLeafwise μ U ν X')
    {A : MeasurableSpace Work.EKLContract.X3} {Z : Set Work.EKLContract.X3}
    (hplaq : Work.EKLContract.IsPlaqueAlgebra U Z A)
    (hdec : MeasurableSpace.comap
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A ≤ A)
    (hZ : μ Zᶜ = 0)
    (hfin : ∫⁻ x, ENNReal.ofReal (Work.EKLC6Core.atomInfo A U ν t x) ∂μ ≠ ⊤) :
    ∫⁻ x, ENNReal.ofReal (Work.EKLC6Core.growthFun U ν t x) ∂μ
      ≤ ∫⁻ x, ENNReal.ofReal (Work.EKLC6Core.atomInfo A U ν t x) ∂μ := by
  classical
  letI : MeasurableSpace Work.EKLContract.X3 := Work.EKLContract.instMeasurableSpaceX3
  have hg_nn : 0 ≤ᵐ[μ] (fun x => Work.EKLC6Core.atomInfo A U ν t x) :=
    Filter.Eventually.of_forall
      (fun x => Work.EKLC6Core.atomInfo_nonneg_mp (U := U) (ν := ν) (t := t) hdec x)
  have hf_nn : 0 ≤ᵐ[μ] (fun x => Work.EKLC6Core.growthFun U ν t x) :=
    Work.EKLC6Core.ae_nonneg_growthFun_of_contracted (μ := μ) (U := U) (ν := ν) (X' := X') t hU hcontr hL
  have hg_aemeas : AEMeasurable (fun x => Work.EKLC6Core.atomInfo A U ν t x) μ :=
    Work.EKLC6Core.atomInfo_aemeasurable (μ := μ) (U := U) (ν := ν) (X' := X') t hL hU hplaq
  have hg_int : MeasureTheory.Integrable (fun x => Work.EKLC6Core.atomInfo A U ν t x) μ :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hg_aemeas.aestronglyMeasurable hg_nn).mp
      hfin
  have hψ : AEMeasurable
      (fun y => Real.log ((ν y (Work.EKLContract.shape A U y)).toReal)) μ :=
    Real.measurable_log.comp_aemeasurable
      ((Work.EKLC6Core.aemeasurable_shape_mass_two (μ := μ) (U := U) (ν := ν) (X' := X')
        t hL hU hplaq).1)
  have hcov := Work.EKLC6Core.per_t_covariance_mp (U := U) hU hL t hmp hcontr
  have hid := Work.EKLC6Core.atomInfo_ae_eq_single_alt (μ := μ) (U := U) (ν := ν) (X' := X')
    (t := t) hL hU hmp hcov hplaq hZ
  have hkey := Work.EKLC6Core.lgla_ofReal_comp_le_lintegral_of_coboundary (μ := μ)
    (T := fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)
    hmp hg_int hg_nn hψ hf_nn hid
  have hshift : ∫⁻ x, ENNReal.ofReal
        (Work.EKLC6Core.growthFun U ν t (Work.EKLContract.aDiag t • x)) ∂μ
      = ∫⁻ x, ENNReal.ofReal (Work.EKLC6Core.growthFun U ν t x) ∂μ := by
    have hAg : AEMeasurable
        (fun y : Work.EKLContract.X3 => ENNReal.ofReal (Work.EKLC6Core.growthFun U ν t y))
        (Measure.map (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ) := by
      rw [hmp.map_eq]
      exact AEMeasurable.ennreal_ofReal
        ((Work.EKLC6Core.aeStronglyMeasurable_growthFun hU hL t).aemeasurable)
    have h1 := (MeasureTheory.lintegral_map'
      (μ := μ) (g := fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) hAg
      hmp.aemeasurable).symm
    rw [hmp.map_eq] at h1
    exact h1
  rw [← hshift]
  exact hkey

/-- **Integrability of the entropy contribution of `Uminus t`** (Pisa 7.6/7.18, Ruelle).
See the module docstring for the three-step argument. -/
theorem integrable_growthFun_uminus_of_plaque
    {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hL : Work.EKLContract.IsLeafwise μ (Work.EKLC6Core.Uminus t) ν X')
    (hcov : Work.EKLC6Core.ACovariant ν X'') (hX'' : μ X''ᶜ = 0)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    {A : MeasurableSpace Work.EKLContract.X3} {Z : Set Work.EKLContract.X3}
    (hplq : Work.EKLContract.IsPlaqueAlgebra (Work.EKLC6Core.Uminus t) Z A)
    (hZ : μ Zᶜ = 0)
    (hdec : MeasurableSpace.comap
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A ≤ A)
    (hfinent : @Work.EKLContract.ent Work.EKLContract.X3
      Work.EKLContract.instMeasurableSpaceX3 μ
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) ≠ ⊤) :
    MeasureTheory.Integrable
      (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t) μ := by
  have hU : Work.EKLContract.IsHoro (Work.EKLC6Core.Uminus t) :=
    (Work.EKLC6Core.uminus_isHoro t).1
  have hcontr : ∀ u ∈ Work.EKLC6Core.Uminus t, Filter.Tendsto
      (fun n : ℕ => Work.EKLContract.aDiag t ^ n * u * (Work.EKLContract.aDiag t ^ n)⁻¹)
      Filter.atTop (nhds 1) :=
    (Work.EKLC6Core.uminus_isHoro t).2
  have hfinA : ∫⁻ x, ENNReal.ofReal
      (Work.EKLC6Core.atomInfo A (Work.EKLC6Core.Uminus t) ν t x) ∂μ ≠ ⊤ :=
    Work.EKLC6Core.lintegral_atomInfo_ne_top_of_ent_ne_top (μ := μ) (U := Work.EKLC6Core.Uminus t) (ν := ν)
      (X' := X') t hU hL hmp hplq hZ hdec hfinent
  have hle : ∫⁻ x, ENNReal.ofReal
        (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t x) ∂μ
      ≤ ∫⁻ x, ENNReal.ofReal
        (Work.EKLC6Core.atomInfo A (Work.EKLC6Core.Uminus t) ν t x) ∂μ :=
    lintegral_growthFun_le_lintegral_atomInfo_horo_ae (μ := μ)
      (U := Work.EKLC6Core.Uminus t) (ν := ν) (X' := X')
      t hU hcontr hmp hL hplq hdec hZ hfinA
  have hlt : ∫⁻ x, ENNReal.ofReal
      (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t x) ∂μ < ⊤ :=
    lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr hfinA)
  have hnn := Work.EKLC6Core.ae_nonneg_growthFun_of_contracted (μ := μ) (U := Work.EKLC6Core.Uminus t)
    (ν := ν) (X' := X') t hU hcontr hL
  have hae := Work.EKLC6Core.aeStronglyMeasurable_growthFun (μ := μ) hU hL t
  exact ⟨hae, (MeasureTheory.hasFiniteIntegral_iff_ofReal hnn).mpr hlt⟩

end Work.EKLC6Core

end
