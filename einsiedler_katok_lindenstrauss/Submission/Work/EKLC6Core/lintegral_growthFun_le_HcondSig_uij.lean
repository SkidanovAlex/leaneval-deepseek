import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.EntSig
import Submission.Work.EKLC6Core.growth_le_HcondSig_mp
import Submission.Work.EKLC6Core.exists_good_set_plaque
import Submission.Work.EKLC6Core.lintegral_atomInfo_le_nocov
import Submission.Work.EKLC6Core.HcondSig_le_lintegral_atomInfo_horo
import Submission.Work.EKLC6Core.HaarPlan
import Submission.Work.EKLC6Core.per_t_covariance_mp
import Submission.Work.EKLC6Core.aeStronglyMeasurable_growthFun
import Submission.Work.EKLC6Core.Growth
import Submission.Work.EKLC6Core.box_conjBox_subset
import Submission.Work.EKLC6Core.lintegral_ofReal_comp_le_of_coboundary

namespace Work.EKLC6Core

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.ambiguousOpen false

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

noncomputable section

theorem lintegral_growthFun_le_HcondSig_uij {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    {i j : Fin 3} (hij : i ≠ j) (hlt : t i < t j)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    (hL : Work.EKLContract.IsLeafwise μ (Work.EKLContract.Uij hij) ν X')
    {A : MeasurableSpace Work.EKLContract.X3} {Z : Set Work.EKLContract.X3}
    (hplq : Work.EKLContract.IsPlaqueAlgebra (Work.EKLContract.Uij hij) Z A)
    (hZ : μ Zᶜ = 0)
    (hdec : MeasurableSpace.comap
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A ≤ A) :
    ∫⁻ x, ENNReal.ofReal (Work.EKLC6Core.growthFun (Work.EKLContract.Uij hij) ν t x) ∂μ
      ≤ @Work.EKLC6Core.HcondSig Work.EKLContract.X3 Work.EKLContract.instMeasurableSpaceX3 μ A
          (MeasurableSpace.comap (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A) := by
  classical
  letI : MeasurableSpace X3 := instMeasurableSpaceX3
  have hU : IsHoro (Uij hij) := Lemmas.isHoro_Uij hij
  have hcontr : ∀ u ∈ Uij hij,
      Filter.Tendsto (fun n : ℕ => aDiag t ^ n * u * (aDiag t ^ n)⁻¹) Filter.atTop (nhds 1) :=
    tendsto_conj_mem_Uij t hij hlt
  -- the a.e. covariance, from Pisa 7.16 (flower argument)
  obtain ⟨N, hN, hcovN⟩ := per_t_covariance_mp (U := Uij hij) hU hL t hmp hcontr
  have hcov : ∃ N : Set X3, μ N = 0 ∧ ∀ x : X3, x ∉ N → x ∈ X' → aDiag t • x ∈ X' →
      ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
        ν (aDiag t • x) = c • (ν x).map (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) :=
    ⟨N, hN, hcovN⟩
  -- the pointwise identity of Pisa 7.34
  have hid := atomInfo_ae_eq_single_alt (t := t) hL hU hmp hcov hplq hZ
  -- a.e. measurability of the two shape masses and of `atomInfo`
  obtain ⟨hmassV, hmassW⟩ := aemeasurable_shape_mass_two (t := t) hL hU hplq
  have hAI_aem : AEMeasurable (fun x : X3 => atomInfo A (Uij hij) ν t x) μ := by
    change AEMeasurable (fun x : X3 => -Real.log
      (((ν x) (shape A (Uij hij) x)).toReal /
        (((ν x) (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A)
          (Uij hij) x)).toReal))) μ
    exact (((hmassV.div hmassW)).log).neg
  have ha_nn : 0 ≤ᵐ[μ] (fun x : X3 => atomInfo A (Uij hij) ν t x) :=
    Filter.Eventually.of_forall
      (fun x => atomInfo_nonneg_mp (U := Uij hij) (ν := ν) (t := t) hdec x)
  have hψ_aem : AEMeasurable
      (fun y : X3 => Real.log (((ν y) (shape A (Uij hij) y)).toReal)) μ :=
    hmassV.log
  -- `growthFun ≥ 0` a.e. (the contracted box sits inside `B₁^U`)
  have hsub : conjBox (Uij hij) t ⊆ Box1 (Uij hij) := (box_conjBox_subset hU hcontr).1
  have hX' : ∀ᵐ x ∂μ, x ∈ X' := by rw [MeasureTheory.ae_iff]; exact hL.conull
  have hgnn : 0 ≤ᵐ[μ] (fun x : X3 => growthFun (Uij hij) ν t x) := by
    filter_upwards [hX'] with x hx
    have hle1 : ν x (conjBox (Uij hij) t) ≤ 1 :=
      (measure_mono hsub).trans_eq (hL.normalised x hx)
    have hle1' : (ν x (conjBox (Uij hij) t)).toReal ≤ 1 :=
      le_trans (ENNReal.toReal_mono (by simp) hle1) (by simp)
    have hlog : Real.log ((ν x (conjBox (Uij hij) t)).toReal) ≤ 0 :=
      Real.log_nonpos ENNReal.toReal_nonneg hle1'
    simp only [growthFun]
    exact neg_nonneg.mpr hlog
  by_cases htop : ∫⁻ x, ENNReal.ofReal (atomInfo A (Uij hij) ν t x) ∂μ = ⊤
  · have hle := lintegral_atomInfo_le_nocov (t := t) hL hU hmp hplq hdec hZ
    rw [htop] at hle
    exact le_top.trans hle
  · have hAI_int : Integrable (fun x : X3 => atomInfo A (Uij hij) ν t x) μ :=
      (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
        hAI_aem.aestronglyMeasurable ha_nn).mp htop
    have hid' : ∀ᵐ x ∂μ, atomInfo A (Uij hij) ν t x =
        (fun y : X3 => Real.log (((ν y) (shape A (Uij hij) y)).toReal)) (aDiag t • x)
          - (fun y : X3 => Real.log (((ν y) (shape A (Uij hij) y)).toReal)) x
          + growthFun (Uij hij) ν t (aDiag t • x) := hid
    have hcob := lintegral_ofReal_comp_le_of_coboundary
      (T := fun x : X3 => aDiag t • x) hmp hAI_int ha_nn hψ_aem hgnn hid'
    -- invariance of the `ℝ≥0∞`-integral under the measure-preserving shift
    have hAg : AEMeasurable
        (fun y : X3 => ENNReal.ofReal (growthFun (Uij hij) ν t y))
        (μ.map (fun x : X3 => aDiag t • x)) := by
      rw [hmp.map_eq]
      exact (aeStronglyMeasurable_growthFun hU hL t).aemeasurable.ennreal_ofReal
    have hcomp : ∫⁻ x, ENNReal.ofReal (growthFun (Uij hij) ν t (aDiag t • x)) ∂μ
        = ∫⁻ x, ENNReal.ofReal (growthFun (Uij hij) ν t x) ∂μ := by
      have h1 := (MeasureTheory.lintegral_map' hAg hmp.aemeasurable).symm
      rw [hmp.map_eq] at h1
      exact h1
    calc ∫⁻ x, ENNReal.ofReal (growthFun (Uij hij) ν t x) ∂μ
        = ∫⁻ x, ENNReal.ofReal (growthFun (Uij hij) ν t (aDiag t • x)) ∂μ := hcomp.symm
      _ ≤ ∫⁻ x, ENNReal.ofReal (atomInfo A (Uij hij) ν t x) ∂μ := hcob
      _ ≤ @Work.EKLC6Core.HcondSig X3 instMeasurableSpaceX3 μ A
            (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) :=
          lintegral_atomInfo_le_nocov (t := t) hL hU hmp hplq hdec hZ

end

end Work.EKLC6Core
