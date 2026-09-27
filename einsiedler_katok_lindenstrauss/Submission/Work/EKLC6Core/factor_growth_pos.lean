import Mathlib
import Submission.Work.EKLC6Core.Assembly
import Submission.Work.EKLC6Core.uminus_isHoro
import Submission.Work.EKLC6Core.growth_integral_sup
import Submission.Work.EKLC6Core.acovariant_of_leafwise
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLC6Core.growthFun_sub_eq_ae
import Submission.Work.EKLC6Core.aestronglyMeasurable_log_prodBoxMass
import Submission.Work.EKLC6Core.uij_normalizes_uij
import Submission.Work.EKLC6Core.uij_conj_uij_cross
import Submission.Work.EKLC6Core.srcU_contraction_of_lt
import Submission.Work.EKLC6Core.disjoint_Uij
import Submission.Work.EKLC6Core.disjoint_Uij_srcU
import Submission.Work.EKLC6Core.exists_mul_of_mem_sup
import Submission.Work.EKLC6Core.aDiag_mul_uij_of_eq

namespace Work.EKLC6Core

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

noncomputable section

/-- For distinct `p,q,r`: `U_qr` normalises the same-source join `U_pq ⊔ U_pr`. -/
theorem qr_normalizes_srcU {p q r : Fin 3} (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r) :
    ∀ g ∈ Uij hqr, ∀ u ∈ Uij hpq ⊔ Uij hpr, g * u * g⁻¹ ∈ Uij hpq ⊔ Uij hpr := by
  intro g hg u hu
  obtain ⟨a, rfl⟩ := (Work.EKLContract.Lemmas.horoUij_mem_iff hqr g).mp hg
  rw [Work.EKLContract.Lemmas.srcU_sup_eq_sub hpq hpr] at hu
  obtain ⟨s, t', rfl⟩ := (Work.EKLContract.Lemmas.srcU_mem_sub hpq hpr u).mp hu
  rw [Work.EKLContract.Lemmas.srcU_shape]
  have h1 : uij hqr a * uij hpq s * (uij hqr a)⁻¹ = uij hpq s * uij hpr (-(a * s)) :=
    uij_conj_uij_cross hpq hqr hpr a s
  have h2 : uij hqr a * uij hpr t' * (uij hqr a)⁻¹ = uij hpr t' :=
    uij_normalizes_uij hqr hpr hpr.symm hqr.symm a t'
  have hgrp : uij hqr a * (uij hpq s * uij hpr t') * (uij hqr a)⁻¹
      = (uij hqr a * uij hpq s * (uij hqr a)⁻¹) *
        (uij hqr a * uij hpr t' * (uij hqr a)⁻¹) := by group
  rw [hgrp, h1, h2]
  refine mul_mem ?_ (Subgroup.mem_sup_right ?_)
  · exact mul_mem
      (Subgroup.mem_sup_left ((Work.EKLContract.Lemmas.horoUij_mem_iff hpq _).mpr ⟨s, rfl⟩))
      (Subgroup.mem_sup_right ((Work.EKLContract.Lemmas.horoUij_mem_iff hpr _).mpr
        ⟨-(a * s), rfl⟩))
  · exact (Work.EKLContract.Lemmas.horoUij_mem_iff hpr _).mpr ⟨t', rfl⟩

/-- Additivity of the integrated growth function over a two-factor product decomposition,
assuming only the integrability of the two *outer* pieces `H` and `T` (the middle piece `U`
need not be known integrable separately). -/
theorem growth_integral_add {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ)
    (hprod : Work.EKLContract.P_Product)
    {H T U : Subgroup Work.EKLContract.SL3} (hTH : T ≤ H) (hUH : U ≤ H)
    (hHT : Work.EKLContract.IsHoro T) (hHU : Work.EKLContract.IsHoro U)
    (hHH : Work.EKLContract.IsHoro H)
    (hcent : ∃ t' : Fin 3 → ℝ,
      (∀ g ∈ T, Work.EKLContract.aDiag t' * g = g * Work.EKLContract.aDiag t') ∧
      (∀ u ∈ U, Filter.Tendsto
        (fun n : ℕ => Work.EKLContract.aDiag t' ^ n * u * (Work.EKLContract.aDiag t' ^ n)⁻¹)
        Filter.atTop (nhds 1)))
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hdec : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hAinv : Work.EKLContract.IsAInvariant μ)
    {νH νT νU : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {XH XT XU XH' XT' XU' : Set Work.EKLContract.X3}
    (hLH : Work.EKLContract.IsLeafwise μ H νH XH)
    (hLT : Work.EKLContract.IsLeafwise μ T νT XT)
    (hLU : Work.EKLContract.IsLeafwise μ U νU XU)
    (hcovH : Work.EKLC6Core.ACovariant νH XH') (hXH' : μ (XH'ᶜ) = 0)
    (hcovT : Work.EKLC6Core.ACovariant νT XT') (hXT' : μ (XT'ᶜ) = 0)
    (hcovU : Work.EKLC6Core.ACovariant νU XU') (hXU' : μ (XU'ᶜ) = 0)
    (hNH : MeasureTheory.Integrable (Work.EKLC6Core.growthFun H νH t) μ)
    (hNT : MeasureTheory.Integrable (Work.EKLC6Core.growthFun T νT t) μ)
    (hNU : MeasureTheory.Integrable (Work.EKLC6Core.growthFun U νU t) μ) :
    ∫ x, Work.EKLC6Core.growthFun H νH t x ∂μ
      = ∫ x, Work.EKLC6Core.growthFun T νT t x ∂μ
        + ∫ x, Work.EKLC6Core.growthFun U νU t x ∂μ := by
  have hae := growthFun_sub_eq_ae t hprod hTH hUH hHT hHU hHH hcent hnorm hdec hdisj hAinv
    hLH hLT hLU hcovH hXH' hcovT hXT' hcovU hXU'
  have hDint : MeasureTheory.Integrable
      (fun x => growthFun H νH t x - growthFun T νT t x - growthFun U νU t x) μ :=
    (hNH.sub hNT).sub hNU
  have hΨ := aestronglyMeasurable_log_prodBoxMass hHT hHU hLH
  have hzero := coboundary_integral (hAinv (-t)) hΨ hDint hae
  have h1 : ∫ x, growthFun H νH t x - growthFun T νT t x ∂μ
      = ∫ x, growthFun H νH t x ∂μ - ∫ x, growthFun T νT t x ∂μ := integral_sub hNH hNT
  have h2 : ∫ x, growthFun H νH t x - growthFun T νT t x - growthFun U νU t x ∂μ
      = ∫ x, growthFun H νH t x - growthFun T νT t x ∂μ - ∫ x, growthFun U νU t x ∂μ :=
    integral_sub (hNH.sub hNT) hNU
  linarith [hzero, h1, h2]

theorem factor_growth_pos (hLeaf : Work.EKLContract.P_Leafwise)
    (hprod : Work.EKLContract.P_Product)
    {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    (hErg : Work.EKLContract.IsAErgodic μ) (t : Fin 3 → ℝ)
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3}
    (hL : Work.EKLContract.IsLeafwise μ (Work.EKLC6Core.Uminus t) ν X')
    (hcov : Work.EKLC6Core.ACovariant ν X'') (hX'' : μ (X''ᶜ) = 0)
    (hint : MeasureTheory.Integrable (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t) μ)
    (hintf : ∀ (i j : Fin 3) (hij : i ≠ j), t i < t j →
      Work.EKLC6Core.IntegrableGrowth μ (Work.EKLContract.Uij hij) t)
    (hpos : 0 < ∫ x, Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t x ∂μ) :
    ∃ (i j : Fin 3) (hij : i ≠ j) (_ : t i < t j),
      ∃ (νij : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3)
        (Xij : Set Work.EKLContract.X3),
        Work.EKLContract.IsLeafwise μ (Work.EKLContract.Uij hij) νij Xij ∧
          0 < ∫ x, Work.EKLC6Core.growthFun (Work.EKLContract.Uij hij) νij t x ∂μ := by
  classical
  have hAinv : Work.EKLContract.IsAInvariant μ := hErg.1
  have hLHst : ∀ {U : Subgroup SL3}, IsHoro U → ∃ ν0 X0, IsLeafwise μ U ν0 X0 := by
    intro U hU
    obtain ⟨t0, ht0⟩ := hU.2.2
    exact (hLeaf μ U hU t0 (hAinv t0) ht0).1
  have hcovst : ∀ {U : Subgroup SL3} {ν0 : X3 → Measure SL3} {X0 : Set X3},
      IsHoro U → IsLeafwise μ U ν0 X0 →
      ∃ X1 : Set X3, X1 ⊆ X0 ∧ MeasurableSet X1 ∧ μ X1ᶜ = 0 ∧ ACovariant ν0 X1 :=
    fun hU hL0 => acovariant_of_leafwise hLeaf hAinv hU hL0
  obtain ⟨p, q, r, hpq, hpr, hqr, h1, h2⟩ := exists_sorted t
  rcases lt_or_eq_of_le h1 with h1' | h1'
  · rcases lt_or_eq_of_le h2 with h2' | h2'
    · -- Case A: t p < t q < t r
      have hprlt : t p < t r := lt_trans h1' h2'
      have hH_eqA : Uminus t = Uij hpq ⊔ Uij hpr ⊔ Uij hqr :=
        uminus_eq_three hpq hqr hpr h1' h2'
      obtain ⟨ν1, X1, hL1⟩ := hLHst (Work.EKLContract.Lemmas.isHoro_Uij hqr)
      obtain ⟨X1', -, -, hX1'null, hcov1⟩ := hcovst (Work.EKLContract.Lemmas.isHoro_Uij hqr) hL1
      obtain ⟨νJ, XJ, hLJ⟩ := hLHst (Work.EKLContract.Lemmas.isHoro_sup_same_source hpq hpr)
      obtain ⟨XJ', -, -, hXJ'null, hcovJ⟩ :=
        hcovst (Work.EKLContract.Lemmas.isHoro_sup_same_source hpq hpr) hLJ
      obtain ⟨ν2, X2, hL2⟩ := hLHst (Work.EKLContract.Lemmas.isHoro_Uij hpr)
      obtain ⟨X2', -, -, hX2'null, hcov2⟩ := hcovst (Work.EKLContract.Lemmas.isHoro_Uij hpr) hL2
      obtain ⟨ν3, X3, hL3⟩ := hLHst (Work.EKLContract.Lemmas.isHoro_Uij hpq)
      obtain ⟨X3', -, -, hX3'null, hcov3⟩ := hcovst (Work.EKLContract.Lemmas.isHoro_Uij hpq) hL3
      have hI1 : Integrable (growthFun (Uij hqr) ν1 t) μ := hintf q r hqr h2' ν1 X1 hL1
      have hI2 : Integrable (growthFun (Uij hpr) ν2 t) μ := hintf p r hpr hprlt ν2 X2 hL2
      have hI3 : Integrable (growthFun (Uij hpq) ν3 t) μ := hintf p q hpq h1' ν3 X3 hL3
      -- step 1: Uminus t = U_qr · (U_pq ⊔ U_pr)
      have hnorm1 : ∀ g ∈ Uij hqr, ∀ u ∈ Uij hpq ⊔ Uij hpr,
          g * u * g⁻¹ ∈ Uij hpq ⊔ Uij hpr := qr_normalizes_srcU hpq hqr hpr
      have hdisj1 : ∀ g ∈ Uij hqr, g ∈ Uij hpq ⊔ Uij hpr → g = 1 :=
        disjoint_Uij_srcU hpq hqr hpr
      have hcent1 : ∃ t' : Fin 3 → ℝ,
          (∀ g ∈ Uij hqr, aDiag t' * g = g * aDiag t') ∧
          (∀ u ∈ Uij hpq ⊔ Uij hpr, Tendsto
            (fun n : ℕ => aDiag t' ^ n * u * (aDiag t' ^ n)⁻¹) atTop (nhds 1)) := by
        refine ⟨fun k => if k = p then 0 else 1, ?_, ?_⟩
        · intro g hg
          obtain ⟨s, rfl⟩ := (Work.EKLContract.Lemmas.horoUij_mem_iff hqr g).mp hg
          exact aDiag_mul_uij_of_eq hqr _ (by simp [hpq.symm, hpr.symm]) s
        · exact srcU_contraction_of_lt hpq hpr _ (by simp [hpq.symm]) (by simp [hpr.symm])
      have hH_eqA1 : Uminus t = Uij hqr ⊔ (Uij hpq ⊔ Uij hpr) := by rw [hH_eqA]; ac_rfl
      have hdec1 : ∀ h ∈ Uminus t, ∃ g ∈ Uij hqr, ∃ u ∈ Uij hpq ⊔ Uij hpr, h = g * u := by
        intro h hh
        rw [hH_eqA1] at hh
        exact exists_mul_of_mem_sup hnorm1 hh
      have hae1 := growthFun_sub_eq_ae t hprod
        (by rw [hH_eqA1]; exact le_sup_left) (by rw [hH_eqA1]; exact le_sup_right)
        (Work.EKLContract.Lemmas.isHoro_Uij hqr)
        (Work.EKLContract.Lemmas.isHoro_sup_same_source hpq hpr) ((uminus_isHoro t).1)
        hcent1 hnorm1 hdec1 hdisj1 hAinv hL hL1 hLJ hcov hX'' hcov1 hX1'null hcovJ hXJ'null
      -- step 2: U_pq ⊔ U_pr = U_pr · U_pq
      have hnorm2 : ∀ g ∈ Uij hpr, ∀ u ∈ Uij hpq, g * u * g⁻¹ ∈ Uij hpq := by
        intro g hg u hu
        obtain ⟨a, rfl⟩ := (Work.EKLContract.Lemmas.horoUij_mem_iff hpr g).mp hg
        obtain ⟨s, rfl⟩ := (Work.EKLContract.Lemmas.horoUij_mem_iff hpq u).mp hu
        rw [uij_normalizes_uij hpr hpq hpr.symm hpq.symm a s]
        exact (Work.EKLContract.Lemmas.horoUij_mem_iff hpq _).mpr ⟨s, rfl⟩
      have hdisj2 : ∀ g ∈ Uij hpr, g ∈ Uij hpq → g = 1 := by
        refine disjoint_Uij hpr hpq ?_
        intro hcon
        exact hqr (Prod.ext_iff.mp hcon).2.symm
      have hcent2 : ∃ t' : Fin 3 → ℝ,
          (∀ g ∈ Uij hpr, aDiag t' * g = g * aDiag t') ∧
          (∀ u ∈ Uij hpq, Tendsto
            (fun n : ℕ => aDiag t' ^ n * u * (aDiag t' ^ n)⁻¹) atTop (nhds 1)) := by
        refine ⟨fun k => if k = q then 1 else 0, ?_, ?_⟩
        · intro g hg
          obtain ⟨s, rfl⟩ := (Work.EKLContract.Lemmas.horoUij_mem_iff hpr g).mp hg
          exact aDiag_mul_uij_of_eq hpr _ (by simp [hpq, hqr.symm]) s
        · intro u hu
          obtain ⟨s, rfl⟩ := (Work.EKLContract.Lemmas.horoUij_mem_iff hpq u).mp hu
          refine Work.EKLContract.Lemmas.horoUij_tendsto_conj _ hpq ?_ s
          simp [hpq]
      have hdec2 : ∀ h ∈ Uij hpq ⊔ Uij hpr, ∃ g ∈ Uij hpr, ∃ u ∈ Uij hpq, h = g * u := by
        intro h hh
        rw [sup_comm (Uij hpq) (Uij hpr)] at hh
        exact exists_mul_of_mem_sup hnorm2 hh
      have hae2 := growthFun_sub_eq_ae t hprod
        (le_sup_right : Uij hpr ≤ Uij hpq ⊔ Uij hpr)
        (le_sup_left : Uij hpq ≤ Uij hpq ⊔ Uij hpr)
        (Work.EKLContract.Lemmas.isHoro_Uij hpr) (Work.EKLContract.Lemmas.isHoro_Uij hpq)
        (Work.EKLContract.Lemmas.isHoro_sup_same_source hpq hpr)
        hcent2 hnorm2 hdec2 hdisj2 hAinv hLJ hL2 hL3 hcovJ hXJ'null hcov2 hX2'null hcov3 hX3'null
      -- combine the two coboundary identities
      have hDint : Integrable (fun x => growthFun (Uminus t) ν t x - growthFun (Uij hqr) ν1 t x
          - growthFun (Uij hpr) ν2 t x - growthFun (Uij hpq) ν3 t x) μ :=
        ((hint.sub hI1).sub hI2).sub hI3
      have hDdec : ∀ᵐ x ∂μ, growthFun (Uminus t) ν t x - growthFun (Uij hqr) ν1 t x
            - growthFun (Uij hpr) ν2 t x - growthFun (Uij hpq) ν3 t x
          = (Real.log ((ν (aDiag (-t) • x) (prodBox (Uij hqr) (Uij hpq ⊔ Uij hpr))).toReal)
              + Real.log ((νJ (aDiag (-t) • x) (prodBox (Uij hpr) (Uij hpq))).toReal))
            - (Real.log ((ν x (prodBox (Uij hqr) (Uij hpq ⊔ Uij hpr))).toReal)
              + Real.log ((νJ x (prodBox (Uij hpr) (Uij hpq))).toReal)) := by
        filter_upwards [hae1, hae2] with x h1x h2x
        linarith
      have hΨAE := 
        (aestronglyMeasurable_log_prodBoxMass (H := Uminus t) (T := Uij hqr)
            (U := Uij hpq ⊔ Uij hpr) (νH := ν) (XH := X')
            (Work.EKLContract.Lemmas.isHoro_Uij hqr)
            (Work.EKLContract.Lemmas.isHoro_sup_same_source hpq hpr) hL).add
          (aestronglyMeasurable_log_prodBoxMass (H := Uij hpq ⊔ Uij hpr) (T := Uij hpr)
            (U := Uij hpq) (νH := νJ) (XH := XJ)
            (Work.EKLContract.Lemmas.isHoro_Uij hpr) (Work.EKLContract.Lemmas.isHoro_Uij hpq) hLJ)
      have hzero := coboundary_integral (hAinv (-t)) hΨAE hDint hDdec
      have hzero' : ∫ x, growthFun (Uminus t) ν t x - growthFun (Uij hqr) ν1 t x
            - growthFun (Uij hpr) ν2 t x - growthFun (Uij hpq) ν3 t x ∂μ = 0 := hzero
      have e1 : ∫ x, growthFun (Uminus t) ν t x - growthFun (Uij hqr) ν1 t x ∂μ
          = ∫ x, growthFun (Uminus t) ν t x ∂μ - ∫ x, growthFun (Uij hqr) ν1 t x ∂μ :=
        integral_sub hint hI1
      have e2 : ∫ x, growthFun (Uminus t) ν t x - growthFun (Uij hqr) ν1 t x
            - growthFun (Uij hpr) ν2 t x ∂μ
          = ∫ x, growthFun (Uminus t) ν t x - growthFun (Uij hqr) ν1 t x ∂μ
            - ∫ x, growthFun (Uij hpr) ν2 t x ∂μ :=
        integral_sub (hint.sub hI1) hI2
      have e3 : ∫ x, growthFun (Uminus t) ν t x - growthFun (Uij hqr) ν1 t x
            - growthFun (Uij hpr) ν2 t x - growthFun (Uij hpq) ν3 t x ∂μ
          = ∫ x, growthFun (Uminus t) ν t x - growthFun (Uij hqr) ν1 t x
              - growthFun (Uij hpr) ν2 t x ∂μ
            - ∫ x, growthFun (Uij hpq) ν3 t x ∂μ :=
        integral_sub ((hint.sub hI1).sub hI2) hI3
      have hsum : 0 < ∫ x, growthFun (Uij hqr) ν1 t x ∂μ
          + ∫ x, growthFun (Uij hpr) ν2 t x ∂μ + ∫ x, growthFun (Uij hpq) ν3 t x ∂μ := by
        linarith [hzero', e1, e2, e3, hpos]
      by_cases hc1 : 0 < ∫ x, growthFun (Uij hqr) ν1 t x ∂μ
      · exact ⟨q, r, hqr, h2', ν1, X1, hL1, hc1⟩
      · by_cases hc2 : 0 < ∫ x, growthFun (Uij hpr) ν2 t x ∂μ
        · exact ⟨p, r, hpr, hprlt, ν2, X2, hL2, hc2⟩
        · refine ⟨p, q, hpq, h1', ν3, X3, hL3, ?_⟩
          push_neg at hc1 hc2
          linarith [hsum]
    · -- Case B: t p < t q = t r
      have hprlt : t p < t r := by rw [← h2']; exact h1'
      obtain ⟨νT, XT, hLT⟩ := hLHst (Work.EKLContract.Lemmas.isHoro_Uij hpr)
      obtain ⟨XT', -, -, hXT'null, hcovT⟩ := hcovst (Work.EKLContract.Lemmas.isHoro_Uij hpr) hLT
      obtain ⟨νU, XU, hLU⟩ := hLHst (Work.EKLContract.Lemmas.isHoro_Uij hpq)
      obtain ⟨XU', -, -, hXU'null, hcovU⟩ := hcovst (Work.EKLContract.Lemmas.isHoro_Uij hpq) hLU
      have hnormB : ∀ g ∈ Uij hpr, ∀ u ∈ Uij hpq, g * u * g⁻¹ ∈ Uij hpq := by
        intro g hg u hu
        obtain ⟨a, rfl⟩ := (Work.EKLContract.Lemmas.horoUij_mem_iff hpr g).mp hg
        obtain ⟨s, rfl⟩ := (Work.EKLContract.Lemmas.horoUij_mem_iff hpq u).mp hu
        rw [uij_normalizes_uij hpr hpq hpr.symm hpq.symm a s]
        exact (Work.EKLContract.Lemmas.horoUij_mem_iff hpq _).mpr ⟨s, rfl⟩
      have hdisjB : ∀ g ∈ Uij hpr, g ∈ Uij hpq → g = 1 := by
        refine disjoint_Uij hpr hpq ?_
        intro hcon
        exact hqr (Prod.ext_iff.mp hcon).2.symm
      have hcentB : ∃ t' : Fin 3 → ℝ,
          (∀ g ∈ Uij hpr, aDiag t' * g = g * aDiag t') ∧
          (∀ u ∈ Uij hpq, Tendsto
            (fun n : ℕ => aDiag t' ^ n * u * (aDiag t' ^ n)⁻¹) atTop (nhds 1)) := by
        refine ⟨fun k => if k = q then 1 else 0, ?_, ?_⟩
        · intro g hg
          obtain ⟨s, rfl⟩ := (Work.EKLContract.Lemmas.horoUij_mem_iff hpr g).mp hg
          exact aDiag_mul_uij_of_eq hpr _ (by simp [hpq, hqr.symm]) s
        · intro u hu
          obtain ⟨s, rfl⟩ := (Work.EKLContract.Lemmas.horoUij_mem_iff hpq u).mp hu
          refine Work.EKLContract.Lemmas.horoUij_tendsto_conj _ hpq ?_ s
          simp [hpq]
      have hH_eqB : Uminus t = Uij hpr ⊔ Uij hpq := by
        rw [uminus_eq_same_source hpq hqr hpr h1' h2']
        exact sup_comm _ _
      have hdecB : ∀ h ∈ Uminus t, ∃ g ∈ Uij hpr, ∃ u ∈ Uij hpq, h = g * u := by
        intro h hh
        rw [hH_eqB] at hh
        exact exists_mul_of_mem_sup hnormB hh
      have hTHB : Uij hpr ≤ Uminus t := by rw [hH_eqB]; exact le_sup_left
      have hUHB : Uij hpq ≤ Uminus t := by rw [hH_eqB]; exact le_sup_right
      have hadd := growth_integral_add t hprod hTHB hUHB
        (Work.EKLContract.Lemmas.isHoro_Uij hpr) (Work.EKLContract.Lemmas.isHoro_Uij hpq)
        ((uminus_isHoro t).1) hcentB hnormB hdecB hdisjB hAinv
        hL hLT hLU hcov hX'' hcovT hXT'null hcovU hXU'null hint
        (hintf p r hpr hprlt νT XT hLT) (hintf p q hpq h1' νU XU hLU)
      rw [hadd] at hpos
      by_cases hcase : 0 < ∫ x, growthFun (Uij hpr) νT t x ∂μ
      · exact ⟨p, r, hpr, hprlt, νT, XT, hLT, hcase⟩
      · refine ⟨p, q, hpq, h1', νU, XU, hLU, ?_⟩
        push_neg at hcase
        linarith [hpos]
  · rcases lt_or_eq_of_le h2 with h2' | h2'
    · -- Case C: t p = t q < t r
      have hprlt : t p < t r := by rw [h1']; exact h2'
      obtain ⟨νT, XT, hLT⟩ := hLHst (Work.EKLContract.Lemmas.isHoro_Uij hqr)
      obtain ⟨XT', -, -, hXT'null, hcovT⟩ := hcovst (Work.EKLContract.Lemmas.isHoro_Uij hqr) hLT
      obtain ⟨νU, XU, hLU⟩ := hLHst (Work.EKLContract.Lemmas.isHoro_Uij hpr)
      obtain ⟨XU', -, -, hXU'null, hcovU⟩ := hcovst (Work.EKLContract.Lemmas.isHoro_Uij hpr) hLU
      have hnormC : ∀ g ∈ Uij hqr, ∀ u ∈ Uij hpr, g * u * g⁻¹ ∈ Uij hpr := by
        intro g hg u hu
        obtain ⟨a, rfl⟩ := (Work.EKLContract.Lemmas.horoUij_mem_iff hqr g).mp hg
        obtain ⟨s, rfl⟩ := (Work.EKLContract.Lemmas.horoUij_mem_iff hpr u).mp hu
        rw [uij_normalizes_uij hqr hpr hpr.symm hqr.symm a s]
        exact (Work.EKLContract.Lemmas.horoUij_mem_iff hpr _).mpr ⟨s, rfl⟩
      have hdisjC : ∀ g ∈ Uij hqr, g ∈ Uij hpr → g = 1 := by
        refine disjoint_Uij hqr hpr ?_
        intro hcon
        exact hpq (Prod.ext_iff.mp hcon).1.symm
      have hcentC : ∃ t' : Fin 3 → ℝ,
          (∀ g ∈ Uij hqr, aDiag t' * g = g * aDiag t') ∧
          (∀ u ∈ Uij hpr, Tendsto
            (fun n : ℕ => aDiag t' ^ n * u * (aDiag t' ^ n)⁻¹) atTop (nhds 1)) := by
        refine ⟨fun k => if k = p then 0 else 1, ?_, ?_⟩
        · intro g hg
          obtain ⟨s, rfl⟩ := (Work.EKLContract.Lemmas.horoUij_mem_iff hqr g).mp hg
          exact aDiag_mul_uij_of_eq hqr _ (by simp [hpq.symm, hpr.symm]) s
        · intro u hu
          obtain ⟨s, rfl⟩ := (Work.EKLContract.Lemmas.horoUij_mem_iff hpr u).mp hu
          refine Work.EKLContract.Lemmas.horoUij_tendsto_conj _ hpr ?_ s
          simp [hpr.symm]
      have hH_eqC : Uminus t = Uij hqr ⊔ Uij hpr := by
        rw [uminus_eq_same_target hpq hqr hpr h1' h2']
        exact sup_comm _ _
      have hdecC : ∀ h ∈ Uminus t, ∃ g ∈ Uij hqr, ∃ u ∈ Uij hpr, h = g * u := by
        intro h hh
        rw [hH_eqC] at hh
        exact exists_mul_of_mem_sup hnormC hh
      have hTHC : Uij hqr ≤ Uminus t := by rw [hH_eqC]; exact le_sup_left
      have hUHC : Uij hpr ≤ Uminus t := by rw [hH_eqC]; exact le_sup_right
      have hadd := growth_integral_add t hprod hTHC hUHC
        (Work.EKLContract.Lemmas.isHoro_Uij hqr) (Work.EKLContract.Lemmas.isHoro_Uij hpr)
        ((uminus_isHoro t).1) hcentC hnormC hdecC hdisjC hAinv
        hL hLT hLU hcov hX'' hcovT hXT'null hcovU hXU'null hint
        (hintf q r hqr h2' νT XT hLT) (hintf p r hpr hprlt νU XU hLU)
      rw [hadd] at hpos
      by_cases hcase : 0 < ∫ x, growthFun (Uij hqr) νT t x ∂μ
      · exact ⟨q, r, hqr, h2', νT, XT, hLT, hcase⟩
      · refine ⟨p, r, hpr, hprlt, νU, XU, hLU, ?_⟩
        push_neg at hcase
        linarith [hpos]
    · -- Case D: t p = t q = t r
      exfalso
      have hbot : Uminus t = ⊥ := uminus_eq_bot hpq hqr hpr h1' h2'
      have hB : Box1 (⊥ : Subgroup SL3) = {1} := by
        ext g
        constructor
        · intro hg
          exact Subgroup.mem_bot.mp hg.1
        · intro hg
          rw [Set.mem_singleton_iff] at hg
          subst hg
          refine ⟨Subgroup.mem_bot.mpr rfl, ?_⟩
          intro i j
          simp
      have hbox : conjBox (Uminus t) t = {1} := by
        rw [hbot, conjBox, hB]
        ext g
        simp [conjBy]
      have hzero : ∫ x, growthFun (Uminus t) ν t x ∂μ = 0 := by
        have hae : growthFun (Uminus t) ν t =ᵐ[μ] fun _ : X3 => (0 : ℝ) := by
          filter_upwards [MeasureTheory.ae_iff.mpr hL.conull] with x hx
          rw [growthFun, hbox]
          have h1x : ν x ({1} : Set SL3) = 1 := by
            rw [← hB, ← hbot]
            exact hL.normalised x hx
          rw [h1x]
          simp
        rw [MeasureTheory.integral_congr_ae hae]
        simp
      rw [hzero] at hpos
      exact lt_irrefl _ hpos

end

end Work.EKLC6Core
