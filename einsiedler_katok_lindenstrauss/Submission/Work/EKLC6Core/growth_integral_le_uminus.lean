import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLC6Core.factor_growth_pos
import Submission.Work.EKLC6Core.uminus_isHoro
import Submission.Work.EKLC6Core.box_conjBox_subset
import Submission.Work.EKLC6Core.growthFun_integral_nonneg_Uij
import Submission.Work.EKLC6Core.integral_eq_of_two_coboundaries

namespace Work.EKLC6Core

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

noncomputable section

theorem growth_integral_le_uminus (hLeaf : Work.EKLContract.P_Leafwise) (hprod : Work.EKLContract.P_Product)
    {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    (hErg : Work.EKLContract.IsAErgodic μ) (t : Fin 3 → ℝ)
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3}
    (hL : Work.EKLContract.IsLeafwise μ (Work.EKLC6Core.Uminus t) ν X')
    (hcov : Work.EKLC6Core.ACovariant ν X'') (hX'' : μ (X''ᶜ) = 0)
    (hint : MeasureTheory.Integrable (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t) μ)
    (hintf : ∀ (i j : Fin 3) (hij : i ≠ j), t i < t j →
      ∀ (ν' : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3) (X : Set Work.EKLContract.X3),
        Work.EKLContract.IsLeafwise μ (Work.EKLContract.Uij hij) ν' X →
          MeasureTheory.Integrable (Work.EKLC6Core.growthFun (Work.EKLContract.Uij hij) ν' t) μ) :
    ∀ (i j : Fin 3) (hij : i ≠ j), t i < t j →
      ∃ (νij : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3)
        (Xij : Set Work.EKLContract.X3),
        Work.EKLContract.IsLeafwise μ (Work.EKLContract.Uij hij) νij Xij ∧
        ∫ x, Work.EKLC6Core.growthFun (Work.EKLContract.Uij hij) νij t x ∂μ
          ≤ ∫ x, Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t x ∂μ := by
  classical
  have hAinv : IsAInvariant μ := hErg.1
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
    · -- =========================== Case A: t p < t q < t r ===========================
      have hprlt : t p < t r := lt_trans h1' h2'
      have hH_eqA : Uminus t = Uij hpq ⊔ Uij hpr ⊔ Uij hqr :=
        uminus_eq_three hpq hqr hpr h1' h2'
      obtain ⟨ν_qr, X_qr, hL_qr⟩ := hLHst (Lemmas.isHoro_Uij hqr)
      obtain ⟨X_qr', -, -, hX_qr'null, hcov_qr⟩ := hcovst (Lemmas.isHoro_Uij hqr) hL_qr
      obtain ⟨νJ, XJ, hLJ⟩ := hLHst (Lemmas.isHoro_sup_same_source hpq hpr)
      obtain ⟨XJ', -, -, hXJ'null, hcovJ⟩ :=
        hcovst (Lemmas.isHoro_sup_same_source hpq hpr) hLJ
      obtain ⟨ν_pr, X_pr, hL_pr⟩ := hLHst (Lemmas.isHoro_Uij hpr)
      obtain ⟨X_pr', -, -, hX_pr'null, hcov_pr⟩ := hcovst (Lemmas.isHoro_Uij hpr) hL_pr
      obtain ⟨ν_pq, X_pq, hL_pq⟩ := hLHst (Lemmas.isHoro_Uij hpq)
      obtain ⟨X_pq', -, -, hX_pq'null, hcov_pq⟩ := hcovst (Lemmas.isHoro_Uij hpq) hL_pq
      have hI_qr : Integrable (growthFun (Uij hqr) ν_qr t) μ := hintf q r hqr h2' ν_qr X_qr hL_qr
      have hI_pr : Integrable (growthFun (Uij hpr) ν_pr t) μ := hintf p r hpr hprlt ν_pr X_pr hL_pr
      have hI_pq : Integrable (growthFun (Uij hpq) ν_pq t) μ := hintf p q hpq h1' ν_pq X_pq hL_pq
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
          obtain ⟨s, rfl⟩ := (Lemmas.horoUij_mem_iff hqr g).mp hg
          exact aDiag_mul_uij_of_eq hqr _ (by simp [hpq.symm, hpr.symm]) s
        · exact srcU_contraction_of_lt hpq hpr _ (by simp [hpq.symm]) (by simp [hpr.symm])
      have hH_eqA1 : Uminus t = Uij hqr ⊔ (Uij hpq ⊔ Uij hpr) := by rw [hH_eqA]; ac_rfl
      have hdec1 : ∀ h ∈ Uminus t, ∃ g ∈ Uij hqr, ∃ u ∈ Uij hpq ⊔ Uij hpr, h = g * u := by
        intro h hh
        rw [hH_eqA1] at hh
        exact exists_mul_of_mem_sup hnorm1 hh
      have hae1 := growthFun_sub_eq_ae t hprod
        (by rw [hH_eqA1]; exact le_sup_left) (by rw [hH_eqA1]; exact le_sup_right)
        (Lemmas.isHoro_Uij hqr) (Lemmas.isHoro_sup_same_source hpq hpr) ((uminus_isHoro t).1)
        hcent1 hnorm1 hdec1 hdisj1 hAinv hL hL_qr hLJ hcov hX'' hcov_qr hX_qr'null hcovJ hXJ'null
      -- step 2: U_pq ⊔ U_pr = U_pr · U_pq
      have hnorm2 : ∀ g ∈ Uij hpr, ∀ u ∈ Uij hpq, g * u * g⁻¹ ∈ Uij hpq := by
        intro g hg u hu
        obtain ⟨a, rfl⟩ := (Lemmas.horoUij_mem_iff hpr g).mp hg
        obtain ⟨s, rfl⟩ := (Lemmas.horoUij_mem_iff hpq u).mp hu
        rw [uij_normalizes_uij hpr hpq hpr.symm hpq.symm a s]
        exact (Lemmas.horoUij_mem_iff hpq _).mpr ⟨s, rfl⟩
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
          obtain ⟨s, rfl⟩ := (Lemmas.horoUij_mem_iff hpr g).mp hg
          exact aDiag_mul_uij_of_eq hpr _ (by simp [hpq, hqr.symm]) s
        · intro u hu
          obtain ⟨s, rfl⟩ := (Lemmas.horoUij_mem_iff hpq u).mp hu
          refine Lemmas.horoUij_tendsto_conj _ hpq ?_ s
          simp [hpq]
      have hdec2 : ∀ h ∈ Uij hpq ⊔ Uij hpr, ∃ g ∈ Uij hpr, ∃ u ∈ Uij hpq, h = g * u := by
        intro h hh
        rw [sup_comm (Uij hpq) (Uij hpr)] at hh
        exact exists_mul_of_mem_sup hnorm2 hh
      have hae2 := growthFun_sub_eq_ae t hprod
        (le_sup_right : Uij hpr ≤ Uij hpq ⊔ Uij hpr)
        (le_sup_left : Uij hpq ≤ Uij hpq ⊔ Uij hpr)
        (Lemmas.isHoro_Uij hpr) (Lemmas.isHoro_Uij hpq) (Lemmas.isHoro_sup_same_source hpq hpr)
        hcent2 hnorm2 hdec2 hdisj2 hAinv hLJ hL_pr hL_pq
        hcovJ hXJ'null hcov_pr hX_pr'null hcov_pq hX_pq'null
      -- combine the two coboundary identities
      have hsum : ∫ x, growthFun (Uminus t) ν t x ∂μ
          = ∫ x, growthFun (Uij hqr) ν_qr t x ∂μ
            + ∫ x, growthFun (Uij hpr) ν_pr t x ∂μ
            + ∫ x, growthFun (Uij hpq) ν_pq t x ∂μ := by
        refine integral_eq_of_two_coboundaries (φ := fun x : X3 => aDiag (-t) • x)
          (hφ := hAinv (-t))
          (hA := aestronglyMeasurable_log_prodBoxMass (H := Uminus t) (T := Uij hqr)
            (U := Uij hpq ⊔ Uij hpr) (νH := ν) (XH := X')
            (Lemmas.isHoro_Uij hqr) (Lemmas.isHoro_sup_same_source hpq hpr) hL)
          (hB := aestronglyMeasurable_log_prodBoxMass (H := Uij hpq ⊔ Uij hpr) (T := Uij hpr)
            (U := Uij hpq) (νH := νJ) (XH := XJ)
            (Lemmas.isHoro_Uij hpr) (Lemmas.isHoro_Uij hpq) hLJ)
          (hae1 := hae1) (hae2 := hae2)
          (hH := hint) (hq := hI_qr) (hp := hI_pr) (hr := hI_pq)
      have hNN_qr : 0 ≤ ∫ x, growthFun (Uij hqr) ν_qr t x ∂μ :=
        growthFun_integral_nonneg_Uij t hqr h2' hL_qr
      have hNN_pr : 0 ≤ ∫ x, growthFun (Uij hpr) ν_pr t x ∂μ :=
        growthFun_integral_nonneg_Uij t hpr hprlt hL_pr
      have hNN_pq : 0 ≤ ∫ x, growthFun (Uij hpq) ν_pq t x ∂μ :=
        growthFun_integral_nonneg_Uij t hpq h1' hL_pq
      have fact_qr : ∃ (νij : X3 → Measure SL3) (Xij : Set X3),
          IsLeafwise μ (Uij hqr) νij Xij ∧
          ∫ x, growthFun (Uij hqr) νij t x ∂μ ≤ ∫ x, growthFun (Uminus t) ν t x ∂μ :=
        ⟨ν_qr, X_qr, hL_qr, by linarith [hsum, hNN_pr, hNN_pq]⟩
      have fact_pr : ∃ (νij : X3 → Measure SL3) (Xij : Set X3),
          IsLeafwise μ (Uij hpr) νij Xij ∧
          ∫ x, growthFun (Uij hpr) νij t x ∂μ ≤ ∫ x, growthFun (Uminus t) ν t x ∂μ :=
        ⟨ν_pr, X_pr, hL_pr, by linarith [hsum, hNN_qr, hNN_pq]⟩
      have fact_pq : ∃ (νij : X3 → Measure SL3) (Xij : Set X3),
          IsLeafwise μ (Uij hpq) νij Xij ∧
          ∫ x, growthFun (Uij hpq) νij t x ∂μ ≤ ∫ x, growthFun (Uminus t) ν t x ∂μ :=
        ⟨ν_pq, X_pq, hL_pq, by linarith [hsum, hNN_qr, hNN_pr]⟩
      intro i j hij hlt
      rcases pair_of_lt_sorted hpq hqr hpr (le_of_lt h1') (le_of_lt h2') hlt with
        ⟨hi, hj⟩ | ⟨hi, hj⟩
      · rcases hj with hj | hj
        · rw [Uij_congr hi hj hij hpq]; exact fact_pq
        · rw [Uij_congr hi hj hij hpr]; exact fact_pr
      · rw [Uij_congr hi hj hij hqr]; exact fact_qr
    · -- =========================== Case B: t p < t q = t r ===========================
      have hprlt : t p < t r := by rw [← h2']; exact h1'
      obtain ⟨ν_pr, X_pr, hL_pr⟩ := hLHst (Lemmas.isHoro_Uij hpr)
      obtain ⟨X_pr', -, -, hX_pr'null, hcov_pr⟩ := hcovst (Lemmas.isHoro_Uij hpr) hL_pr
      obtain ⟨ν_pq, X_pq, hL_pq⟩ := hLHst (Lemmas.isHoro_Uij hpq)
      obtain ⟨X_pq', -, -, hX_pq'null, hcov_pq⟩ := hcovst (Lemmas.isHoro_Uij hpq) hL_pq
      have hnormB : ∀ g ∈ Uij hpr, ∀ u ∈ Uij hpq, g * u * g⁻¹ ∈ Uij hpq := by
        intro g hg u hu
        obtain ⟨a, rfl⟩ := (Lemmas.horoUij_mem_iff hpr g).mp hg
        obtain ⟨s, rfl⟩ := (Lemmas.horoUij_mem_iff hpq u).mp hu
        rw [uij_normalizes_uij hpr hpq hpr.symm hpq.symm a s]
        exact (Lemmas.horoUij_mem_iff hpq _).mpr ⟨s, rfl⟩
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
          obtain ⟨s, rfl⟩ := (Lemmas.horoUij_mem_iff hpr g).mp hg
          exact aDiag_mul_uij_of_eq hpr _ (by simp [hpq, hqr.symm]) s
        · intro u hu
          obtain ⟨s, rfl⟩ := (Lemmas.horoUij_mem_iff hpq u).mp hu
          refine Lemmas.horoUij_tendsto_conj _ hpq ?_ s
          simp [hpq]
      have hH_eqB : Uminus t = Uij hpr ⊔ Uij hpq := by
        rw [uminus_eq_same_source hpq hqr hpr h1' h2']; exact sup_comm _ _
      have hdecB : ∀ h ∈ Uminus t, ∃ g ∈ Uij hpr, ∃ u ∈ Uij hpq, h = g * u := by
        intro h hh
        rw [hH_eqB] at hh
        exact exists_mul_of_mem_sup hnormB hh
      have hTHB : Uij hpr ≤ Uminus t := by rw [hH_eqB]; exact le_sup_left
      have hUHB : Uij hpq ≤ Uminus t := by rw [hH_eqB]; exact le_sup_right
      have hI_pr : Integrable (growthFun (Uij hpr) ν_pr t) μ := hintf p r hpr hprlt ν_pr X_pr hL_pr
      have hI_pq : Integrable (growthFun (Uij hpq) ν_pq t) μ := hintf p q hpq h1' ν_pq X_pq hL_pq
      have hadd := growth_integral_sup t hprod hTHB hUHB
        (Lemmas.isHoro_Uij hpr) (Lemmas.isHoro_Uij hpq) ((uminus_isHoro t).1)
        hcentB hnormB hdecB hdisjB hAinv
        hL hL_pr hL_pq hcov hX'' hcov_pr hX_pr'null hcov_pq hX_pq'null
        hint hI_pr hI_pq
      have hNN_pr : 0 ≤ ∫ x, growthFun (Uij hpr) ν_pr t x ∂μ :=
        growthFun_integral_nonneg_Uij t hpr hprlt hL_pr
      have hNN_pq : 0 ≤ ∫ x, growthFun (Uij hpq) ν_pq t x ∂μ :=
        growthFun_integral_nonneg_Uij t hpq h1' hL_pq
      have fact_pr : ∃ (νij : X3 → Measure SL3) (Xij : Set X3),
          IsLeafwise μ (Uij hpr) νij Xij ∧
          ∫ x, growthFun (Uij hpr) νij t x ∂μ ≤ ∫ x, growthFun (Uminus t) ν t x ∂μ :=
        ⟨ν_pr, X_pr, hL_pr, by linarith [hadd, hNN_pq]⟩
      have fact_pq : ∃ (νij : X3 → Measure SL3) (Xij : Set X3),
          IsLeafwise μ (Uij hpq) νij Xij ∧
          ∫ x, growthFun (Uij hpq) νij t x ∂μ ≤ ∫ x, growthFun (Uminus t) ν t x ∂μ :=
        ⟨ν_pq, X_pq, hL_pq, by linarith [hadd, hNN_pr]⟩
      intro i j hij hlt
      rcases pair_of_lt_sorted hpq hqr hpr (le_of_lt h1') (le_of_eq h2') hlt with
        ⟨hi, hj⟩ | ⟨hi, hj⟩
      · rcases hj with hj | hj
        · rw [Uij_congr hi hj hij hpq]; exact fact_pq
        · rw [Uij_congr hi hj hij hpr]; exact fact_pr
      · rw [hi, hj] at hlt; linarith
  · rcases lt_or_eq_of_le h2 with h2' | h2'
    · -- =========================== Case C: t p = t q < t r ===========================
      have hprlt : t p < t r := by rw [h1']; exact h2'
      obtain ⟨ν_qr, X_qr, hL_qr⟩ := hLHst (Lemmas.isHoro_Uij hqr)
      obtain ⟨X_qr', -, -, hX_qr'null, hcov_qr⟩ := hcovst (Lemmas.isHoro_Uij hqr) hL_qr
      obtain ⟨ν_pr, X_pr, hL_pr⟩ := hLHst (Lemmas.isHoro_Uij hpr)
      obtain ⟨X_pr', -, -, hX_pr'null, hcov_pr⟩ := hcovst (Lemmas.isHoro_Uij hpr) hL_pr
      have hnormC : ∀ g ∈ Uij hqr, ∀ u ∈ Uij hpr, g * u * g⁻¹ ∈ Uij hpr := by
        intro g hg u hu
        obtain ⟨a, rfl⟩ := (Lemmas.horoUij_mem_iff hqr g).mp hg
        obtain ⟨s, rfl⟩ := (Lemmas.horoUij_mem_iff hpr u).mp hu
        rw [uij_normalizes_uij hqr hpr hpr.symm hqr.symm a s]
        exact (Lemmas.horoUij_mem_iff hpr _).mpr ⟨s, rfl⟩
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
          obtain ⟨s, rfl⟩ := (Lemmas.horoUij_mem_iff hqr g).mp hg
          exact aDiag_mul_uij_of_eq hqr _ (by simp [hpq.symm, hpr.symm]) s
        · intro u hu
          obtain ⟨s, rfl⟩ := (Lemmas.horoUij_mem_iff hpr u).mp hu
          refine Lemmas.horoUij_tendsto_conj _ hpr ?_ s
          simp [hpr.symm]
      have hH_eqC : Uminus t = Uij hqr ⊔ Uij hpr := by
        rw [uminus_eq_same_target hpq hqr hpr h1' h2']; exact sup_comm _ _
      have hdecC : ∀ h ∈ Uminus t, ∃ g ∈ Uij hqr, ∃ u ∈ Uij hpr, h = g * u := by
        intro h hh
        rw [hH_eqC] at hh
        exact exists_mul_of_mem_sup hnormC hh
      have hTHC : Uij hqr ≤ Uminus t := by rw [hH_eqC]; exact le_sup_left
      have hUHC : Uij hpr ≤ Uminus t := by rw [hH_eqC]; exact le_sup_right
      have hI_qr : Integrable (growthFun (Uij hqr) ν_qr t) μ := hintf q r hqr h2' ν_qr X_qr hL_qr
      have hI_pr : Integrable (growthFun (Uij hpr) ν_pr t) μ := hintf p r hpr hprlt ν_pr X_pr hL_pr
      have hadd := growth_integral_sup t hprod hTHC hUHC
        (Lemmas.isHoro_Uij hqr) (Lemmas.isHoro_Uij hpr) ((uminus_isHoro t).1)
        hcentC hnormC hdecC hdisjC hAinv
        hL hL_qr hL_pr hcov hX'' hcov_qr hX_qr'null hcov_pr hX_pr'null
        hint hI_qr hI_pr
      have hNN_qr : 0 ≤ ∫ x, growthFun (Uij hqr) ν_qr t x ∂μ :=
        growthFun_integral_nonneg_Uij t hqr h2' hL_qr
      have hNN_pr : 0 ≤ ∫ x, growthFun (Uij hpr) ν_pr t x ∂μ :=
        growthFun_integral_nonneg_Uij t hpr hprlt hL_pr
      have fact_qr : ∃ (νij : X3 → Measure SL3) (Xij : Set X3),
          IsLeafwise μ (Uij hqr) νij Xij ∧
          ∫ x, growthFun (Uij hqr) νij t x ∂μ ≤ ∫ x, growthFun (Uminus t) ν t x ∂μ :=
        ⟨ν_qr, X_qr, hL_qr, by linarith [hadd, hNN_pr]⟩
      have fact_pr : ∃ (νij : X3 → Measure SL3) (Xij : Set X3),
          IsLeafwise μ (Uij hpr) νij Xij ∧
          ∫ x, growthFun (Uij hpr) νij t x ∂μ ≤ ∫ x, growthFun (Uminus t) ν t x ∂μ :=
        ⟨ν_pr, X_pr, hL_pr, by linarith [hadd, hNN_qr]⟩
      intro i j hij hlt
      rcases pair_of_lt_sorted hpq hqr hpr (le_of_eq h1') (le_of_lt h2') hlt with
        ⟨hi, hj⟩ | ⟨hi, hj⟩
      · rcases hj with hj | hj
        · rw [hi, hj] at hlt; linarith
        · rw [Uij_congr hi hj hij hpr]; exact fact_pr
      · rw [Uij_congr hi hj hij hqr]; exact fact_qr
    · -- =========================== Case D: t p = t q = t r ===========================
      intro i j hij hlt
      rcases pair_of_lt_sorted hpq hqr hpr (le_of_eq h1') (le_of_eq h2') hlt with
        ⟨hi, hj⟩ | ⟨hi, hj⟩
      · rcases hj with hj | hj
        · rw [hi, hj] at hlt; linarith
        · rw [hi, hj] at hlt; linarith
      · rw [hi, hj] at hlt; linarith

end

end Work.EKLC6Core
