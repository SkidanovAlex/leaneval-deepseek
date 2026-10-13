import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.FTS.PhiStar.Radial.radGreen_solves
import Submission.Work.EllipticEst.ModalSolution.RGW.Defs
import Submission.Work.EllipticEst.ModalSolution.RGW.lagrange_ibp
import Submission.Work.EllipticEst.ModalSolution.RGW.Lneg_rpow
import Submission.Work.EllipticEst.ModalSolution.RGW.primitive_mul_left
import Submission.Work.EllipticEst.ModalSolution.RGW.primitive_mul_right
import Submission.Work.EllipticEst.ModalSolution.RGW.support_extract
import Submission.Work.EllipticEst.ModalSolution.RGW.integral_deriv_eq_zero
import Submission.Work.EllipticEst.ModalSolution.RGW.kernel_junk
import Submission.Work.EllipticEst.ModalSolution.RGW.final_algebra
import Submission.Work.EllipticEst.ModalSolution.RGW.srcM_integrable
import Submission.Work.EllipticEst.ModalSolution.RGW.srcP_integrable
import Submission.Work.FTS.H2.ModalSolR.RGWeakAux
import Submission.Work.FTS.H2.ModalSolR.RGWeak.Fgen_algebra
import Submission.Work.FTS.H2.ModalSolR.RGWeak.qm_formula
import Submission.Work.FTS.H2.ModalSolR.RGWeak.qp_formula
import Submission.Work.FTS.H2.ModalSolR.RGWeak.AB_continuous

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.ModalSolR

open MeasureTheory Set Filter
open scoped Real Topology
open Work.EllipticEst.ModalSolution.RadGreenWeak (sM sP qW wgt pwt Lneg srcM srcP)
open Work.FTS.H2.ModalSolR.RGWeak (Fgen Fgen_eq_zero integral_Ioi_eq_intervalIntegral)

theorem radGreenWeakOdeMeas {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (m : ℕ) {c ψ : ℝ → ℝ}
    (hc : MeasureTheory.IntegrableOn (fun t => c t ^ 2) (Set.Ioi 0))
    (hcm : MeasureTheory.AEStronglyMeasurable c (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Set.Ioi 0) :
    (∫ z in Set.Ioi 0, Work.FTS.PhiStar.Radial.radGreen α m c z *
        (-(α ^ 2) * z ^ 2 * deriv (deriv ψ) z - (α * (5 + α) * z) * deriv ψ z)
        * z ^ ((5 - α) / α))
      + Work.FTS.PhiStar.Radial.lamR m
          * (∫ z in Set.Ioi 0,
              Work.FTS.PhiStar.Radial.radGreen α m c z * ψ z * z ^ ((5 - α) / α))
      = ∫ z in Set.Ioi 0, c z * ψ z * z ^ ((5 - α) / α) := by
  -- ## 0. the support interval
  obtain ⟨a, b, ha, hab, hsub, hvan⟩ :=
    Work.EllipticEst.ModalSolution.RGW.support_extract ψ hψ hψc hψs
  have hable : a ≤ b := le_of_lt hab
  have hvan2 : ∀ z : ℝ, z ∉ Set.Ioo a b → ψ z = 0 ∧ deriv ψ z = 0 :=
    fun z hz => ⟨(hvan z hz).1, (hvan z hz).2.1⟩
  have hsubI : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun z hz => lt_of_lt_of_le ha hz.1
  have huIcc : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hable
  -- ## 1. continuity of the elementary factors on `(0,∞)`
  have hpowM : ContinuousOn (fun z : ℝ => z ^ (sM α m)) (Set.Ioi 0) := fun z hz =>
    (Real.continuousAt_rpow_const z (sM α m) (Or.inl (ne_of_gt hz))).continuousWithinAt
  have hpowP : ContinuousOn (fun z : ℝ => z ^ (sP α m)) (Set.Ioi 0) := fun z hz =>
    (Real.continuousAt_rpow_const z (sP α m) (Or.inl (ne_of_gt hz))).continuousWithinAt
  have hpowMm : ContinuousOn (fun z : ℝ => z ^ (sM α m - 1)) (Set.Ioi 0) := fun z hz =>
    (Real.continuousAt_rpow_const z (sM α m - 1) (Or.inl (ne_of_gt hz))).continuousWithinAt
  have hpowPm : ContinuousOn (fun z : ℝ => z ^ (sP α m - 1)) (Set.Ioi 0) := fun z hz =>
    (Real.continuousAt_rpow_const z (sP α m - 1) (Or.inl (ne_of_gt hz))).continuousWithinAt
  have hwgtc : ContinuousOn (wgt α) (Set.Ioi 0) := fun z hz =>
    (Real.continuousAt_rpow_const z (qW α) (Or.inl (ne_of_gt hz))).continuousWithinAt
  have hLc : ContinuousOn (Lneg α ψ) (Set.Ioi 0) :=
    Work.EllipticEst.ModalSolution.RGW.Lneg_continuousOn α hψ.contDiffOn
  have hpsic : ContinuousOn ψ (Set.Ioi 0) := hψ.continuous.continuousOn
  have hψdc : ContinuousOn (deriv ψ) (Set.Ioi 0) :=
    (hψ.continuous_deriv (by norm_num)).continuousOn
  have hpwtc : ContinuousOn (pwt α) (Set.Ioi 0) := by
    have h : pwt α = fun z : ℝ => α ^ 2 * (z ^ 2 * wgt α z) := by
      funext z; simp only [pwt]
    rw [h]
    exact continuousOn_const.mul ((continuousOn_id.pow 2).mul hwgtc)
  have hFgenM : ContinuousOn (fun z : ℝ => Fgen α (sM α m) ψ z) (Set.Ioi 0) :=
    (hpwtc.mul ((hpowM.mul hψdc).sub
      (((continuousOn_const (c := sM α m)).mul hpowMm).mul hpsic))).congr
      (fun z _ => by simp only [Fgen, Pi.mul_apply, Pi.sub_apply] <;> ring)
  have hFgenP : ContinuousOn (fun z : ℝ => Fgen α (sP α m) ψ z) (Set.Ioi 0) :=
    (hpwtc.mul ((hpowP.mul hψdc).sub
      (((continuousOn_const (c := sP α m)).mul hpowPm).mul hpsic))).congr
      (fun z _ => by simp only [Fgen, Pi.mul_apply, Pi.sub_apply] <;> ring)
  -- ## 2. the local abbreviations
  set GM : ℝ → ℝ := fun z => z ^ (sM α m) * (wgt α z * Lneg α ψ z) with hGM
  set GP : ℝ → ℝ := fun z => z ^ (sP α m) * (wgt α z * Lneg α ψ z) with hGP
  set RM : ℝ → ℝ := fun z => z ^ (sM α m) * (wgt α z * ψ z) with hRM
  set RP : ℝ → ℝ := fun z => z ^ (sP α m) * (wgt α z * ψ z) with hRP
  set fM : ℝ → ℝ := srcM α m c with hfM
  set fP : ℝ → ℝ := srcP α m c with hfP
  set A : ℝ → ℝ := fun z => ∫ t in (0 : ℝ)..z, srcM α m c t with hA
  set Bz : ℝ → ℝ := fun z => ∫ t in Set.Ioi z, srcP α m c t with hB
  -- ## 3. continuity / integrability of the pieces
  have hGMcontI : ContinuousOn GM (Set.Icc a b) := by
    rw [hGM]
    exact (hpowM.mono hsubI).mul ((hwgtc.mono hsubI).mul (hLc.mono hsubI))
  have hGPcontI : ContinuousOn GP (Set.Icc a b) := by
    rw [hGP]
    exact (hpowP.mono hsubI).mul ((hwgtc.mono hsubI).mul (hLc.mono hsubI))
  have hRMcontI : ContinuousOn RM (Set.Icc a b) := by
    rw [hRM]
    exact (hpowM.mono hsubI).mul ((hwgtc.mono hsubI).mul (hpsic.mono hsubI))
  have hRPcontI : ContinuousOn RP (Set.Icc a b) := by
    rw [hRP]
    exact (hpowP.mono hsubI).mul ((hwgtc.mono hsubI).mul (hpsic.mono hsubI))
  have hGMcontU : ContinuousOn GM (Set.uIcc a b) := by rw [huIcc]; exact hGMcontI
  have hGPcontU : ContinuousOn GP (Set.uIcc a b) := by rw [huIcc]; exact hGPcontI
  have hRMcontU : ContinuousOn RM (Set.uIcc a b) := by rw [huIcc]; exact hRMcontI
  have hRPcontU : ContinuousOn RP (Set.uIcc a b) := by rw [huIcc]; exact hRPcontI
  have hFgenMcontU : ContinuousOn (fun t : ℝ => Fgen α (sM α m) ψ t) (Set.uIcc a b) := by
    rw [huIcc]; exact hFgenM.mono hsubI
  have hFgenPcontU : ContinuousOn (fun t : ℝ => Fgen α (sP α m) ψ t) (Set.uIcc a b) := by
    rw [huIcc]; exact hFgenP.mono hsubI
  have hGMint : IntervalIntegrable GM volume a b := hGMcontI.intervalIntegrable_of_Icc hable
  have hGPint : IntervalIntegrable GP volume a b := hGPcontI.intervalIntegrable_of_Icc hable
  have hRMint : IntervalIntegrable RM volume a b := hRMcontI.intervalIntegrable_of_Icc hable
  have hRPint : IntervalIntegrable RP volume a b := hRPcontI.intervalIntegrable_of_Icc hable
  have hGM_uIcc : IntegrableOn GM (Set.uIcc a b) volume := by
    rw [huIcc]; exact hGMcontI.integrableOn_compact isCompact_Icc
  have hGP_uIcc : IntegrableOn GP (Set.uIcc a b) volume := by
    rw [huIcc]; exact hGPcontI.integrableOn_compact isCompact_Icc
  have hRM_uIcc : IntegrableOn RM (Set.uIcc a b) volume := by
    rw [huIcc]; exact hRMcontI.integrableOn_compact isCompact_Icc
  have hRP_uIcc : IntegrableOn RP (Set.uIcc a b) volume := by
    rw [huIcc]; exact hRPcontI.integrableOn_compact isCompact_Icc
  -- the source functions and their primitives
  have hfM_int : IntervalIntegrable fM volume a b := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hable, hfM]
    exact (Work.EllipticEst.ModalSolution.RGW.srcM_integrable hα hα1 m hc hcm
      (lt_of_lt_of_le ha hable)).mono_set (fun t ht => ⟨lt_of_lt_of_le ha ht.1.le, ht.2⟩)
  have hfP_int : IntervalIntegrable fP volume a b := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hable, hfP]
    exact (Work.EllipticEst.ModalSolution.RGW.srcP_integrable hα hα1 m hc hcm ha).mono_set
      (fun t ht => ht.1)
  have hfM_Icc : IntegrableOn fM (Set.Icc a b) volume :=
    (integrableOn_Icc_iff_integrableOn_Ioc).mpr hfM_int.1
  have hfP_Icc : IntegrableOn fP (Set.Icc a b) volume :=
    (integrableOn_Icc_iff_integrableOn_Ioc).mpr hfP_int.1
  have hfM_uIcc : IntegrableOn fM (Set.uIcc a b) volume := by rw [huIcc]; exact hfM_Icc
  have hfP_uIcc : IntegrableOn fP (Set.uIcc a b) volume := by rw [huIcc]; exact hfP_Icc
  have hprimMint : IntervalIntegrable (fun z => ∫ t in a..z, fM t) volume a b :=
    (intervalIntegral.continuousOn_primitive_interval hfM_uIcc).intervalIntegrable
  have hprimPint : IntervalIntegrable (fun z => ∫ t in z..b, fP t) volume a b :=
    (intervalIntegral.continuousOn_primitive_interval_left hfP_uIcc).intervalIntegrable
  -- continuity of the running integrals (with the `b`-end resp. `a`-end fixed)
  have hQMcont : ContinuousOn (fun t => ∫ z in t..b, GM z) (Set.uIcc a b) :=
    intervalIntegral.continuousOn_primitive_interval_left hGM_uIcc
  have hQMcontR : ContinuousOn (fun t => ∫ z in t..b, RM z) (Set.uIcc a b) :=
    intervalIntegral.continuousOn_primitive_interval_left hRM_uIcc
  have hQPcont : ContinuousOn (fun t => ∫ z in a..t, GP z) (Set.uIcc a b) :=
    intervalIntegral.continuousOn_primitive_interval hGP_uIcc
  have hQPcontR : ContinuousOn (fun t => ∫ z in a..t, RP z) (Set.uIcc a b) :=
    intervalIntegral.continuousOn_primitive_interval hRP_uIcc
  -- ## 4. `A` and `Bz` are continuous
  have hAB := Work.FTS.H2.ModalSolR.RGWeak.AB_continuous hα hα1 m hc hcm ha hable
  have hAc : ContinuousOn A (Set.Icc a b) := by rw [hA]; exact hAB.1
  have hBc : ContinuousOn Bz (Set.Icc a b) := by rw [hB]; exact hAB.2
  have hAGM_int : IntervalIntegrable (fun z => A z * GM z) volume a b :=
    (hAc.mul hGMcontI).intervalIntegrable_of_Icc hable
  have hBGP_int : IntervalIntegrable (fun z => Bz z * GP z) volume a b :=
    (hBc.mul hGPcontI).intervalIntegrable_of_Icc hable
  have hARM_int : IntervalIntegrable (fun z => A z * RM z) volume a b :=
    (hAc.mul hRMcontI).intervalIntegrable_of_Icc hable
  have hBRP_int : IntervalIntegrable (fun z => Bz z * RP z) volume a b :=
    (hBc.mul hRPcontI).intervalIntegrable_of_Icc hable
  -- the Fgen values at the two endpoints of the support interval
  have hFa : Fgen α (sM α m) ψ a = 0 :=
    Fgen_eq_zero (hvan a (by simp [Set.mem_Ioo])).1 (hvan a (by simp [Set.mem_Ioo])).2.1
  have hFb : Fgen α (sP α m) ψ b = 0 :=
    Fgen_eq_zero (hvan b (by simp [Set.mem_Ioo])).1 (hvan b (by simp [Set.mem_Ioo])).2.1
  -- ## 5. splitting `A` and `Bz`
  have hA_split : ∀ z ∈ Set.Icc a b, A z = A a + ∫ t in a..z, fM t := by
    intro z hz
    simp only [hA, hfM]
    have hb : 0 < b := lt_of_lt_of_le ha hable
    have h1 : IntervalIntegrable (srcM α m c) volume 0 a := by
      rw [intervalIntegrable_iff, Set.uIoc_of_le ha.le]
      exact (Work.EllipticEst.ModalSolution.RGW.srcM_integrable hα hα1 m hc hcm hb).mono_set
        (fun t ht => ⟨ht.1, le_trans ht.2 hable⟩)
    have h2 : IntervalIntegrable (srcM α m c) volume a z := by
      rw [intervalIntegrable_iff, Set.uIoc_of_le hz.1]
      exact (Work.EllipticEst.ModalSolution.RGW.srcM_integrable hα hα1 m hc hcm hb).mono_set
        (fun t ht => ⟨lt_of_lt_of_le ha ht.1.le, le_trans ht.2 hz.2⟩)
    have h3 := intervalIntegral.integral_add_adjacent_intervals h1 h2
    linarith [h3]
  have hB_split : ∀ z ∈ Set.Icc a b, Bz z = Bz b + ∫ t in z..b, fP t := by
    intro z hz
    simp only [hB, hfP]
    have hdisj : Disjoint (Set.Ioi b) (Set.Ioc z b) := by
      rw [Set.disjoint_left]
      intro t ht1 ht2
      exact absurd ht2.2 (not_le.mpr ht1)
    have hunion : Set.Ioi b ∪ Set.Ioc z b = Set.Ioi z := by
      ext t
      simp only [Set.mem_union, Set.mem_Ioi, Set.mem_Ioc]
      constructor
      · rintro (h | h)
        · exact lt_of_le_of_lt hz.2 h
        · exact h.1
      · intro ht
        by_cases h : t ≤ b
        · exact Or.inr ⟨ht, h⟩
        · exact Or.inl (lt_of_not_ge h)
    have hb_int : IntegrableOn (srcP α m c) (Set.Ioi b) volume :=
      (Work.EllipticEst.ModalSolution.RGW.srcP_integrable hα hα1 m hc hcm ha).mono_set
        (fun t ht => lt_of_le_of_lt hable ht)
    have hz_int : IntegrableOn (srcP α m c) (Set.Ioc z b) volume :=
      (Work.EllipticEst.ModalSolution.RGW.srcP_integrable hα hα1 m hc hcm ha).mono_set
        (fun t ht => lt_of_le_of_lt hz.1 ht.1)
    have hsum := setIntegral_union hdisj measurableSet_Ioc hb_int hz_int
    rw [← hunion, hsum, ← intervalIntegral.integral_of_le hz.2]
  -- ## 6. the four integration-by-parts / Fubini identities
  have hFubiniM : ∫ z in a..b, A z * GM z
      = A a * (∫ z in a..b, GM z) + ∫ t in a..b, fM t * (∫ z in t..b, GM z) := by
    have hsplitpt : ∀ z ∈ Set.Icc a b, A z * GM z = (A a + ∫ t in a..z, fM t) * GM z := by
      intro z hz
      rw [hA_split z hz]
    rw [intervalIntegral.integral_congr (fun z hz => hsplitpt z (huIcc ▸ hz))]
    have h2 := intervalIntegral.integral_add
      (f := fun z => A a * GM z) (g := fun z => (∫ t in a..z, fM t) * GM z)
      (hGMint.const_mul (A a)) (hprimMint.mul_continuousOn hGMcontU)
    rw [show (fun z => (A a + ∫ t in a..z, fM t) * GM z)
        = fun z => A a * GM z + (∫ t in a..z, fM t) * GM z from by funext z; ring]
    rw [h2, intervalIntegral.integral_const_mul]
    rw [Work.EllipticEst.ModalSolution.RGW.primitive_mul_left hable hfM_int hGMint]
  have hFubiniP : ∫ z in a..b, Bz z * GP z
      = Bz b * (∫ z in a..b, GP z) + ∫ t in a..b, fP t * (∫ z in a..t, GP z) := by
    have hsplitpt : ∀ z ∈ Set.Icc a b, Bz z * GP z = (Bz b + ∫ t in z..b, fP t) * GP z := by
      intro z hz
      rw [hB_split z hz]
    rw [intervalIntegral.integral_congr (fun z hz => hsplitpt z (huIcc ▸ hz))]
    have h2 := intervalIntegral.integral_add
      (f := fun z => Bz b * GP z) (g := fun z => (∫ t in z..b, fP t) * GP z)
      (hGPint.const_mul (Bz b)) (hprimPint.mul_continuousOn hGPcontU)
    rw [show (fun z => (Bz b + ∫ t in z..b, fP t) * GP z)
        = fun z => Bz b * GP z + (∫ t in z..b, fP t) * GP z from by funext z; ring]
    rw [h2, intervalIntegral.integral_const_mul]
    rw [Work.EllipticEst.ModalSolution.RGW.primitive_mul_right hable hfP_int hGPint]
  have hFubiniRM : ∫ z in a..b, A z * RM z
      = A a * (∫ z in a..b, RM z) + ∫ t in a..b, fM t * (∫ z in t..b, RM z) := by
    have hsplitpt : ∀ z ∈ Set.Icc a b, A z * RM z = (A a + ∫ t in a..z, fM t) * RM z := by
      intro z hz
      rw [hA_split z hz]
    rw [intervalIntegral.integral_congr (fun z hz => hsplitpt z (huIcc ▸ hz))]
    have h2 := intervalIntegral.integral_add
      (f := fun z => A a * RM z) (g := fun z => (∫ t in a..z, fM t) * RM z)
      (hRMint.const_mul (A a)) (hprimMint.mul_continuousOn hRMcontU)
    rw [show (fun z => (A a + ∫ t in a..z, fM t) * RM z)
        = fun z => A a * RM z + (∫ t in a..z, fM t) * RM z from by funext z; ring]
    rw [h2, intervalIntegral.integral_const_mul]
    rw [Work.EllipticEst.ModalSolution.RGW.primitive_mul_left hable hfM_int hRMint]
  have hFubiniRP : ∫ z in a..b, Bz z * RP z
      = Bz b * (∫ z in a..b, RP z) + ∫ t in a..b, fP t * (∫ z in a..t, RP z) := by
    have hsplitpt : ∀ z ∈ Set.Icc a b, Bz z * RP z = (Bz b + ∫ t in z..b, fP t) * RP z := by
      intro z hz
      rw [hB_split z hz]
    rw [intervalIntegral.integral_congr (fun z hz => hsplitpt z (huIcc ▸ hz))]
    have h2 := intervalIntegral.integral_add
      (f := fun z => Bz b * RP z) (g := fun z => (∫ t in z..b, fP t) * RP z)
      (hRPint.const_mul (Bz b)) (hprimPint.mul_continuousOn hRPcontU)
    rw [show (fun z => (Bz b + ∫ t in z..b, fP t) * RP z)
        = fun z => Bz b * RP z + (∫ t in z..b, fP t) * RP z from by funext z; ring]
    rw [h2, intervalIntegral.integral_const_mul]
    rw [Work.EllipticEst.ModalSolution.RGW.primitive_mul_right hable hfP_int hRPint]
  -- ## 7. the endpoint values of the Lagrange antiderivative
  have hB1 : ∫ z in a..b, GM z = - Work.FTS.PhiStar.Radial.lamR m * (∫ z in a..b, RM z) := by
    have h := Work.FTS.H2.ModalSolR.RGWeak.qm_formula hα m hψ ha hable hvan2 a ⟨le_rfl, hable⟩
    rw [hFa, add_zero] at h
    simpa only [hGM, hRM] using h
  have hB2 : ∫ z in a..b, GP z = - Work.FTS.PhiStar.Radial.lamR m * (∫ z in a..b, RP z) := by
    have h := Work.FTS.H2.ModalSolR.RGWeak.qp_formula hα m hψ ha hable hvan2 b ⟨hable, le_rfl⟩
    rw [hFb, sub_zero] at h
    simpa only [hGP, hRP] using h
  -- ## 8. the two remaining running-integral identities
  have hC1 : ∫ t in a..b, fM t * (∫ z in t..b, GM z)
      = - Work.FTS.PhiStar.Radial.lamR m * (∫ t in a..b, fM t * (∫ z in t..b, RM z))
        + ∫ t in a..b, fM t * Fgen α (sM α m) ψ t := by
    have hcongr : ∫ t in a..b, fM t * (∫ z in t..b, GM z)
        = ∫ t in a..b,
            (-(Work.FTS.PhiStar.Radial.lamR m) * (fM t * (∫ z in t..b, RM z))
              + fM t * Fgen α (sM α m) ψ t) := by
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      rw [Set.uIcc_of_le hable] at ht
      have h := Work.FTS.H2.ModalSolR.RGWeak.qm_formula hα m hψ ha hable hvan2 t ht
      have h' : (∫ z in t..b, GM z)
          = - Work.FTS.PhiStar.Radial.lamR m * (∫ z in t..b, RM z)
            + Fgen α (sM α m) ψ t := by
        simpa only [hGM, hRM] using h
      rw [h']
      ring
    rw [hcongr]
    have h1 := (hfM_int.mul_continuousOn hQMcontR).const_mul (-(Work.FTS.PhiStar.Radial.lamR m))
    have h2 := hfM_int.mul_continuousOn hFgenMcontU
    rw [intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const_mul]
  have hC2 : ∫ t in a..b, fP t * (∫ z in a..t, GP z)
      = - Work.FTS.PhiStar.Radial.lamR m * (∫ t in a..b, fP t * (∫ z in a..t, RP z))
        - ∫ t in a..b, fP t * Fgen α (sP α m) ψ t := by
    have hcongr : ∫ t in a..b, fP t * (∫ z in a..t, GP z)
        = ∫ t in a..b,
            (-(Work.FTS.PhiStar.Radial.lamR m) * (fP t * (∫ z in a..t, RP z))
              - fP t * Fgen α (sP α m) ψ t) := by
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      rw [Set.uIcc_of_le hable] at ht
      have h := Work.FTS.H2.ModalSolR.RGWeak.qp_formula hα m hψ ha hable hvan2 t ht
      have h' : (∫ z in a..t, GP z)
          = - Work.FTS.PhiStar.Radial.lamR m * (∫ z in a..t, RP z)
            - Fgen α (sP α m) ψ t := by
        simpa only [hGP, hRP] using h
      rw [h']
      ring
    rw [hcongr]
    have h1 := (hfP_int.mul_continuousOn hQPcontR).const_mul (-(Work.FTS.PhiStar.Radial.lamR m))
    have h2 := hfP_int.mul_continuousOn hFgenPcontU
    rw [intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const_mul]
  -- ## 9. the pointwise cancellation of the source terms
  have hD : (∫ t in a..b, fM t * Fgen α (sM α m) ψ t)
        - (∫ t in a..b, fP t * Fgen α (sP α m) ψ t)
      = ∫ t in a..b, α * (4 * (m : ℝ) + 5) * (c t * ψ t * wgt α t) := by
    have h1 := hfM_int.mul_continuousOn hFgenMcontU
    have h2 := hfP_int.mul_continuousOn hFgenPcontU
    have hsub := intervalIntegral.integral_sub
      (f := fun t => fM t * Fgen α (sM α m) ψ t)
      (g := fun t => fP t * Fgen α (sP α m) ψ t) h1 h2
    have hcongr : ∫ t in a..b, (fM t * Fgen α (sM α m) ψ t - fP t * Fgen α (sP α m) ψ t)
        = ∫ t in a..b, α * (4 * (m : ℝ) + 5) * (c t * ψ t * wgt α t) := by
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      rw [Set.uIcc_of_le hable] at ht
      have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
      have h := Work.FTS.H2.ModalSolR.RGWeak.Fgen_algebra hα m (c := c) (ψ := ψ) t ht0
      simpa only [hfM, hfP] using h
    exact hsub.symm.trans hcongr
  have hE : ∫ t in a..b, α * (4 * (m : ℝ) + 5) * (c t * ψ t * wgt α t)
      = α * (4 * (m : ℝ) + 5) * (∫ t in a..b, c t * ψ t * wgt α t) := by
    rw [intervalIntegral.integral_const_mul]
  -- ## 10. the middle identity
  have hmid : (A a * (∫ z in a..b, GM z) + ∫ t in a..b, fM t * (∫ z in t..b, GM z))
        + (Bz b * (∫ z in a..b, GP z) + ∫ t in a..b, fP t * (∫ z in a..t, GP z))
        + Work.FTS.PhiStar.Radial.lamR m
          * ((A a * (∫ z in a..b, RM z) + ∫ t in a..b, fM t * (∫ z in t..b, RM z))
            + (Bz b * (∫ z in a..b, RP z) + ∫ t in a..b, fP t * (∫ z in a..t, RP z)))
      = (∫ t in a..b, fM t * Fgen α (sM α m) ψ t)
        - (∫ t in a..b, fP t * Fgen α (sP α m) ψ t) := by
    rw [hB1, hB2, hC1, hC2]
    ring
  -- ## 11. the crux
  have hcrux : ((∫ z in a..b, A z * GM z) + (∫ z in a..b, Bz z * GP z))
        + Work.FTS.PhiStar.Radial.lamR m
          * ((∫ z in a..b, A z * RM z) + (∫ z in a..b, Bz z * RP z))
      = α * (4 * (m : ℝ) + 5) * (∫ t in a..b, c t * ψ t * wgt α t) := by
    rw [hFubiniM, hFubiniP, hFubiniRM, hFubiniRP]
    exact hmid.trans (by rw [hD, hE])
  -- ## 12. rewriting the `radGreen` integrals
  have hT1 : ∫ z in a..b, Work.FTS.PhiStar.Radial.radGreen α m c z * Lneg α ψ z * wgt α z
      = (1 / (α * (4 * (m : ℝ) + 5)))
        * ((∫ z in a..b, A z * GM z) + ∫ z in a..b, Bz z * GP z) := by
    have h1 : ∀ z ∈ Set.Icc a b,
        Work.FTS.PhiStar.Radial.radGreen α m c z * Lneg α ψ z * wgt α z
          = (1 / (α * (4 * (m : ℝ) + 5))) * (A z * GM z + Bz z * GP z) := by
      intro z hz
      rw [Work.EllipticEst.ModalSolution.RadGreenWeak.radGreen_eq, hA, hB, hGM, hGP]
      ring
    rw [intervalIntegral.integral_congr (fun z hz => h1 z (huIcc ▸ hz)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_add hAGM_int hBGP_int]
  have hT2 : ∫ z in a..b, Work.FTS.PhiStar.Radial.radGreen α m c z * ψ z * wgt α z
      = (1 / (α * (4 * (m : ℝ) + 5)))
        * ((∫ z in a..b, A z * RM z) + ∫ z in a..b, Bz z * RP z) := by
    have h1 : ∀ z ∈ Set.Icc a b,
        Work.FTS.PhiStar.Radial.radGreen α m c z * ψ z * wgt α z
          = (1 / (α * (4 * (m : ℝ) + 5))) * (A z * RM z + Bz z * RP z) := by
      intro z hz
      rw [Work.EllipticEst.ModalSolution.RadGreenWeak.radGreen_eq, hA, hB, hRM, hRP]
      ring
    rw [intervalIntegral.integral_congr (fun z hz => h1 z (huIcc ▸ hz)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_add hARM_int hBRP_int]
  -- ## 13. the interval form of the identity
  have hmain : (∫ z in a..b, Work.FTS.PhiStar.Radial.radGreen α m c z * Lneg α ψ z * wgt α z)
        + Work.FTS.PhiStar.Radial.lamR m
          * (∫ z in a..b, Work.FTS.PhiStar.Radial.radGreen α m c z * ψ z * wgt α z)
      = ∫ z in a..b, c z * ψ z * wgt α z := by
    rw [hT1, hT2]
    have hK : (1 / (α * (4 * (m : ℝ) + 5))) * (α * (4 * (m : ℝ) + 5)) = 1 := by
      field_simp
    rw [show (1 / (α * (4 * (m : ℝ) + 5)))
            * ((∫ z in a..b, A z * GM z) + (∫ z in a..b, Bz z * GP z))
          + Work.FTS.PhiStar.Radial.lamR m
            * ((1 / (α * (4 * (m : ℝ) + 5)))
              * ((∫ z in a..b, A z * RM z) + (∫ z in a..b, Bz z * RP z)))
        = (1 / (α * (4 * (m : ℝ) + 5)))
            * (((∫ z in a..b, A z * GM z) + (∫ z in a..b, Bz z * GP z))
              + Work.FTS.PhiStar.Radial.lamR m
                * ((∫ z in a..b, A z * RM z) + (∫ z in a..b, Bz z * RP z))) from by ring]
    rw [hcrux, ← mul_assoc, hK, one_mul]
  -- ## 14. reduction of the original half-line integrals
  have hI1 : (∫ z in Set.Ioi 0, Work.FTS.PhiStar.Radial.radGreen α m c z *
        (-(α ^ 2) * z ^ 2 * deriv (deriv ψ) z - (α * (5 + α) * z) * deriv ψ z)
        * z ^ ((5 - α) / α))
      = ∫ z in a..b, Work.FTS.PhiStar.Radial.radGreen α m c z * Lneg α ψ z * wgt α z := by
    rw [show (∫ z in Set.Ioi 0, Work.FTS.PhiStar.Radial.radGreen α m c z *
            (-(α ^ 2) * z ^ 2 * deriv (deriv ψ) z - (α * (5 + α) * z) * deriv ψ z)
            * z ^ ((5 - α) / α))
        = ∫ z in Set.Ioi 0, Work.FTS.PhiStar.Radial.radGreen α m c z * Lneg α ψ z * wgt α z
        from setIntegral_congr_fun measurableSet_Ioi (fun z _ => by
          simp only [Lneg, wgt, qW]
          ring)]
    exact integral_Ioi_eq_intervalIntegral ha hable (fun z hz => by
      obtain ⟨h0, h1, h2⟩ := hvan z hz
      simp only [Lneg, h0, h1, h2]
      ring)
  have hI2 : (∫ z in Set.Ioi 0, Work.FTS.PhiStar.Radial.radGreen α m c z * ψ z
        * z ^ ((5 - α) / α))
      = ∫ z in a..b, Work.FTS.PhiStar.Radial.radGreen α m c z * ψ z * wgt α z := by
    rw [show (fun z => Work.FTS.PhiStar.Radial.radGreen α m c z * ψ z * z ^ ((5 - α) / α))
        = fun z => Work.FTS.PhiStar.Radial.radGreen α m c z * ψ z * wgt α z from by
          funext z; simp only [wgt, qW]]
    exact integral_Ioi_eq_intervalIntegral ha hable (fun z hz => by
      obtain ⟨h0, -⟩ := hvan z hz
      simp only [h0, mul_zero, zero_mul])
  have hI3 : (∫ z in Set.Ioi 0, c z * ψ z * z ^ ((5 - α) / α))
      = ∫ z in a..b, c z * ψ z * wgt α z := by
    rw [show (fun z => c z * ψ z * z ^ ((5 - α) / α))
        = fun z => c z * ψ z * wgt α z from by funext z; simp only [wgt, qW]]
    exact integral_Ioi_eq_intervalIntegral ha hable (fun z hz => by
      obtain ⟨h0, -⟩ := hvan z hz
      simp only [h0, mul_zero, zero_mul])
  rw [hI1, hI2, hI3]
  exact hmain

end Work.FTS.H2.ModalSolR
