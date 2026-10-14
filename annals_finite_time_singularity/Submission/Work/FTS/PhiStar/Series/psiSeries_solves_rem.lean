import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.PhiStar.FlatWAux.Expansion
import Submission.Work.FTS.PhiStar.FlatWAux.Fam2Diff.SummBounds
import Submission.Work.FTS.PhiStar.FlatWAux.QmDerivBound
import Submission.Work.FTS.PhiStar.FlatWAux.QmLopBound
import Submission.Work.FTS.PhiStar.FlatWAux.RadGreenPhiAjFlat
import Submission.Work.FTS.PhiStar.Honesty.radGreen_near_limits_of_le_rpow
import Submission.Work.FTS.PhiStar.LinvI_solves
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.CmodeDecay
import Submission.Work.FTS.PhiStar.Series.Deleg.psiExpansion
import Submission.Work.FTS.PhiStar.Series.Deleg.psiRadFacts
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Series.Weil.Main
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.PhiStar.Series.psiSeries_bslOp
import Submission.Work.FTS.PhiStar.Series.psiTrunc_solves
import Submission.Work.FTS.RegPkgGal.RVocab
import Submission.Work.FTS.RegPkgGal.St1Class
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.H6Aux.RadialAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.fstarDat
import Submission.Work.FTS.StrongPersist.SP6.RadialSlot6
import Submission.Work.FTS.StrongPersist.Star6
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_MuLamOK.Rows.Rl1Defs
import Submission.Work.FTS_RegExport.RXR1.HJ.AKBounds
import Submission.Work.FTS_RegExport.RXT.radial_noDecay_le
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2W.FstarDzIterFourPsiAe
import Submission.Work.H2W.fstarDzIterFourAe
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.sin_two_rpow
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.Fam1Bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.FlatWAux

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem Fam1Bound : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (ψ : ℝ → ℝ), 0 < α → α ≤ 1 / 5 →
    Work.FTS.PhiStar.AngModel α ψ → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
    ∀ k : ℕ, k ≤ 7 →
      |(z + 1) ^ k * Work.Spaces.pzIter k
          (fun z' θ' => (z' + 1) / z' * (Work.FTS.PhiStar.Series.psiSeries α
            (Work.FTS.PhiStar.RemSource α ψ) z' θ' / Work.Construction.s2 θ')) z θ|
        ≤ C * α ^ 2 := by
  obtain ⟨Cd, hCd0, hCd⟩ := Work.FTS.PhiStar.Series.CmodeDecay
  obtain ⟨Cgr, hCgr0, hCgr⟩ := eFamSupBound
  obtain ⟨CQf, hCQf0, hCQf⟩ := QmDerivBound
  obtain ⟨CRG, hCRG0, hRG⟩ := RadGreenPhiAjFlat
  obtain ⟨Kmaj, hKmaj0, hmaj⟩ := ModeMajorant
  obtain ⟨CAF, hCAF0, hAF⟩ := PhiAjDivFlat
  obtain ⟨Kw, KcU, hKw0, hKcU0, hAB⟩ := AngBoundU
  have hlamnn : ∀ m : ℕ, (0 : ℝ) ≤ Work.FTS.PhiStar.Gegenbauer.lam m := fun m => by
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hlam : Work.FTS.PhiStar.Gegenbauer.lam m = 2 * (m : ℝ) * (2 * (m : ℝ) + 5) := rfl
    rw [hlam]
    nlinarith [hm]
  have hKsum0 : (0 : ℝ) ≤ ∑ j ∈ Finset.range J, Kw (j + 1) :=
    Finset.sum_nonneg fun j _ => hKw0 (j + 1)
  refine ⟨8 * 2 ^ 8 * CAF * (∑ j ∈ Finset.range J, Kw (j + 1))
      + Kmaj * Cd * CRG * (CQf 0) + 1, ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ 8 * 2 ^ 8 * CAF * (∑ j ∈ Finset.range J, Kw (j + 1)) :=
      mul_nonneg (by positivity) hKsum0
    have h2 : (0 : ℝ) ≤ Kmaj * Cd * CRG * (CQf 0) :=
      mul_nonneg (mul_nonneg (mul_nonneg hKmaj0 (le_of_lt hCd0)) (le_of_lt hCRG0)) (hCQf0 0)
    linarith
  · intro α ψ hα hα5 hang z θ hz hθ0 hθ2 k hk
    have hθ : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ2⟩
    have hWt : ∀ j : ℕ, j ≤ J → ∀ θ' : ℝ, θ' ∈ Set.Ioo 0 (Real.pi / 2) →
        |Wt ψ j θ'| ≤ Kw j := (hAB α ψ hα hα5 hang).1
    have hb0 : Work.FTS.PhiStar.Series.bmode 0 ψ = 0 := bmode_zero_of_moment hang.moment
    have hdecf : ∀ m : ℕ, 1 ≤ m →
        |Work.FTS.PhiStar.Series.bmode m ψ|
          ≤ Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) :=
      fun m hm => by
        rw [Work.FTS.PhiStar.Series.bmode_eq_cmode m ψ 0]
        exact hCd α ψ hα hα5 hang m hm
    have hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
        |Work.FTS.PhiStar.Series.bmode m ψ|
          ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) :=
      ⟨Cd, hCd0, hdecf⟩
    have hgr : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ' : ℝ), θ' ∈ Work.Spaces.Iθ →
        |Work.FTS.PhiStar.Gegenbauer.eFam m θ'| ≤ C * (2 * (m : ℝ) + 1) :=
      ⟨Cgr, hCgr0, hCgr⟩
    have hrbf : ∀ m : ℕ, 1 ≤ m → ∀ k' : ℕ, k' ≤ 7 → ∀ z' : ℝ, 0 < z' →
        |(z' + 1) ^ k' * iteratedDeriv k' (fun z'' => (z'' + 1) / z''
            * Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z'') z'|
          ≤ CRG / Work.FTS.PhiStar.Gegenbauer.lam m :=
      fun m hm k' hk' z' hz' => hRG.1 α hα hα5 m hm k' hk' z' hz'
    have hrb : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ k' : ℕ, k' ≤ 7 → ∀ z' : ℝ, 0 < z' →
        |(z' + 1) ^ k' * iteratedDeriv k' (fun z'' => (z'' + 1) / z''
            * Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z'') z'|
          ≤ C / Work.FTS.PhiStar.Gegenbauer.lam m :=
      ⟨CRG, hCRG0, hrbf⟩
    have hrbJf : ∀ m : ℕ, 1 ≤ m → ∀ k' : ℕ, k' ≤ 7 → ∀ z' : ℝ, 0 < z' →
        |(z' + 1) ^ k' * iteratedDeriv k' (fun z'' => (z'' + 1) / z''
            * Work.FTS.PhiStar.Radial.radGreen α m
                (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
                  (Work.FTS.VocabO.phiA α)) z'') z'|
          ≤ CRG / Work.FTS.PhiStar.Gegenbauer.lam m :=
      fun m hm k' hk' z' hz' => hRG.2 α hα hα5 m hm k' hk' z' hz'
    have hrbJ : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ k' : ℕ, k' ≤ 7 → ∀ z' : ℝ, 0 < z' →
        |(z' + 1) ^ k' * iteratedDeriv k' (fun z'' => (z'' + 1) / z''
            * Work.FTS.PhiStar.Radial.radGreen α m
                (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
                  (Work.FTS.VocabO.phiA α)) z'') z'|
          ≤ C / Work.FTS.PhiStar.Gegenbauer.lam m :=
      ⟨CRG, hCRG0, hrbJf⟩
    have hexp : ∀ m : ℕ, 1 ≤ m → ∀ z' : ℝ, 0 < z' →
        Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z'
          = (∑ j ∈ Finset.range J, (α ^ j / (Work.FTS.PhiStar.Radial.lamR m) ^ (j + 1))
                * Work.FTS.PhiStar.FlatWAux.Ajit α j (Work.FTS.VocabO.phiA α) z')
            + (α ^ J / (Work.FTS.PhiStar.Radial.lamR m) ^ J)
                * Work.FTS.PhiStar.Radial.radGreen α m
                    (Work.FTS.PhiStar.FlatWAux.Ajit α J (Work.FTS.VocabO.phiA α)) z' :=
      fun m hm z' hz' => RadGreenExpansionPhiAj α hα hα5 m hm z' hz'
    have hid := Fam1Id α ψ z θ hz hθ hb0 hdec hgr hrb hrbJ hexp k hk
    -- the finite (resummed) part
    have hF1 : |∑ j ∈ Finset.range J, α ^ j * ((z + 1) ^ k * iteratedDeriv k
          (fun z'' => (z'' + 1) / z'' * Work.FTS.PhiStar.FlatWAux.Ajit α j
            (Work.FTS.VocabO.phiA α) z'') z) * Wt ψ (j + 1) θ|
        ≤ CAF * (∑ j ∈ Finset.range J, Kw (j + 1)) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j hj => ?_
      have hjJ : j < J := Finset.mem_range.mp hj
      have hj9 : j + 1 ≤ 9 := by simp only [J] at hjJ; omega
      have hR := hAF α hα hα5 (j + 1) hj9 k hk z hz
      rw [← Work.FTS.PhiStar.FlatWAux.Ajit_phiA α j] at hR
      have hW := hWt (j + 1) (by simp only [J] at hjJ ⊢; omega) θ hθ
      have hp : α ^ j ≤ 1 := pow_le_one₀ (le_of_lt hα) (le_trans hα5 (by norm_num))
      rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg (le_of_lt hα) j)]
      calc α ^ j * |(z + 1) ^ k * iteratedDeriv k
              (fun z'' => (z'' + 1) / z'' * Work.FTS.PhiStar.FlatWAux.Ajit α j
                (Work.FTS.VocabO.phiA α) z'') z| * |Wt ψ (j + 1) θ|
          ≤ 1 * CAF * Kw (j + 1) := by
            refine mul_le_mul (mul_le_mul hp hR (abs_nonneg _) (by norm_num))
              hW (abs_nonneg _) (by positivity)
        _ = CAF * Kw (j + 1) := by ring
    -- the remainder series
    have hcmp : ∀ m : ℕ,
        |Work.FTS.PhiStar.Series.bmode m ψ
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
            * ((z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
                * Work.FTS.PhiStar.Radial.radGreen α m
                    (Work.FTS.PhiStar.FlatWAux.Ajit α J (Work.FTS.VocabO.phiA α)) z'') z)
            * Work.FTS.PhiStar.FlatWAux.Qm m θ|
        ≤ Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
            * (CRG / Work.FTS.PhiStar.Gegenbauer.lam m)
            * ((CQf 0) * (2 * (m : ℝ) + 1) ^ 2) := by
      intro m
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · subst hm0
        rw [hb0]
        have hl0 : Work.FTS.PhiStar.Gegenbauer.lam 0 = 0 := by
          simp only [Work.FTS.PhiStar.Gegenbauer.lam]; norm_num
        simp only [abs_zero, zero_mul, hl0, Nat.cast_zero, add_zero, mul_one,
          Work.FTS.PhiStar.FlatWAux.J]
        norm_num
      · have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
        have hlam : 0 < Work.FTS.PhiStar.Gegenbauer.lam m := by
          simp only [Work.FTS.PhiStar.Gegenbauer.lam]; positivity
        have hs2 : 0 < Real.sqrt (2 * (m : ℝ) + 1) := Real.sqrt_pos_of_pos (by linarith)
        have hb := hdecf m hmpos
        have hR := hrbJf m hmpos k hk z hz
        have hQ := hCQf m hmpos 0 (by norm_num : (0 : ℕ) ≤ 8) θ hθ
        simp only [iteratedDeriv_zero] at hQ
        have hQ' : |Work.FTS.PhiStar.FlatWAux.Qm m θ|
            ≤ CQf 0 * (2 * (m : ℝ) + 1) ^ 2 := by
          simpa using hQ
        have hden : 0 < Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1) :=
          mul_pos hlam hs2
        rw [abs_mul, abs_mul, abs_mul,
          abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (le_of_lt hlam)) J)]
        have s1 : |Work.FTS.PhiStar.Series.bmode m ψ| * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
            ≤ (Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J :=
          mul_le_mul_of_nonneg_right hb (by positivity)
        have s2 : |Work.FTS.PhiStar.Series.bmode m ψ| * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
              * |(z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
                  * Work.FTS.PhiStar.Radial.radGreen α m
                      (Work.FTS.PhiStar.FlatWAux.Ajit α J (Work.FTS.VocabO.phiA α)) z'') z|
            ≤ (Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
              * (CRG / Work.FTS.PhiStar.Gegenbauer.lam m) :=
          mul_le_mul s1 hR (abs_nonneg _) (by positivity)
        exact mul_le_mul s2 hQ' (abs_nonneg _) (by positivity)
    have hcmpA : ∀ m : ℕ,
        |Work.FTS.PhiStar.Series.bmode m ψ|
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
            * |(z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
                * Work.FTS.PhiStar.Radial.radGreen α m
                    (Ajit α J (Work.FTS.VocabO.phiA α)) z'') z|
            * |Work.FTS.PhiStar.FlatWAux.Qm m θ|
        ≤ Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
            * (CRG / Work.FTS.PhiStar.Gegenbauer.lam m)
            * ((CQf 0) * (2 * (m : ℝ) + 1) ^ 2) := by
      intro m
      have h := hcmp m
      rw [abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (hlamnn m)) J)] at h
      exact h
    have hHsum : Summable (fun m : ℕ =>
        Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
          * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
          * (CRG / Work.FTS.PhiStar.Gegenbauer.lam m)
          * ((CQf 0) * (2 * (m : ℝ) + 1) ^ 2)) :=
      (hmaj Cd CRG (CQf 0) (le_of_lt hCd0) (le_of_lt hCRG0) (hCQf0 0)).1
    have hHle : (∑' m : ℕ,
        Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
          * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
          * (CRG / Work.FTS.PhiStar.Gegenbauer.lam m)
          * ((CQf 0) * (2 * (m : ℝ) + 1) ^ 2))
        ≤ Kmaj * Cd * CRG * (CQf 0) :=
      (hmaj Cd CRG (CQf 0) (le_of_lt hCd0) (le_of_lt hCRG0) (hCQf0 0)).2
    have hGsum : Summable (fun m : ℕ =>
        ‖Work.FTS.PhiStar.Series.bmode m ψ
          * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
          * ((z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
              * Work.FTS.PhiStar.Radial.radGreen α m
                  (Work.FTS.PhiStar.FlatWAux.Ajit α J (Work.FTS.VocabO.phiA α)) z'') z)
          * Work.FTS.PhiStar.FlatWAux.Qm m θ‖) := by
      refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) hHsum
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (hlamnn m)) J)]
      exact hcmpA m
    have hGsumA : Summable (fun m : ℕ =>
        |Work.FTS.PhiStar.Series.bmode m ψ|
          * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
          * |(z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
              * Work.FTS.PhiStar.Radial.radGreen α m
                  (Work.FTS.PhiStar.FlatWAux.Ajit α J (Work.FTS.VocabO.phiA α)) z'') z|
          * |Work.FTS.PhiStar.FlatWAux.Qm m θ|) :=
      Summable.of_nonneg_of_le (fun m => mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _)
        (pow_nonneg (inv_nonneg.mpr (hlamnn m)) J)) (abs_nonneg _)) (abs_nonneg _)) hcmpA hHsum
    have hF2 : |∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
            * ((z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
                * Work.FTS.PhiStar.Radial.radGreen α m
                    (Work.FTS.PhiStar.FlatWAux.Ajit α J (Work.FTS.VocabO.phiA α)) z'') z)
            * Work.FTS.PhiStar.FlatWAux.Qm m θ|
        ≤ Kmaj * Cd * CRG * (CQf 0) := by
      calc |∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
              * ((z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
                  * Work.FTS.PhiStar.Radial.radGreen α m
                      (Work.FTS.PhiStar.FlatWAux.Ajit α J (Work.FTS.VocabO.phiA α)) z'') z)
              * Work.FTS.PhiStar.FlatWAux.Qm m θ|
          ≤ ∑' m : ℕ, |Work.FTS.PhiStar.Series.bmode m ψ
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
              * ((z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
                  * Work.FTS.PhiStar.Radial.radGreen α m
                      (Work.FTS.PhiStar.FlatWAux.Ajit α J (Work.FTS.VocabO.phiA α)) z'') z)
              * Work.FTS.PhiStar.FlatWAux.Qm m θ| := by
            simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hGsum
        _ = ∑' m : ℕ, |Work.FTS.PhiStar.Series.bmode m ψ|
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
              * |(z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
                  * Work.FTS.PhiStar.Radial.radGreen α m
                      (Work.FTS.PhiStar.FlatWAux.Ajit α J (Work.FTS.VocabO.phiA α)) z'') z|
              * |Work.FTS.PhiStar.FlatWAux.Qm m θ| := by
            refine tsum_congr fun m => ?_
            rw [abs_mul, abs_mul, abs_mul,
              abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (hlamnn m)) J)]
        _ ≤ ∑' m : ℕ, Cd / (Work.FTS.PhiStar.Gegenbauer.lam m
                * Real.sqrt (2 * (m : ℝ) + 1))
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
              * (CRG / Work.FTS.PhiStar.Gegenbauer.lam m)
              * ((CQf 0) * (2 * (m : ℝ) + 1) ^ 2) :=
            Summable.tsum_le_tsum hcmpA hGsumA hHsum
        _ ≤ Kmaj * Cd * CRG * (CQf 0) := hHle
    -- assemble
    rw [hid, abs_mul, abs_of_nonneg (pow_nonneg (le_of_lt hα) 2)]
    have hab : |(∑ j ∈ Finset.range J, α ^ j * ((z + 1) ^ k * iteratedDeriv k
            (fun z'' => (z'' + 1) / z'' * Work.FTS.PhiStar.FlatWAux.Ajit α j
              (Work.FTS.VocabO.phiA α) z'') z) * Wt ψ (j + 1) θ)
          + α ^ J * (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
              * ((z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
                  * Work.FTS.PhiStar.Radial.radGreen α m
                      (Work.FTS.PhiStar.FlatWAux.Ajit α J (Work.FTS.VocabO.phiA α)) z'') z)
              * Work.FTS.PhiStar.FlatWAux.Qm m θ)|
        ≤ CAF * (∑ j ∈ Finset.range J, Kw (j + 1)) + Kmaj * Cd * CRG * (CQf 0) := by
      refine le_trans (abs_add_le _ _) ?_
      have h2 : |α ^ J * (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
              * ((z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
                  * Work.FTS.PhiStar.Radial.radGreen α m
                      (Work.FTS.PhiStar.FlatWAux.Ajit α J (Work.FTS.VocabO.phiA α)) z'') z)
              * Work.FTS.PhiStar.FlatWAux.Qm m θ)|
          ≤ Kmaj * Cd * CRG * (CQf 0) := by
        rw [abs_mul, abs_of_nonneg (pow_nonneg (le_of_lt hα) J)]
        calc α ^ J * |∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
                * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
                * ((z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
                    * Work.FTS.PhiStar.Radial.radGreen α m
                        (Work.FTS.PhiStar.FlatWAux.Ajit α J (Work.FTS.VocabO.phiA α)) z'') z)
                * Work.FTS.PhiStar.FlatWAux.Qm m θ|
            ≤ 1 * |∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
                * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
                * ((z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
                    * Work.FTS.PhiStar.Radial.radGreen α m
                        (Work.FTS.PhiStar.FlatWAux.Ajit α J (Work.FTS.VocabO.phiA α)) z'') z)
                * Work.FTS.PhiStar.FlatWAux.Qm m θ| :=
              mul_le_mul_of_nonneg_right
                (pow_le_one₀ (le_of_lt hα) (le_trans hα5 (by norm_num))) (abs_nonneg _)
          _ = _ := one_mul _
          _ ≤ Kmaj * Cd * CRG * (CQf 0) := hF2
      linarith [hF1, h2]
    have hC1 : CAF * (∑ j ∈ Finset.range J, Kw (j + 1))
        ≤ 8 * 2 ^ 8 * CAF * (∑ j ∈ Finset.range J, Kw (j + 1)) := by
      have h0 : (0 : ℝ) ≤ CAF * (∑ j ∈ Finset.range J, Kw (j + 1)) :=
        mul_nonneg (le_of_lt hCAF0) hKsum0
      nlinarith [h0]
    calc α ^ 2 * |(∑ j ∈ Finset.range J, α ^ j * ((z + 1) ^ k * iteratedDeriv k
              (fun z'' => (z'' + 1) / z'' * Work.FTS.PhiStar.FlatWAux.Ajit α j
                (Work.FTS.VocabO.phiA α) z'') z) * Wt ψ (j + 1) θ)
            + α ^ J * (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
                * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
                * ((z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
                    * Work.FTS.PhiStar.Radial.radGreen α m
                        (Work.FTS.PhiStar.FlatWAux.Ajit α J (Work.FTS.VocabO.phiA α)) z'') z)
                * Work.FTS.PhiStar.FlatWAux.Qm m θ)|
        ≤ α ^ 2 * (CAF * (∑ j ∈ Finset.range J, Kw (j + 1)) + Kmaj * Cd * CRG * (CQf 0)) :=
          mul_le_mul_of_nonneg_left hab (pow_nonneg (le_of_lt hα) 2)
      _ ≤ α ^ 2 * (8 * 2 ^ 8 * CAF * (∑ j ∈ Finset.range J, Kw (j + 1))
            + Kmaj * Cd * CRG * (CQf 0) + 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (le_of_lt hα) 2)
          linarith [hC1]
      _ = (8 * 2 ^ 8 * CAF * (∑ j ∈ Finset.range J, Kw (j + 1))
            + Kmaj * Cd * CRG * (CQf 0) + 1) * α ^ 2 := by ring

end Work.FTS.PhiStar.FlatWAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.Fam2Diff.AngleAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.FlatWAux

section Helpers

/-- `iteratedDeriv r (deriv g) = iteratedDeriv (r+1) g`. -/
lemma iteratedDeriv_deriv_eq (r : ℕ) (g : ℝ → ℝ) :
    iteratedDeriv r (deriv g) = iteratedDeriv (r + 1) g := by
  induction r with
  | zero => rw [iteratedDeriv_zero, Nat.zero_add, iteratedDeriv_one]
  | succ r ih =>
      rw [iteratedDeriv_succ (n := r) (f := deriv g), ih,
        iteratedDeriv_succ (n := r + 1) (f := g)]

/-- The cast comparison `(i+1) + 1 ≤ i + 2` in `WithTop ℕ∞`. -/
lemma cast_succ_le (i : ℕ) :
    ((i + 1 : ℕ) : WithTop ℕ∞) + 1 ≤ ((i + 2 : ℕ) : WithTop ℕ∞) := by
  have h : ((i + 1 : ℕ) : WithTop ℕ∞) + 1 = ((i + 1 + 1 : ℕ) : WithTop ℕ∞) := by
    push_cast
    ring
  rw [h]

/-- `sin 2θ ≠ 0` on the open interval. -/
lemma s2_ne_zero_of_mem {θ' : ℝ} (hθ' : θ' ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Construction.s2 θ' ≠ 0 := by
  rw [Work.Construction.s2_eq, Real.sin_two_mul]
  exact mul_ne_zero
    (mul_ne_zero two_ne_zero
      (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ'.1 (by linarith [hθ'.2, Real.pi_pos]))))
    (ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ'.1], hθ'.2⟩))

/-- Locality of the iterates of `Lop = sin(2θ) ∂_θ` on an open set. -/
lemma Lop_iter_congr (i : ℕ) {u v : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (h : Set.EqOn u v U) : ∀ θ ∈ U, (Work.Spaces.Lop^[i]) u θ = (Work.Spaces.Lop^[i]) v θ := by
  induction i with
  | zero => intro θ hθ; exact h hθ
  | succ i ih =>
      intro θ hθ
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      simp only [Work.Spaces.Lop]
      congr 1
      exact Filter.EventuallyEq.deriv_eq (by
        filter_upwards [hU.mem_nhds hθ] with θ' hθ'
        exact ih θ' hθ')

/-- `Lop^[i]` of a constant multiple (as functions, unconditionally). -/
lemma Lop_iter_const_mul (i : ℕ) (c : ℝ) (u : ℝ → ℝ) :
    (Work.Spaces.Lop^[i]) (fun θ => c * u θ) = fun θ => c * (Work.Spaces.Lop^[i]) u θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      funext θ
      simp only [Work.Spaces.Lop]
      rw [ih, deriv_const_mul_field]
      ring

/-- Smoothness of the rescaled `𝒜^j φ` on `(0,∞)`. -/
lemma contDiffOn_radj (α : ℝ) (j n : ℕ) :
    ContDiffOn ℝ n (fun z' => (z' + 1) / z' * Ajit α j (VocabO.phiA α) z') (Set.Ioi 0) := by
  have h1 : ContDiffOn ℝ n (fun z' : ℝ => (z' + 1) / z') (Set.Ioi 0) :=
    (contDiffOn_id.add contDiffOn_const).div contDiffOn_id (fun z hz => ne_of_gt hz)
  exact h1.mul (contDiffOn_Ajit_phiA α j n)

/-- Smoothness of the rescaled radial Green function on `(0,∞)`. -/
lemma contDiffOn_radJ (α : ℝ) (m n : ℕ) :
    ContDiffOn ℝ n (fun z' => (z' + 1) / z'
      * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z') (Set.Ioi 0) := by
  have h1 : ContDiffOn ℝ n (fun z' : ℝ => (z' + 1) / z') (Set.Ioi 0) :=
    (contDiffOn_id.add contDiffOn_const).div contDiffOn_id (fun z hz => ne_of_gt hz)
  exact h1.mul (contDiffOn_radGreen α m n (contDiffOn_Ajit_phiA α J n))

/-- The purely algebraic rearrangement of the resummed leading terms and the remainder modes:
distributing the factor `(z'+1)/z'` into the radial profiles. -/
lemma psi_alg (α : ℝ) (ψ : ℝ → ℝ) (θ : ℝ) (i : ℕ) (z' : ℝ) :
    ((z' + 1) / z' * α ^ 2)
        * ((∑ j ∈ Finset.range J, α ^ j * Ajit α j (VocabO.phiA α) z'
              * (Work.Spaces.Lop^[i]) (Work.FTS.PhiStar.Linv (chia ψ j)) θ)
          + α ^ J * (∑' m : ℕ, Series.bmode m ψ
              * ((Gegenbauer.lam m)⁻¹) ^ J
              * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z'
              * (Work.Spaces.Lop^[i]) (deriv (Qm m)) θ))
      = α ^ 2 * ((∑ j ∈ Finset.range J, α ^ j * (Work.Spaces.Lop^[i])
              (Work.FTS.PhiStar.Linv (chia ψ j)) θ * ((z' + 1) / z' * Ajit α j (VocabO.phiA α) z'))
          + α ^ J * (∑' m : ℕ, (Series.bmode m ψ
              * ((Gegenbauer.lam m)⁻¹) ^ J
              * (Work.Spaces.Lop^[i]) (deriv (Qm m)) θ)
              * ((z' + 1) / z' * Radial.radGreen α m
                  (Ajit α J (VocabO.phiA α)) z'))) := by
  rw [show ((z' + 1) / z' * α ^ 2)
        * ((∑ j ∈ Finset.range J, α ^ j * Ajit α j (VocabO.phiA α) z'
              * (Work.Spaces.Lop^[i]) (Work.FTS.PhiStar.Linv (chia ψ j)) θ)
          + α ^ J * (∑' m : ℕ, Series.bmode m ψ
              * ((Gegenbauer.lam m)⁻¹) ^ J
              * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z'
              * (Work.Spaces.Lop^[i]) (deriv (Qm m)) θ))
      = α ^ 2 * (((z' + 1) / z')
          * ((∑ j ∈ Finset.range J, α ^ j * Ajit α j (VocabO.phiA α) z'
                * (Work.Spaces.Lop^[i]) (Work.FTS.PhiStar.Linv (chia ψ j)) θ)
            + α ^ J * (∑' m : ℕ, Series.bmode m ψ
                * ((Gegenbauer.lam m)⁻¹) ^ J
                * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z'
                * (Work.Spaces.Lop^[i]) (deriv (Qm m)) θ))) from by ring]
  congr 1
  rw [mul_add]
  congr 1
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  · rw [show (z' + 1) / z' * (α ^ J * (∑' m : ℕ, Series.bmode m ψ
          * ((Gegenbauer.lam m)⁻¹) ^ J
          * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z'
          * (Work.Spaces.Lop^[i]) (deriv (Qm m)) θ))
        = α ^ J * ((z' + 1) / z' * (∑' m : ℕ, Series.bmode m ψ
          * ((Gegenbauer.lam m)⁻¹) ^ J
          * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z'
          * (Work.Spaces.Lop^[i]) (deriv (Qm m)) θ)) from by ring]
    congr 1
    rw [← tsum_mul_left]
    exact tsum_congr (fun m => by ring)

end Helpers

section Angle

/-- **The angular identity.**  For every `z' > 0`, the `i`-fold `D_θ` (preceded by one `∂_θ`) of
the rescaled series is the resummed expression: the leading profiles contribute
`Lop^[i] (Linv (chia ψ j))` and the remainder modes contribute `Lop^[i] (∂_θ Qm m)`. -/
lemma Lop_angle_id (α : ℝ) (ψ : ℝ → ℝ) (θ : ℝ) (i : ℕ) (hi6 : i ≤ 6)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hb0 : Series.bmode 0 ψ = 0)
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Series.bmode m ψ| ≤ C / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ' : ℝ), θ' ∈ Work.Spaces.Iθ →
      |Gegenbauer.eFam m θ'| ≤ C * (2 * (m : ℝ) + 1))
    (hrb : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ, k ≤ 7 → ∀ z' : ℝ, 0 < z' →
      |(z' + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
          * Radial.radGreen α m (VocabO.phiA α) z'') z'| ≤ C / Gegenbauer.lam m)
    (hrbJ : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ, k ≤ 7 → ∀ z' : ℝ, 0 < z' →
      |(z' + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
          * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z'') z'|
        ≤ C / Gegenbauer.lam m)
    (hexp : ∀ m : ℕ, 1 ≤ m → ∀ z' : ℝ, 0 < z' →
      Radial.radGreen α m (VocabO.phiA α) z'
        = (∑ j ∈ Finset.range J,
            (α ^ j / (Radial.lamR m) ^ (j + 1)) * Ajit α j (VocabO.phiA α) z')
          + (α ^ J / (Radial.lamR m) ^ J)
              * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z')
    (hchiasm : ∀ j : ℕ, j ≤ J → ∀ n : ℕ,
      ContDiffOn ℝ n (chia ψ j) (Set.Ioo 0 (Real.pi / 2)))
    (hWtDeriv : ∀ j : ℕ, 1 ≤ j → j ≤ J → ∀ θ' : ℝ, θ' ∈ Set.Ioo 0 (Real.pi / 2) →
      deriv (Wt ψ j) θ' = Work.FTS.PhiStar.Linv (chia ψ (j - 1)) θ') :
    ∀ z' : ℝ, 0 < z' →
      (Work.Spaces.Lop^[i]) (deriv (fun θ'' => (z' + 1) / z'
          * (Series.psiSeries α (RemSource α ψ) z' θ'' / Work.Construction.s2 θ''))) θ
        = ((z' + 1) / z' * α ^ 2)
            * ((∑ j ∈ Finset.range J, α ^ j * Ajit α j (VocabO.phiA α) z'
                  * (Work.Spaces.Lop^[i]) (Work.FTS.PhiStar.Linv (chia ψ j)) θ)
              + α ^ J * (∑' m : ℕ, Series.bmode m ψ
                    * ((Gegenbauer.lam m)⁻¹) ^ J
                    * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z'
                    * (Work.Spaces.Lop^[i]) (deriv (Qm m)) θ)) := by
  obtain ⟨CrJ, hCrJ0, hrbJ'⟩ := hrbJ
  have hrbJ0 : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ, k ≤ 7 → ∀ z' : ℝ, 0 < z' →
      |(z' + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
          * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z'') z'|
        ≤ C / Gegenbauer.lam m := ⟨CrJ, hCrJ0, hrbJ'⟩
  -- smoothness of the rescaled profiles
  have hWt_sm : ∀ j : ℕ, 1 ≤ j → j ≤ J → ∀ n : ℕ,
      ContDiffOn ℝ n (Wt ψ j) (Set.Ioo 0 (Real.pi / 2)) := by
    intro j hj1 hjJ n
    have hs2sm : ContDiffOn ℝ n (Work.Construction.s2) (Set.Ioo 0 (Real.pi / 2)) := by
      show ContDiffOn ℝ n (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2))
      fun_prop
    have hdiv : ContDiffOn ℝ n (fun θ' : ℝ => chia ψ j θ' / Work.Construction.s2 θ')
        (Set.Ioo 0 (Real.pi / 2)) :=
      (hchiasm j hjJ n).div hs2sm (fun θ' hθ' => s2_ne_zero_of_mem hθ')
    refine hdiv.congr (fun θ' hθ' => ?_)
    show Wt ψ j θ' = chia ψ j θ' / Work.Construction.s2 θ'
    rw [chia_eq, eq_div_iff (s2_ne_zero_of_mem hθ')]
    ring
  -- the majorant for the θ-derivatives of the divided modes
  let BQ : ℕ → ℝ := fun m => (2 ^ (2 * 8 + 2) + 100) * (2 * (m : ℝ) + 1) ^ 18 + 2
  have hBQ0 : ∀ m : ℕ, 0 ≤ BQ m := fun m => by
    change (0 : ℝ) ≤ (2 ^ (2 * 8 + 2) + 100) * (2 * (m : ℝ) + 1) ^ 18 + 2
    positivity
  have hQbd : ∀ (m r : ℕ), r ≤ 8 → ∀ θ' : ℝ, θ' ∈ Set.Ioo 0 (Real.pi / 2) →
      |iteratedDeriv r (Qm m) θ'| ≤ BQ m := by
    intro m r hr θ' hθ'
    change |iteratedDeriv r (Qm m) θ'| ≤
      (2 ^ (2 * 8 + 2) + 100) * (2 * (m : ℝ) + 1) ^ 18 + 2
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rcases Nat.eq_zero_or_pos r with rfl | hr1
      · rw [iteratedDeriv_zero, Fam2Diff.QmSmooth.2.1 θ' hθ']
        norm_num
      · rw [Fam2Diff.QmSmooth.2.2 r hr1 θ' hθ', abs_zero]
        positivity
    · rcases Nat.eq_zero_or_pos r with rfl | hr1
      · rw [iteratedDeriv_zero]
        refine le_trans (Qm_sup_bound hm hθ') ?_
        have h1 : (1 : ℝ) ≤ 2 * (m : ℝ) + 1 := by
          have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
          linarith
        have h2 : (2 * (m : ℝ) + 1) ^ 2 ≤ (2 * (m : ℝ) + 1) ^ 18 :=
          pow_le_pow_right₀ h1 (by norm_num)
        have h5 : (0 : ℝ) < 2 * (m : ℝ) + 1 := by linarith
        have h6 : (0 : ℝ) < (2 * (m : ℝ) + 1) ^ 18 := pow_pos h5 18
        have h7 : 100 * (2 * (m : ℝ) + 1) ^ 2 ≤ 100 * (2 * (m : ℝ) + 1) ^ 18 :=
          mul_le_mul_of_nonneg_left h2 (by norm_num)
        have h8 : (100 : ℝ) ≤ 2 ^ (2 * 8 + 2) + 100 := by norm_num
        nlinarith [h6, h7, h8]
      · refine le_trans (Qm_iteratedDeriv_bound (m := m) (l := r) hm hθ') ?_
        have h1 : (1 : ℝ) ≤ 2 * (m : ℝ) + 1 := by
          have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
          linarith
        have h2 : (2 : ℝ) ^ (2 * r + 2) ≤ 2 ^ 18 :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        have h4 : (2 * (m : ℝ) + 1) ^ (r + 3) ≤ (2 * (m : ℝ) + 1) ^ 18 :=
          pow_le_pow_right₀ h1 (by omega)
        have h5 : (0 : ℝ) < 2 * (m : ℝ) + 1 := by linarith
        have h6 : (0 : ℝ) < (2 * (m : ℝ) + 1) ^ 18 := pow_pos h5 18
        have h8 : (2 : ℝ) ^ 18 ≤ 2 ^ (2 * 8 + 2) :=
          pow_le_pow_right₀ (by norm_num) (by norm_num)
        calc 2 ^ (2 * r + 2) * (2 * (m : ℝ) + 1) ^ (r + 3)
            ≤ 2 ^ 18 * (2 * (m : ℝ) + 1) ^ 18 :=
              mul_le_mul h2 h4 (by positivity) (by positivity)
          _ ≤ (2 ^ (2 * 8 + 2) + 100) * (2 * (m : ℝ) + 1) ^ 18 + 2 := by
              nlinarith [h6, h8]
  intro z' hz'
  -- the tail coefficient and the two angular pieces
  let coef : ℕ → ℝ := fun m => Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ J
      * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z'
  let Sf : ℝ → ℝ := fun y => ∑ j ∈ Finset.range J,
      α ^ j * Ajit α j (VocabO.phiA α) z' * Wt ψ (j + 1) y
  let Tf : ℝ → ℝ := fun y => ∑' m : ℕ, coef m * Qm m y
  let Hf : ℝ → ℝ := fun y => Sf y + α ^ J * Tf y
  have hSf_e : Sf = ∑ j ∈ Finset.range J,
      (fun y : ℝ => α ^ j * Ajit α j (VocabO.phiA α) z' * Wt ψ (j + 1) y) := by
    funext y
    show (∑ j ∈ Finset.range J, α ^ j * Ajit α j (VocabO.phiA α) z' * Wt ψ (j + 1) y) = _
    rw [Finset.sum_apply]
  -- summability of the θ-majorant
  have hsumθ : Summable (fun m : ℕ => |Series.bmode m ψ|
      * ((Gegenbauer.lam m)⁻¹) ^ J
      * |Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z'| * BQ m) := by
    change Summable (fun m : ℕ => |Series.bmode m ψ|
      * ((Gegenbauer.lam m)⁻¹) ^ J
      * |Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z'|
        * ((2 ^ (2 * 8 + 2) + 100) * (2 * (m : ℝ) + 1) ^ 18 + 2))
    exact (Fam2Diff.SummBounds hi6 hz' hθ hb0 hdec hrbJ0).1
  have hcBθ : Summable (fun m : ℕ => |coef m| * BQ m) := by
    have hfun : (fun m : ℕ => |coef m| * BQ m) = fun m : ℕ => |Series.bmode m ψ|
        * ((Gegenbauer.lam m)⁻¹) ^ J
        * |Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z'| * BQ m := by
      funext m
      simp only [coef]
      rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (lam_nonneg m)) J)]
    rw [hfun]
    exact hsumθ
  have hQ8 : ∀ m : ℕ, ContDiffOn ℝ 8 (Qm m) (Set.Ioo 0 (Real.pi / 2)) :=
    fun m => Fam2Diff.QmSmooth.1 m
  have hQcd : ∀ m : ℕ, ContDiffOn ℝ (i + 2) (Qm m) (Set.Ioo 0 (Real.pi / 2)) :=
    fun m => (hQ8 m).of_le (by exact_mod_cast (by omega : i + 2 ≤ 8))
  have hTA := Fam2Diff.TsumContDiff (k := i + 2) (c := coef) (q := fun m => Qm m)
    (B := BQ) (a := 0) (b := Real.pi / 2) (by linarith [Real.pi_pos]) hBQ0 hcBθ hQcd
    (fun m r hr θ'' hθ'' => by
      change |iteratedDeriv r (Qm m) θ''| ≤ BQ m
      exact hQbd m r (by omega) θ'' hθ'')
  have hTf_sm : ContDiffOn ℝ (i + 2) Tf (Set.Ioo 0 (Real.pi / 2)) := hTA.1
  have hSf_sm : ContDiffOn ℝ (i + 2) Sf (Set.Ioo 0 (Real.pi / 2)) := by
    refine ContDiffOn.sum (fun j hj => ?_)
    have hjJ : j < J := Finset.mem_range.mp hj
    have hjJ' : j + 1 ≤ J := by simp only [J] at hjJ ⊢; omega
    exact contDiffOn_const.mul (hWt_sm (j + 1) (by omega) hjJ' (i + 2))
  have hHf_sm : ContDiffOn ℝ (i + 2) Hf (Set.Ioo 0 (Real.pi / 2)) :=
    hSf_sm.add (contDiffOn_const.mul hTf_sm)
  have hderivHf_sm : ContDiffOn ℝ (i + 1) (deriv Hf) (Set.Ioo 0 (Real.pi / 2)) :=
    hHf_sm.deriv_of_isOpen isOpen_Ioo (cast_succ_le i)
  have hderivTf_sm : ContDiffOn ℝ (i + 1) (deriv Tf) (Set.Ioo 0 (Real.pi / 2)) :=
    hTf_sm.deriv_of_isOpen isOpen_Ioo (cast_succ_le i)
  have hderivSf_sm : ContDiffOn ℝ (i + 1) (deriv Sf) (Set.Ioo 0 (Real.pi / 2)) :=
    hSf_sm.deriv_of_isOpen isOpen_Ioo (cast_succ_le i)
  -- the `Decomp` hypotheses
  have hQ0 : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ θ' : ℝ,
      θ' ∈ Set.Ioo 0 (Real.pi / 2) → |Qm m θ'| ≤ C * (2 * (m : ℝ) + 1) ^ 2 :=
    ⟨100, by norm_num, fun m hm θ' hθ' => by simpa using Qm_sup_bound hm hθ'⟩
  have hsrc : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ z'' : ℝ, 0 < z'' →
      |(z'' + 1) / z'' * Radial.radGreen α m (VocabO.phiA α) z''| ≤ C / Gegenbauer.lam m := by
    obtain ⟨Cr, hCr0, hrb'⟩ := hrb
    refine ⟨Cr, hCr0, fun m hm z'' hz'' => ?_⟩
    simpa using hrb' m hm 0 (by norm_num) z'' hz''
  have hrem : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ z'' : ℝ, 0 < z'' →
      |(z'' + 1) / z'' * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z''|
        ≤ C / Gegenbauer.lam m := by
    refine ⟨CrJ, hCrJ0, fun m hm z'' hz'' => ?_⟩
    simpa using hrbJ' m hm 0 (by norm_num) z'' hz''
  -- the `Decomp` form of the slice
  have hslice : Set.EqOn
      (fun y => (z' + 1) / z'
        * (Series.psiSeries α (RemSource α ψ) z' y / Work.Construction.s2 y))
      (fun y => (z' + 1) / z' * (α ^ 2 * Hf y)) (Set.Ioo 0 (Real.pi / 2)) := by
    intro y hy
    show (z' + 1) / z' * (Series.psiSeries α (RemSource α ψ) z' y / Work.Construction.s2 y)
      = (z' + 1) / z' * (α ^ 2 * Hf y)
    rw [Decomp α ψ z' y hy hz' hb0 hdec hQ0 hgr hsrc hrem hexp]
  have hderiv_eq : Set.EqOn
      (deriv (fun y => (z' + 1) / z'
        * (Series.psiSeries α (RemSource α ψ) z' y / Work.Construction.s2 y)))
      (fun y => (z' + 1) / z' * α ^ 2 * deriv Hf y) (Set.Ioo 0 (Real.pi / 2)) := by
    intro y hy
    have hev : (fun y => (z' + 1) / z'
        * (Series.psiSeries α (RemSource α ψ) z' y / Work.Construction.s2 y))
        =ᶠ[𝓝 y] (fun y => (z' + 1) / z' * (α ^ 2 * Hf y)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hy] with y' hy'
      exact hslice hy'
    show deriv (fun y => (z' + 1) / z'
        * (Series.psiSeries α (RemSource α ψ) z' y / Work.Construction.s2 y)) y
      = (z' + 1) / z' * α ^ 2 * deriv Hf y
    rw [hev.deriv_eq, deriv_const_mul_field, deriv_const_mul_field]
    ring
  -- the value of `iteratedDeriv (r+1) Sf`
  have hSf_val : ∀ r : ℕ, iteratedDeriv (r + 1) Sf θ
      = ∑ j ∈ Finset.range J, α ^ j * Ajit α j (VocabO.phiA α) z'
          * iteratedDeriv (r + 1) (Wt ψ (j + 1)) θ := by
    intro r
    have hcd : ∀ j ∈ Finset.range J, ContDiffAt ℝ (r + 1)
        (fun y : ℝ => α ^ j * Ajit α j (VocabO.phiA α) z' * Wt ψ (j + 1) y) θ := by
      intro j hj
      have hjJ : j < J := Finset.mem_range.mp hj
      have hjJ' : j + 1 ≤ J := by simp only [J] at hjJ ⊢; omega
      exact (contDiffOn_const.mul (hWt_sm (j + 1) (by omega) hjJ' (r + 1))).contDiffAt
        (isOpen_Ioo.mem_nhds hθ)
    have hsum := iteratedDeriv_sum (n := r + 1) (x := θ) (I := Finset.range J)
      (f := fun j y => α ^ j * Ajit α j (VocabO.phiA α) z' * Wt ψ (j + 1) y) hcd
    rw [hSf_e, hsum]
    exact Finset.sum_congr rfl (fun j _ => by rw [iteratedDeriv_const_mul_field])
  -- the leading contribution
  have hLead : (∑ r ∈ Finset.range (i + 1),
        Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ * iteratedDeriv (r + 1) Sf θ)
      = ∑ j ∈ Finset.range J, α ^ j * Ajit α j (VocabO.phiA α) z'
          * (Work.Spaces.Lop^[i]) (Work.FTS.PhiStar.Linv (chia ψ j)) θ := by
    have hsum_eq : ∀ j : ℕ, j < J →
        (∑ r ∈ Finset.range (i + 1), Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ
            * iteratedDeriv (r + 1) (Wt ψ (j + 1)) θ)
          = (Work.Spaces.Lop^[i]) (Work.FTS.PhiStar.Linv (chia ψ j)) θ := by
      intro j hjJ
      have hj1 : 1 ≤ j + 1 := by omega
      have hjJ' : j + 1 ≤ J := by simp only [J] at hjJ ⊢; omega
      have hgj : ContDiffOn ℝ (i + 1) (deriv (Wt ψ (j + 1))) (Set.Ioo 0 (Real.pi / 2)) :=
        (hWt_sm (j + 1) hj1 hjJ' (i + 2)).deriv_of_isOpen isOpen_Ioo (cast_succ_le i)
      have hWW : (Work.Spaces.Lop^[i]) (deriv (Wt ψ (j + 1))) θ
          = (Work.Spaces.Lop^[i]) (Work.FTS.PhiStar.Linv (chia ψ j)) θ := by
        refine Lop_iter_congr i isOpen_Ioo (fun y hy => ?_) θ hθ
        have h := hWtDeriv (j + 1) hj1 hjJ' y hy
        rw [h, show j + 1 - 1 = j from by omega]
      have hsum_eq' : (∑ r ∈ Finset.range (i + 1),
          Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ
            * iteratedDeriv (r + 1) (Wt ψ (j + 1)) θ)
          = (Work.Spaces.Lop^[i]) (deriv (Wt ψ (j + 1))) θ := by
        rw [Fam2Diff.LopExpansion i isOpen_Ioo hgj θ hθ]
        exact Finset.sum_congr rfl (fun r _ => by rw [iteratedDeriv_deriv_eq])
      rw [hsum_eq', hWW]
    calc ∑ r ∈ Finset.range (i + 1),
            Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ * iteratedDeriv (r + 1) Sf θ
        = ∑ r ∈ Finset.range (i + 1), ∑ j ∈ Finset.range J,
            Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ * (α ^ j
              * Ajit α j (VocabO.phiA α) z' * iteratedDeriv (r + 1) (Wt ψ (j + 1)) θ) := by
          refine Finset.sum_congr rfl (fun r _ => ?_)
          rw [hSf_val r, Finset.mul_sum]
      _ = ∑ j ∈ Finset.range J, ∑ r ∈ Finset.range (i + 1),
            Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ * (α ^ j
              * Ajit α j (VocabO.phiA α) z' * iteratedDeriv (r + 1) (Wt ψ (j + 1)) θ) :=
          Finset.sum_comm
      _ = ∑ j ∈ Finset.range J, (α ^ j * Ajit α j (VocabO.phiA α) z')
            * ∑ r ∈ Finset.range (i + 1),
                Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ
                  * iteratedDeriv (r + 1) (Wt ψ (j + 1)) θ := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun r _ => by ring)
      _ = ∑ j ∈ Finset.range J, α ^ j * Ajit α j (VocabO.phiA α) z'
            * (Work.Spaces.Lop^[i]) (Work.FTS.PhiStar.Linv (chia ψ j)) θ := by
          refine Finset.sum_congr rfl (fun j hj => ?_)
          rw [hsum_eq j (Finset.mem_range.mp hj)]
  -- the tail contribution
  have hTail : (Work.Spaces.Lop^[i]) (deriv Tf) θ
      = ∑' m : ℕ, coef m * (Work.Spaces.Lop^[i]) (deriv (Qm m)) θ := by
    have h := TsumLopDerivU coef (fun m => Qm m) BQ hBQ0 hcBθ hQ8
      (fun m r hr θ'' hθ'' => by
        change |iteratedDeriv r (Qm m) θ''| ≤ BQ m
        exact hQbd m r hr θ'' hθ'') i hi6 θ hθ
    exact h
  -- the total
  have hAll : (Work.Spaces.Lop^[i]) (deriv Hf) θ
      = (∑ j ∈ Finset.range J, α ^ j * Ajit α j (VocabO.phiA α) z'
            * (Work.Spaces.Lop^[i]) (Work.FTS.PhiStar.Linv (chia ψ j)) θ)
        + α ^ J * (∑' m : ℕ, Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ J
            * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z'
            * (Work.Spaces.Lop^[i]) (deriv (Qm m)) θ) := by
    have h1 : (Work.Spaces.Lop^[i]) (deriv Hf) θ
        = ∑ r ∈ Finset.range (i + 1),
            Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ * iteratedDeriv (r + 1) Hf θ := by
      rw [Fam2Diff.LopExpansion i isOpen_Ioo hderivHf_sm θ hθ]
      exact Finset.sum_congr rfl (fun r _ => by rw [iteratedDeriv_deriv_eq])
    have h2 : (∑ r ∈ Finset.range (i + 1),
            Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ * iteratedDeriv (r + 1) Hf θ)
        = (∑ r ∈ Finset.range (i + 1),
              Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ * iteratedDeriv (r + 1) Sf θ)
          + α ^ J * (∑ r ∈ Finset.range (i + 1),
              Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ * iteratedDeriv (r + 1) Tf θ) := by
      have hp : ∀ r ∈ Finset.range (i + 1),
          Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ * iteratedDeriv (r + 1) Hf θ
            = Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ * iteratedDeriv (r + 1) Sf θ
              + α ^ J * (Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ
                  * iteratedDeriv (r + 1) Tf θ) := by
        intro r hr
        have hle' : (r + 1 : ℕ) ≤ i + 2 := by
          have := Finset.mem_range.mp hr
          omega
        have hSf_cd : ContDiffAt ℝ (r + 1) Sf θ :=
          (hSf_sm.contDiffAt (isOpen_Ioo.mem_nhds hθ)).of_le (by exact_mod_cast hle')
        have hTf_cd : ContDiffAt ℝ (r + 1) Tf θ :=
          (hTf_sm.contDiffAt (isOpen_Ioo.mem_nhds hθ)).of_le (by exact_mod_cast hle')
        have hB_cd : ContDiffAt ℝ (r + 1) (fun y => α ^ J * Tf y) θ :=
          contDiffAt_const.mul hTf_cd
        have hHf_eq : Hf = Sf + fun y => α ^ J * Tf y := rfl
        rw [hHf_eq, iteratedDeriv_add hSf_cd hB_cd, iteratedDeriv_const_mul (α ^ J) hTf_cd]
        ring
      calc (∑ r ∈ Finset.range (i + 1),
              Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ * iteratedDeriv (r + 1) Hf θ)
          = ∑ r ∈ Finset.range (i + 1),
              (Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ * iteratedDeriv (r + 1) Sf θ
                + α ^ J * (Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ
                    * iteratedDeriv (r + 1) Tf θ)) := Finset.sum_congr rfl hp
        _ = (∑ r ∈ Finset.range (i + 1),
                Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ * iteratedDeriv (r + 1) Sf θ)
              + ∑ r ∈ Finset.range (i + 1),
                α ^ J * (Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ
                    * iteratedDeriv (r + 1) Tf θ) := Finset.sum_add_distrib
        _ = (∑ r ∈ Finset.range (i + 1),
                Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ * iteratedDeriv (r + 1) Sf θ)
              + α ^ J * (∑ r ∈ Finset.range (i + 1),
                Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ
                  * iteratedDeriv (r + 1) Tf θ) := by rw [Finset.mul_sum]
    have h3 : (∑ r ∈ Finset.range (i + 1),
            Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ * iteratedDeriv (r + 1) Tf θ)
          = ∑' m : ℕ, Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ J
              * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z'
              * (Work.Spaces.Lop^[i]) (deriv (Qm m)) θ := by
      have h2' : (∑ r ∈ Finset.range (i + 1),
            Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ * iteratedDeriv (r + 1) Tf θ)
          = (Work.Spaces.Lop^[i]) (deriv Tf) θ := by
        rw [Fam2Diff.LopExpansion i isOpen_Ioo hderivTf_sm θ hθ]
        exact Finset.sum_congr rfl (fun r _ => by rw [iteratedDeriv_deriv_eq])
      rw [h2', hTail]
    rw [h1, h2, hLead, h3]
  -- the identification of the derivative of the slice
  have hval : (Work.Spaces.Lop^[i]) (deriv (fun θ'' => (z' + 1) / z'
        * (Series.psiSeries α (RemSource α ψ) z' θ'' / Work.Construction.s2 θ''))) θ
      = (z' + 1) / z' * α ^ 2 * (Work.Spaces.Lop^[i]) (deriv Hf) θ := by
    rw [Lop_iter_congr i isOpen_Ioo hderiv_eq θ hθ, Lop_iter_const_mul]
  rw [hval, hAll]

end Angle

end Work.FTS.PhiStar.FlatWAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.Fstar_psiSeries_eq_zero_of_hkMem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false

/-- **The moment of the mode series vanishes, from `ℋ⁰`-honesty of the source.** -/
theorem Fstar_psiSeries_eq_zero_of_hkMem {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {F : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hF : Work.Spaces.HkMem α 0 F)
    (hFs : ∀ t : ℝ, 0 < t → Work.Elliptic.Fstar F t = 0) :
    ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar (Work.FTS.PhiStar.Series.psiSeries α F) z = 0 :=
  fun z hz => Fstar_psiSeries_eq_zero hz (hcoef_psiSeries hα hα4 hsm hF z hz) hFs

end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.psiSeries_solves_rem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series

theorem psiSeries_solves_rem :
    (∀ (α : ℝ) (ψ : ℝ → ℝ), 0 < α → α ≤ 1 / 5 → Work.FTS.PhiStar.AngModel α ψ →
      Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => Work.FTS.PhiStar.Series.psiSeries α (Work.FTS.PhiStar.RemSource α ψ) z θ)) ∧
    (∀ (α : ℝ) (ψ : ℝ → ℝ), 0 < α → α ≤ 1 / 5 → Work.FTS.PhiStar.AngModel α ψ →
      ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 →
        Work.Elliptic.bslOp α
            (fun z θ => Work.FTS.PhiStar.Series.psiSeries α (Work.FTS.PhiStar.RemSource α ψ) z θ)
            z θ = Work.FTS.PhiStar.RemSource α ψ z θ) ∧
    (∀ (α : ℝ) (ψ : ℝ → ℝ), 0 < α → α ≤ 1 / 5 → Work.FTS.PhiStar.AngModel α ψ →
      ∀ z, Work.FTS.PhiStar.Series.psiSeries α (Work.FTS.PhiStar.RemSource α ψ) z 0 = 0 ∧
        Work.FTS.PhiStar.Series.psiSeries α (Work.FTS.PhiStar.RemSource α ψ) z (π / 2) = 0) ∧
    (∀ (α : ℝ) (ψ : ℝ → ℝ), 0 < α → α ≤ 1 / 5 → Work.FTS.PhiStar.AngModel α ψ →
      ∀ θ ∈ Work.Spaces.Iθ,
        Filter.Tendsto
          (fun z => Work.FTS.PhiStar.Series.psiSeries α (Work.FTS.PhiStar.RemSource α ψ) z θ)
          Filter.atTop (nhds 0)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro α ψ hα hα5 hψ
    exact Work.FTS.PhiStar.Series.Weil.smoothOpenR α ψ hα hα5 hψ
  · intro α ψ hα hα5 hψ
    exact psiSeries_bslOp α ψ hα hα5 hψ
  · intro α ψ hα hα5 hψ z
    exact psiSeries_dirichlet_inst α ψ z
  · intro α ψ hα hα5 hψ θ hθ
    exact psiSeries_tendsto_zero_inst α ψ hα hα5 hψ θ hθ

end Work.FTS.PhiStar.Series
end
end
