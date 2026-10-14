import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.EllExistHalf
import Submission.Work.FTS.PhiStar.FlatWAux.QmDerivBound
import Submission.Work.FTS.PhiStar.FlatWAux.QmLopBound
import Submission.Work.FTS.PhiStar.FlatWAux.RadGreenPhiAjFlat
import Submission.Work.FTS.PhiStar.Honesty.bslSolExists_moment_of_node_hyp
import Submission.Work.FTS.PhiStar.Honesty.psiTrunc_tendsto_psiSeries
import Submission.Work.FTS.PhiStar.Series.CmodeDecay
import Submission.Work.FTS.PhiStar.Series.Deleg.psiRadFacts
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Series.Weil.Main
import Submission.Work.FTS.PhiStar.Series.psiSeries_bslOp
import Submission.Work.FTS.RegPkgGal.St1Class
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.fstarDat
import Submission.Work.FTS.StrongPersist.SP6.RadialSlot6
import Submission.Work.FTS.StrongPersist.Star6
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.VocabO2
import Submission.Work.H2W.FstarDzIterFourPsiAe
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.Fam2Bound =====
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

theorem Fam2Bound : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (ψ : ℝ → ℝ), 0 < α → α ≤ 1 / 5 →
    Work.FTS.PhiStar.AngModel α ψ → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
    ∀ k i : ℕ, k + i + 1 ≤ 7 →
      |(z + 1) ^ k * Work.Spaces.pzIter k
          (Work.Spaces.DthIter i (Work.Spaces.pth (fun z' θ' => (z' + 1) / z'
            * (Work.FTS.PhiStar.Series.psiSeries α (Work.FTS.PhiStar.RemSource α ψ) z' θ'
              / Work.Construction.s2 θ')))) z θ|
        ≤ C * α ^ 2 := by
  obtain ⟨Cd, hCd0, hCd⟩ := Work.FTS.PhiStar.Series.CmodeDecay
  obtain ⟨Cgr, hCgr0, hCgr⟩ := eFamSupBound
  obtain ⟨CQf, hCQf0, hCQf⟩ := QmDerivBound
  obtain ⟨CRG, hCRG0, hRG⟩ := RadGreenPhiAjFlat
  obtain ⟨KmajL, hKmajL0, hmajL⟩ := ModeMajorantLop
  obtain ⟨CAF, hCAF0, hAF⟩ := PhiAjDivFlat
  obtain ⟨Kw, KcU, hKw0, hKcU0, hAB⟩ := AngBoundU
  obtain ⟨CL, hCL0, hCL⟩ := QmLopBound
  obtain ⟨Kchi, hKchi0, hKchi⟩ := ChiaLinvLop KcU
  obtain ⟨Cfl, hCfl0, hFfl⟩ := FlatW_psiDiv
  obtain ⟨Cpsi, hCpsi0, hPsi⟩ := PsiExpansion
  have hlamnn : ∀ m : ℕ, (0 : ℝ) ≤ Work.FTS.PhiStar.Gegenbauer.lam m := fun m => by
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hlam : Work.FTS.PhiStar.Gegenbauer.lam m = 2 * (m : ℝ) * (2 * (m : ℝ) + 5) := rfl
    rw [hlam]
    nlinarith [hm]
  have hKtot0 : (0 : ℝ) ≤ ∑ j ∈ Finset.range J, ∑ i' ∈ Finset.range 7, Kchi j i' :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i' _ => hKchi0 j i'
  have hKmaj0 : (0 : ℝ) ≤ ∑ i' ∈ Finset.range 7, KmajL i' :=
    Finset.sum_nonneg fun i' _ => hKmajL0 i'
  have hCLt0 : (0 : ℝ) ≤ ∑ i' ∈ Finset.range 7, CL i' :=
    Finset.sum_nonneg fun i' _ => hCL0 i'
  refine ⟨8 * CAF * (∑ j ∈ Finset.range J, ∑ i' ∈ Finset.range 7, Kchi j i')
      + (∑ i' ∈ Finset.range 7, KmajL i') * Cd * CRG * (∑ i' ∈ Finset.range 7, CL i')
      + 1, ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ 8 * CAF * (∑ j ∈ Finset.range J, ∑ i' ∈ Finset.range 7, Kchi j i') :=
      mul_nonneg (by positivity) hKtot0
    have h2 : (0 : ℝ) ≤ (∑ i' ∈ Finset.range 7, KmajL i') * Cd * CRG
        * (∑ i' ∈ Finset.range 7, CL i') :=
      mul_nonneg (mul_nonneg (mul_nonneg hKmaj0 (le_of_lt hCd0)) (le_of_lt hCRG0)) hCLt0
    linarith
  · intro α ψ hα hα5 hang z θ hz hθ0 hθ2 k i hki
    have hθ : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ2⟩
    have hk7 : k ≤ 7 := by omega
    have hi6 : i ≤ 6 := by omega
    have hhQ : ∃ C : ℕ → ℝ, (∀ l : ℕ, 0 ≤ C l) ∧
        ∀ (m : ℕ), 1 ≤ m → ∀ (l : ℕ), l ≤ 8 → ∀ θ' : ℝ, θ' ∈ Set.Ioo 0 (Real.pi / 2) →
          |iteratedDeriv l (Qm m) θ'| ≤ C l * (2 * (m : ℝ) + 1) ^ (2 * l + 2) :=
      ⟨CQf, hCQf0, hCQf⟩
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
    -- smoothness of `ψ` and its boundedness
    have hsmψ : ∀ n : ℕ, ContDiffOn ℝ n ψ (Set.Ioo 0 (Real.pi / 2)) := fun n =>
      hang.smooth.of_le (by
        rw [show Work.Stability.smoothOrder = ((⊤ : ℕ∞) : WithTop ℕ∞) from rfl]
        exact_mod_cast le_top)
    have hbddψ : ∃ M : ℝ, ∀ θ' : ℝ, θ' ∈ Set.Ioo 0 (Real.pi / 2) → |ψ θ'| ≤ M := by
      refine ⟨Cfl, fun θ' hθ' => ?_⟩
      have hF := hFfl α ψ hα (le_trans hα5 (by norm_num)) hang
      have hs2pos : 0 < Work.Construction.s2 θ' := by
        rw [Work.Construction.s2_eq, Real.sin_two_mul]
        exact mul_pos
          (mul_pos two_pos (Real.sin_pos_of_pos_of_lt_pi hθ'.1 (by linarith [Real.pi_pos, hθ'.2])))
          (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ'.1], hθ'.2⟩)
      have hflat := (hF 1 θ' one_pos hθ'.1 hθ'.2).1 0 (by norm_num)
      have h1 : |ψ θ'| = |ψ θ' / Work.Construction.s2 θ'| * |Work.Construction.s2 θ'| := by
        rw [← abs_mul, div_mul_cancel₀]
        exact ne_of_gt hs2pos
      have h2 : |Work.Construction.s2 θ'| ≤ 1 := by
        rw [Work.Construction.s2_eq]
        exact Real.abs_sin_le_one _
      rw [h1]
      calc |ψ θ' / Work.Construction.s2 θ'| * |Work.Construction.s2 θ'|
          ≤ Cfl * 1 := by
            refine mul_le_mul ?_ h2 (abs_nonneg _) (le_of_lt hCfl0)
            simpa using hflat
        _ = Cfl := by ring
    have hchiasm : ∀ j : ℕ, j ≤ J → ∀ n : ℕ,
        ContDiffOn ℝ n (chia ψ j) (Set.Ioo 0 (Real.pi / 2)) :=
      ChiaContDiffOn ψ hdec hgr hsmψ hbddψ hang.moment
    have hhexp : ∀ θ' : ℝ, θ' ∈ Set.Ioo 0 (Real.pi / 2) →
        (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ') = ψ θ' :=
      fun θ' hθ' => hPsi α ψ hα hα5 hang θ' hθ'
    have hWtDeriv : ∀ j : ℕ, 1 ≤ j → j ≤ J → ∀ θ' : ℝ,
        θ' ∈ Set.Ioo 0 (Real.pi / 2) →
        deriv (Wt ψ j) θ' = Work.FTS.PhiStar.Linv (chia ψ (j - 1)) θ' :=
      AngDeriv ψ hdec hgr hhQ ((hsmψ 0).continuousOn) hbddψ hang.moment hhexp
    -- the `chia ψ 0 = ψ` identification on `Iθ`
    have hchia0 : ∀ θ' ∈ Work.Spaces.Iθ, chia ψ 0 θ' = ψ θ' := by
      intro θ' hθ'
      by_cases h : Work.Construction.s2 θ' = 0
      · obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp (by rw [← Work.Construction.s2_eq]; exact h)
        have hge : (0 : ℝ) ≤ (n : ℝ) := by
          have h1 : (0 : ℝ) ≤ (n : ℝ) * Real.pi := by rw [hn]; linarith [hθ'.1]
          exact nonneg_of_mul_nonneg_left h1 Real.pi_pos
        have hle : (n : ℝ) ≤ 1 := by
          have h1 : (n : ℝ) * Real.pi ≤ 1 * Real.pi := by
            rw [one_mul, hn]; linarith [hθ'.2]
          exact le_of_mul_le_mul_right h1 Real.pi_pos
        have hn01 : n = 0 ∨ n = 1 := by
          have h0 : (0 : ℤ) ≤ n := by exact_mod_cast hge
          have h1 : n ≤ (1 : ℤ) := by exact_mod_cast hle
          omega
        have hθ'c : θ' = 0 ∨ θ' = Real.pi / 2 := by
          rcases hn01 with hn0 | hn1
          · left
            have h2 : (2 : ℝ) * θ' = 0 := by rw [← hn, hn0]; ring
            linarith
          · right
            have h2 : (2 : ℝ) * θ' = Real.pi := by rw [← hn, hn1]; ring
            linarith
        rcases hθ'c with rfl | rfl
        · simp only [chia_eq, Wt_zero, Work.Construction.s2_eq, Real.sin_zero, mul_zero,
            zero_div, hang.bdry0]
        · have h2pi : 2 * (Real.pi / 2) = Real.pi := by ring
          simp only [chia_eq, Wt_zero, Work.Construction.s2_eq, h2pi, Real.sin_pi, mul_zero,
            zero_div, hang.bdry1]
      · rw [chia_eq, Wt_zero]
        field_simp
    obtain ⟨hChSm, hChInt, hChMom⟩ := MomentChia ψ hdec hgr hsmψ hbddψ hang.moment
    have hcontSC : ContinuousOn (fun θ' : ℝ => Work.Elliptic.sinCos2 θ') Work.Spaces.Iθ := by
      rw [show (fun θ' : ℝ => Work.Elliptic.sinCos2 θ')
          = fun θ' : ℝ => Real.sin θ' * Real.cos θ' ^ 2 from rfl]
      exact Real.continuous_sin.continuousOn.mul (Real.continuous_cos.continuousOn.pow 2)
    have hIntψ : MeasureTheory.IntegrableOn
        (fun θ' => ψ θ' * Work.Elliptic.sinCos2 θ') Work.Spaces.Iθ :=
      (hang.cont.mul hcontSC).integrableOn_compact isCompact_Icc
    have hint : ∀ j : ℕ, j ≤ J → MeasureTheory.IntegrableOn
        (fun θ' => chia ψ j θ' * Work.Elliptic.sinCos2 θ') Work.Spaces.Iθ := by
      intro j hj
      rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · subst hj0
        refine MeasureTheory.IntegrableOn.congr_fun hIntψ ?_ measurableSet_Icc
        intro θ' hθ'
        show ψ θ' * Work.Elliptic.sinCos2 θ' = chia ψ 0 θ' * Work.Elliptic.sinCos2 θ'
        rw [hchia0 θ' hθ']
      · exact hChInt j hjpos hj
    have hmomI : ∀ j : ℕ, j ≤ J →
        (∫ θ' in Work.Spaces.Iθ, chia ψ j θ' * Work.Elliptic.sinCos2 θ') = 0 := by
      intro j hj
      rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · subst hj0
        have h1 : (∫ θ' in Work.Spaces.Iθ, chia ψ 0 θ' * Work.Elliptic.sinCos2 θ')
            = (∫ θ' in Work.Spaces.Iθ, ψ θ' * Work.Elliptic.sinCos2 θ') := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ' hθ'
          show chia ψ 0 θ' * Work.Elliptic.sinCos2 θ' = ψ θ' * Work.Elliptic.sinCos2 θ'
          rw [hchia0 θ' hθ']
        rw [h1]
        exact hang.moment
      · exact hChMom j hjpos hj
    have hlinvLop : ∀ h : ℝ → ℝ, ContinuousOn h (Set.Ioo 0 (Real.pi / 2)) →
        (∃ M : ℝ, ∀ θ' ∈ Set.Ioo 0 (Real.pi / 2), |h θ'| ≤ M) →
        MeasureTheory.IntegrableOn (fun θ' => h θ' * Work.Elliptic.sinCos2 θ') Work.Spaces.Iθ →
        (∫ θ' in Work.Spaces.Iθ, h θ' * Work.Elliptic.sinCos2 θ') = 0 →
        ∀ θ' ∈ Set.Ioo 0 (Real.pi / 2),
          Work.Spaces.Lop (Work.FTS.PhiStar.Linv h) θ'
            = (6 - 10 * Real.cos θ' ^ 2) * Work.FTS.PhiStar.Linv h θ' - h θ' :=
      fun h hc hb hi hm => Work.FTS.PhiStar.FlatWAux.Linv_lop hc hb hi hm
    have hKcB : ∀ j : ℕ, j ≤ J → ∀ i' : ℕ, i' ≤ 6 → ∀ θ' : ℝ,
        θ' ∈ Set.Ioo 0 (Real.pi / 2) →
        |(Work.Spaces.Lop^[i']) (chia ψ j) θ'| ≤ KcU j i' := (hAB α ψ hα hα5 hang).2
    have hChB : ∀ j : ℕ, j ≤ J → ∀ i' : ℕ, i' ≤ 6 → ∀ θ' : ℝ,
        θ' ∈ Set.Ioo 0 (Real.pi / 2) →
        |(Work.Spaces.Lop^[i']) (Work.FTS.PhiStar.Linv (chia ψ j)) θ'| ≤ Kchi j i' :=
      hKchi ψ hKcB (fun j hj => hchiasm j hj 9) hint hmomI hlinvLop
    have hid := Fam2DiffId α ψ z θ hz hθ hb0 hdec hgr hrb hrbJ hexp hchiasm hWtDeriv k i hki
    rw [hid, abs_mul, abs_of_nonneg (pow_nonneg (le_of_lt hα) 2)]
    -- the resummed finite sum
    have hF1 : |∑ j ∈ Finset.range J, α ^ j * ((z + 1) ^ k * iteratedDeriv k
          (fun z'' => (z'' + 1) / z'' * Ajit α j (Work.FTS.VocabO.phiA α) z'') z)
          * ((Work.Spaces.Lop^[i]) (Work.FTS.PhiStar.Linv (chia ψ j)) θ)|
        ≤ CAF * (∑ j ∈ Finset.range J, ∑ i' ∈ Finset.range 7, Kchi j i') := by
      have hsum : ∀ j ∈ Finset.range J, |α ^ j * ((z + 1) ^ k * iteratedDeriv k
            (fun z'' => (z'' + 1) / z'' * Ajit α j (Work.FTS.VocabO.phiA α) z'') z)
            * ((Work.Spaces.Lop^[i]) (Work.FTS.PhiStar.Linv (chia ψ j)) θ)|
          ≤ CAF * (∑ i' ∈ Finset.range 7, Kchi j i') := by
        intro j hj
        have hjJ : j < J := Finset.mem_range.mp hj
        have hj9 : j + 1 ≤ 9 := by simp only [J] at hjJ; omega
        have hR := hAF α hα hα5 (j + 1) hj9 k hk7 z hz
        rw [← Ajit_phiA α j] at hR
        have hL := hChB j (le_of_lt hjJ) i hi6 θ hθ
        have hKsum : Kchi j i ≤ ∑ i' ∈ Finset.range 7, Kchi j i' :=
          Finset.single_le_sum (fun i' _ => hKchi0 j i') (Finset.mem_range.mpr (by omega))
        have hp : α ^ j ≤ 1 := pow_le_one₀ (le_of_lt hα) (le_trans hα5 (by norm_num))
        rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg (le_of_lt hα) j)]
        calc α ^ j * |(z + 1) ^ k * iteratedDeriv k
                (fun z'' => (z'' + 1) / z'' * Ajit α j (Work.FTS.VocabO.phiA α) z'') z|
              * |(Work.Spaces.Lop^[i]) (Work.FTS.PhiStar.Linv (chia ψ j)) θ|
            ≤ 1 * CAF * (∑ i' ∈ Finset.range 7, Kchi j i') := by
              refine mul_le_mul (mul_le_mul hp hR (abs_nonneg _) (by norm_num)) ?_
                (abs_nonneg _) (by positivity)
              exact le_trans hL hKsum
          _ = CAF * (∑ i' ∈ Finset.range 7, Kchi j i') := by ring
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hsum
    -- the remainder series
    have hcmp : ∀ m : ℕ,
        |Work.FTS.PhiStar.Series.bmode m ψ
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
            * ((z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
                * Work.FTS.PhiStar.Radial.radGreen α m
                    (Ajit α J (Work.FTS.VocabO.phiA α)) z'') z)
            * ((Work.Spaces.Lop^[i]) (deriv (Qm m)) θ)|
        ≤ Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
            * (CRG / Work.FTS.PhiStar.Gegenbauer.lam m)
            * (CL i * (2 * (m : ℝ) + 1) ^ (2 * i + 4)) := by
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
        have hR := hrbJf m hmpos k hk7 z hz
        have hL := hCL m hmpos i hi6 θ hθ
        have hden : 0 < Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1) :=
          mul_pos hlam hs2
        rw [abs_mul, abs_mul, abs_mul,
          abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (le_of_lt hlam)) J)]
        have s1 : |Work.FTS.PhiStar.Series.bmode m ψ|
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
            ≤ (Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J :=
          mul_le_mul_of_nonneg_right hb (by positivity)
        have s2 : |Work.FTS.PhiStar.Series.bmode m ψ|
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
              * |(z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
                  * Work.FTS.PhiStar.Radial.radGreen α m
                      (Ajit α J (Work.FTS.VocabO.phiA α)) z'') z|
            ≤ (Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
              * (CRG / Work.FTS.PhiStar.Gegenbauer.lam m) :=
          mul_le_mul s1 hR (abs_nonneg _) (by positivity)
        exact mul_le_mul s2 hL (abs_nonneg _) (by positivity)
    have hcmpA : ∀ m : ℕ,
        |Work.FTS.PhiStar.Series.bmode m ψ|
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
            * |(z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
                * Work.FTS.PhiStar.Radial.radGreen α m
                    (Ajit α J (Work.FTS.VocabO.phiA α)) z'') z|
            * |(Work.Spaces.Lop^[i]) (deriv (Qm m)) θ|
        ≤ Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
            * (CRG / Work.FTS.PhiStar.Gegenbauer.lam m)
            * (CL i * (2 * (m : ℝ) + 1) ^ (2 * i + 4)) := by
      intro m
      have h := hcmp m
      rw [abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (hlamnn m)) J)] at h
      exact h
    have hHsum : Summable (fun m : ℕ =>
        Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
          * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
          * (CRG / Work.FTS.PhiStar.Gegenbauer.lam m)
          * (CL i * (2 * (m : ℝ) + 1) ^ (2 * i + 4))) :=
      (hmajL Cd CRG (le_of_lt hCd0) (le_of_lt hCRG0) CL hCL0 i hi6).1
    have hHle : (∑' m : ℕ,
        Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
          * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
          * (CRG / Work.FTS.PhiStar.Gegenbauer.lam m)
          * (CL i * (2 * (m : ℝ) + 1) ^ (2 * i + 4)))
        ≤ (∑ i' ∈ Finset.range 7, KmajL i') * Cd * CRG * (∑ i' ∈ Finset.range 7, CL i') := by
      refine le_trans (hmajL Cd CRG (le_of_lt hCd0) (le_of_lt hCRG0) CL hCL0 i hi6).2 ?_
      have hKi : KmajL i ≤ ∑ i' ∈ Finset.range 7, KmajL i' :=
        Finset.single_le_sum (fun i' _ => hKmajL0 i') (Finset.mem_range.mpr (by omega))
      have hCLi : CL i ≤ ∑ i' ∈ Finset.range 7, CL i' :=
        Finset.single_le_sum (fun i' _ => hCL0 i') (Finset.mem_range.mpr (by omega))
      have hCdnn : (0 : ℝ) ≤ Cd := le_of_lt hCd0
      have hCRGnn : (0 : ℝ) ≤ CRG := le_of_lt hCRG0
      calc KmajL i * Cd * CRG * CL i
          ≤ (∑ i' ∈ Finset.range 7, KmajL i') * Cd * CRG * (∑ i' ∈ Finset.range 7, CL i') := by
            have h1 : KmajL i * Cd * CRG ≤ (∑ i' ∈ Finset.range 7, KmajL i') * Cd * CRG := by
              apply mul_le_mul_of_nonneg_right _ hCRGnn
              exact mul_le_mul_of_nonneg_right hKi hCdnn
            exact mul_le_mul h1 hCLi (hCL0 i) (mul_nonneg (mul_nonneg hKmaj0 hCdnn) hCRGnn)
        _ = _ := rfl
    have hGsum : Summable (fun m : ℕ =>
        ‖Work.FTS.PhiStar.Series.bmode m ψ
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
            * ((z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
                * Work.FTS.PhiStar.Radial.radGreen α m
                    (Ajit α J (Work.FTS.VocabO.phiA α)) z'') z)
            * ((Work.Spaces.Lop^[i]) (deriv (Qm m)) θ)‖) := by
      refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) hHsum
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (hlamnn m)) J)]
      exact hcmpA m
    have hGsumA : Summable (fun m : ℕ =>
        |Work.FTS.PhiStar.Series.bmode m ψ|
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
            * |(z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
                * Work.FTS.PhiStar.Radial.radGreen α m
                    (Ajit α J (Work.FTS.VocabO.phiA α)) z'') z|
            * |(Work.Spaces.Lop^[i]) (deriv (Qm m)) θ|) :=
      Summable.of_nonneg_of_le (fun m => mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _)
        (pow_nonneg (inv_nonneg.mpr (hlamnn m)) J)) (abs_nonneg _)) (abs_nonneg _)) hcmpA hHsum
    have hF2 : |∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
            * ((z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
                * Work.FTS.PhiStar.Radial.radGreen α m
                    (Ajit α J (Work.FTS.VocabO.phiA α)) z'') z)
            * ((Work.Spaces.Lop^[i]) (deriv (Qm m)) θ)|
        ≤ (∑ i' ∈ Finset.range 7, KmajL i') * Cd * CRG * (∑ i' ∈ Finset.range 7, CL i') := by
      calc |∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
              * ((z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
                  * Work.FTS.PhiStar.Radial.radGreen α m
                      (Ajit α J (Work.FTS.VocabO.phiA α)) z'') z)
              * ((Work.Spaces.Lop^[i]) (deriv (Qm m)) θ)|
          ≤ ∑' m : ℕ, |Work.FTS.PhiStar.Series.bmode m ψ
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
              * ((z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
                  * Work.FTS.PhiStar.Radial.radGreen α m
                      (Ajit α J (Work.FTS.VocabO.phiA α)) z'') z)
              * ((Work.Spaces.Lop^[i]) (deriv (Qm m)) θ)| := by
            simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hGsum
        _ = ∑' m : ℕ, |Work.FTS.PhiStar.Series.bmode m ψ|
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
              * |(z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
                  * Work.FTS.PhiStar.Radial.radGreen α m
                      (Ajit α J (Work.FTS.VocabO.phiA α)) z'') z|
              * |(Work.Spaces.Lop^[i]) (deriv (Qm m)) θ| := by
            refine tsum_congr fun m => ?_
            rw [abs_mul, abs_mul, abs_mul,
              abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (hlamnn m)) J)]
        _ ≤ ∑' m : ℕ, Cd / (Work.FTS.PhiStar.Gegenbauer.lam m
                * Real.sqrt (2 * (m : ℝ) + 1))
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
              * (CRG / Work.FTS.PhiStar.Gegenbauer.lam m)
              * (CL i * (2 * (m : ℝ) + 1) ^ (2 * i + 4)) :=
            Summable.tsum_le_tsum hcmpA hGsumA hHsum
        _ ≤ (∑ i' ∈ Finset.range 7, KmajL i') * Cd * CRG
              * (∑ i' ∈ Finset.range 7, CL i') := hHle
    have hab : |(∑ j ∈ Finset.range J, α ^ j * ((z + 1) ^ k * iteratedDeriv k
            (fun z'' => (z'' + 1) / z'' * Ajit α j (Work.FTS.VocabO.phiA α) z'') z)
            * ((Work.Spaces.Lop^[i]) (Work.FTS.PhiStar.Linv (chia ψ j)) θ))
          + α ^ J * (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
              * ((z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
                  * Work.FTS.PhiStar.Radial.radGreen α m
                      (Ajit α J (Work.FTS.VocabO.phiA α)) z'') z)
              * ((Work.Spaces.Lop^[i]) (deriv (Qm m)) θ))|
        ≤ CAF * (∑ j ∈ Finset.range J, ∑ i' ∈ Finset.range 7, Kchi j i')
          + (∑ i' ∈ Finset.range 7, KmajL i') * Cd * CRG * (∑ i' ∈ Finset.range 7, CL i') := by
      refine le_trans (abs_add_le _ _) ?_
      have h2 : |α ^ J * (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
              * ((z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
                  * Work.FTS.PhiStar.Radial.radGreen α m
                      (Ajit α J (Work.FTS.VocabO.phiA α)) z'') z)
              * ((Work.Spaces.Lop^[i]) (deriv (Qm m)) θ))|
          ≤ (∑ i' ∈ Finset.range 7, KmajL i') * Cd * CRG * (∑ i' ∈ Finset.range 7, CL i') := by
        rw [abs_mul, abs_of_nonneg (pow_nonneg (le_of_lt hα) J)]
        calc α ^ J * |∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
                * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
                * ((z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
                    * Work.FTS.PhiStar.Radial.radGreen α m
                        (Ajit α J (Work.FTS.VocabO.phiA α)) z'') z)
                * ((Work.Spaces.Lop^[i]) (deriv (Qm m)) θ)|
            ≤ 1 * |∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
                * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
                * ((z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
                    * Work.FTS.PhiStar.Radial.radGreen α m
                        (Ajit α J (Work.FTS.VocabO.phiA α)) z'') z)
                * ((Work.Spaces.Lop^[i]) (deriv (Qm m)) θ)| :=
              mul_le_mul_of_nonneg_right
                (pow_le_one₀ (le_of_lt hα) (le_trans hα5 (by norm_num))) (abs_nonneg _)
          _ = _ := one_mul _
          _ ≤ _ := hF2
      linarith [hF1, h2]
    have hC1 : CAF * (∑ j ∈ Finset.range J, ∑ i' ∈ Finset.range 7, Kchi j i')
        ≤ 8 * CAF * (∑ j ∈ Finset.range J, ∑ i' ∈ Finset.range 7, Kchi j i') := by
      have h0 : (0 : ℝ) ≤ CAF * (∑ j ∈ Finset.range J, ∑ i' ∈ Finset.range 7, Kchi j i') :=
        mul_nonneg (le_of_lt hCAF0) hKtot0
      nlinarith [h0]
    calc α ^ 2 * |(∑ j ∈ Finset.range J, α ^ j * ((z + 1) ^ k * iteratedDeriv k
              (fun z'' => (z'' + 1) / z'' * Ajit α j (Work.FTS.VocabO.phiA α) z'') z)
              * ((Work.Spaces.Lop^[i]) (Work.FTS.PhiStar.Linv (chia ψ j)) θ))
            + α ^ J * (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
                * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
                * ((z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
                    * Work.FTS.PhiStar.Radial.radGreen α m
                        (Ajit α J (Work.FTS.VocabO.phiA α)) z'') z)
                * ((Work.Spaces.Lop^[i]) (deriv (Qm m)) θ))|
        ≤ α ^ 2 * (CAF * (∑ j ∈ Finset.range J, ∑ i' ∈ Finset.range 7, Kchi j i')
            + (∑ i' ∈ Finset.range 7, KmajL i') * Cd * CRG
              * (∑ i' ∈ Finset.range 7, CL i')) :=
          mul_le_mul_of_nonneg_left hab (pow_nonneg (le_of_lt hα) 2)
      _ ≤ α ^ 2 * (8 * CAF * (∑ j ∈ Finset.range J, ∑ i' ∈ Finset.range 7, Kchi j i')
            + (∑ i' ∈ Finset.range 7, KmajL i') * Cd * CRG * (∑ i' ∈ Finset.range 7, CL i')
            + 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (le_of_lt hα) 2)
          linarith [hC1]
      _ = (8 * CAF * (∑ j ∈ Finset.range J, ∑ i' ∈ Finset.range 7, Kchi j i')
            + (∑ i' ∈ Finset.range 7, KmajL i') * Cd * CRG * (∑ i' ∈ Finset.range 7, CL i')
            + 1) * α ^ 2 := by ring

end Work.FTS.PhiStar.FlatWAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.RouteB.bslSolExists_psiSeries_of_node_hyp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.RouteB

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "Q0" => Work.FTS.EllipticEst.Q0
local notation "Iθ" => Work.Spaces.Iθ
local notation "Psis" => Work.FTS.H2.ModalSol.Psi

/-! ## Two angle functions agreeing on the open interval agree a.e. on `Iθ` -/

private lemma ae_imp_eq_of_eqOn_Ioo {f g : ℝ → ℝ}
    (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), f θ = g θ) :
    ∀ᵐ θ ∂volume, θ ∈ Iθ → f θ = g θ := by
  have hμ : volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) = volume.restrict Iθ := by
    rw [Work.Spaces.Iθ]
    exact Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc
  rw [← MeasureTheory.ae_restrict_iff' (s := Iθ)
    (show MeasurableSet Iθ from measurableSet_Icc), ← hμ]
  exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mpr
    (Filter.Eventually.of_forall (fun x hx => h x hx))

/-! ## Locality of the mode series in the source -/

/-- `radGreen` only sees the values of its source on the open half-line `(0,∞)`: for `z > 0`
both integrals range over positive arguments only. -/
private lemma radGreen_congr_Ioi {α : ℝ} (m : ℕ) {f g : ℝ → ℝ}
    (h : ∀ t : ℝ, 0 < t → f t = g t) {z : ℝ} (hz : 0 < z) :
    Work.FTS.PhiStar.Radial.radGreen α m f z
      = Work.FTS.PhiStar.Radial.radGreen α m g z := by
  have h1 : (∫ t in (0 : ℝ)..z, f t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      = (∫ t in (0 : ℝ)..z, g t * t ^ ((2 * (m : ℝ) + 5) / α - 1)) := by
    rw [intervalIntegral.integral_of_le hz.le, intervalIntegral.integral_of_le hz.le]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun t ht => by rw [h t ht.1])
  have h2 : (∫ t in Set.Ioi z, f t * t ^ (-(2 * (m : ℝ) / α) - 1))
      = (∫ t in Set.Ioi z, g t * t ^ (-(2 * (m : ℝ) / α) - 1)) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun t ht => by rw [h t (lt_trans hz ht)])
  simp only [Work.FTS.PhiStar.Radial.radGreen, h1, h2]

/-- The clamped source `clampQ F` has, at `z > 0`, the same mode coefficients as `F`. -/
private lemma cmode_clampQ (m : ℕ) {F : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z) :
    Work.FTS.PhiStar.Series.cmode m (Work.FTS.PhiStar.clampQ F) z
      = Work.FTS.PhiStar.Series.cmode m F z := by
  have hn : (∫ θ in (0 : ℝ)..(Real.pi / 2),
        (Work.FTS.PhiStar.clampQ F) z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
      = (∫ θ in (0 : ℝ)..(Real.pi / 2),
        F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) := by
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    simp only [Work.FTS.PhiStar.clampQ, if_pos hz]
  rw [Work.FTS.PhiStar.Series.cmode, Work.FTS.PhiStar.Series.cmode, hn]

/-- The mode-`m` radial coefficient is the same for `clampQ F` and `F` at `z > 0`. -/
private lemma acoeff_clampQ (α : ℝ) (m : ℕ) {F : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z) :
    Work.FTS.PhiStar.Series.acoeff α m (Work.FTS.PhiStar.clampQ F) z
      = Work.FTS.PhiStar.Series.acoeff α m F z := by
  rw [Work.FTS.PhiStar.Series.acoeff, Work.FTS.PhiStar.Series.acoeff]
  exact radGreen_congr_Ioi m (fun t ht => cmode_clampQ m ht) hz

/-- **The mode series only sees its source on `z > 0`**: the clamped source has the same series
as `F` in the open half-plane `z > 0`. -/
private lemma psiSeries_clampQ (α : ℝ) {F : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z) :
    Work.FTS.PhiStar.Series.psiSeries α (Work.FTS.PhiStar.clampQ F) z θ
      = Work.FTS.PhiStar.Series.psiSeries α F z θ := by
  refine tsum_congr (fun m => ?_)
  rw [acoeff_clampQ α m hz]

/-! ## The theorem -/

theorem bslSolExists_psiSeries_of_node_hyp (k : ℕ) :
    ∀ (α : ℝ) (F : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.SmoothOpen F → Work.Spaces.HkMem α k F →
      (∀ z : ℝ, 0 < z → Work.Elliptic.Fstar F z = 0) →
      (∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun z => F z θ) Filter.atTop (nhds 0)) →
      ∃ Ψ : ℝ → ℝ → ℝ,
        Work.FTS.EllipticEst.SmoothOpen Ψ ∧ Work.Elliptic.IsBslSol α F Ψ ∧
          (∀ z : ℝ, 0 < z → Work.Elliptic.Fstar Ψ z = 0) ∧
          (∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
            Ψ z θ = Work.FTS.PhiStar.Series.psiSeries α F z θ) := by
  intro α F hα hα4 hsm hk horth hdec
  have hα1 : α ≤ 1 := by linarith
  -- ## the clamped source `G = clampQ F` and its `ℋ^0`-data
  have h0F : Work.Spaces.HkMem α 0 F :=
    Work.FTS.OpenPkg.HkMem_mono_open hsm 0 (Nat.zero_le k) hk
  have hsmG : Work.FTS.EllipticEst.SmoothOpen (clampQ F) := smoothOpen_clampQ hsm
  have horthG : Work.Elliptic.OrthCond (clampQ F) := orthCond_clampQ horth
  have h0G : Work.Spaces.HkMem α 0 (clampQ F) :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 0 h0F
      (fun z hz θ hθ => by simp only [clampQ]; rw [if_pos (show (0 : ℝ) < z from hz)])
  have hL2F : IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2) Q0 :=
    integrableOn_sq_Q0_of_HkMem h0F hsm
  have hL2G : IntegrableOn (fun p : ℝ × ℝ => (clampQ F) p.1 p.2 ^ 2) Q0 := by
    refine hL2F.congr_fun ?_ Work.FTS.EllipticEst.isOpen_Q0.measurableSet
    intro p hp
    obtain ⟨hz, -, -⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    show (F p.1 p.2) ^ 2 = ((if 0 < p.1 then F p.1 p.2 else 0)) ^ 2
    rw [if_pos hz]
  have hfstG : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar (clampQ F) z = 0 := by
    intro z hz
    rw [fstar_clampQ, if_pos hz]
    exact horth z hz
  -- ## the modal weak solution `Ψ` and its properties (all clean statements)
  have hcontΨ : ContinuousOn (Function.uncurry (Psis α (clampQ F))) Q0 :=
    Honesty.NodeAux.continuousOn_uncurry_Psi_mod α hα hα1 horthG hsmG hL2G
  have hΨli : LocallyIntegrableOn (Function.uncurry (Psis α (clampQ F))) Q0 :=
    hcontΨ.locallyIntegrableOn Work.FTS.EllipticEst.isOpen_Q0.measurableSet
  have hΨdec : ∀ θ ∈ Iθ, Tendsto (fun z => Psis α (clampQ F) z θ) atTop (nhds 0) :=
    Honesty.NodeAux.Psi_tendsto_atTop_zero_mod α hα hα1 horthG hsmG hL2G
  have hΨslice : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      ContinuousOn (fun θ => Psis α (clampQ F) z θ) (Set.Ioo 0 (π / 2)) := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall (fun z hz =>
      Work.FTS.H2.ModalSolR.Psi_slice_continuous α hα hα1 horthG hsmG hL2G hz)
  -- ## interior regularity: the smooth representative `Φ`
  obtain ⟨Φ, hΦsm, hΦae⟩ :=
    Work.EllipticEst.InteriorRegularity.Q0.interiorSmoothQ0_fts hα hsmG hΨli
      (fun φ hφ hcφ hsub =>
        Work.FTS.H2.ModalSolR.psi_weak_identity α hα hα1 horthG hsmG hL2G hφ hcφ hsub)
  -- ## the pointwise equation for `Φ`
  have hΦeq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 →
      Work.Elliptic.bslOp α Φ z θ = clampQ F z θ := by
    refine Work.EllipticEst.Assembly.bslOp_eq_of_weak_of_smooth hα hΦsm hsmG ?_
    intro φ hφ hcφ hsub
    rw [← Work.FTS.H2.ModalSolR.psi_weak_identity α hα hα1 horthG hsmG hL2G hφ hcφ hsub]
    refine MeasureTheory.setIntegral_congr_ae Work.FTS.EllipticEst.isOpen_Q0.measurableSet ?_
    rw [← MeasureTheory.ae_restrict_iff' Work.FTS.EllipticEst.isOpen_Q0.measurableSet]
    refine hΦae.symm.mono (fun p hp => ?_)
    have hp' : Φ p.1 p.2 = Psis α (clampQ F) p.1 p.2 := hp
    show Φ p.1 p.2 * (Work.Elliptic.bslOp α φ p.1 p.2) * (p.1 ^ ((5 - α) / α) * Real.cos p.2)
       = Psis α (clampQ F) p.1 p.2 * (Work.Elliptic.bslOp α φ p.1 p.2)
         * (p.1 ^ ((5 - α) / α) * Real.cos p.2)
    rw [hp']
  -- ## `Φ = Ψ` on the open quadrant (both continuous there, equal a.e.)
  have hcontΦ : ContinuousOn (Function.uncurry Φ) Q0 := hΦsm.continuousOn
  have hEqOn : Set.EqOn (Function.uncurry Φ) (Function.uncurry (Psis α (clampQ F))) Q0 :=
    MeasureTheory.Measure.eqOn_open_of_ae_eq hΦae.symm Work.FTS.EllipticEst.isOpen_Q0
      hcontΦ hcontΨ
  have hΦΨ : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → Φ z θ = Psis α (clampQ F) z θ :=
    fun z θ hz hθ hθ2 => hEqOn (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ2⟩)
  -- ## the decay of `Φ`
  have hΦdec : ∀ θ ∈ Set.Ioo 0 (π / 2), Tendsto (fun z => Φ z θ) atTop (nhds 0) :=
    Work.FTS.H2.PhiStarE5.smoothRep_decay hΦsm hΦae.symm hΨslice hΨdec
  -- ## on the quadrant, `Ψ` is the mode series of `G`
  have hPsiSeries : ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Psis α (clampQ F) z θ = Work.FTS.PhiStar.Series.psiSeries α (clampQ F) z θ := by
    intro z θ hz hθ
    exact tendsto_nhds_unique
      (Work.FTS.H2.ModalSolR.psiTrunc_tendsto_Psi α hα hα1 horthG hsmG hL2G hz hθ)
      (Honesty.psiTrunc_tendsto_psiSeries hα hα1 hfstG hsmG hL2G hz hθ)
  -- ## the witness
  refine ⟨fun z θ => if θ ∈ Set.Ioo 0 (π / 2) then Φ z θ else 0, ?_, ?_, ?_, ?_⟩
  · -- `SmoothOpen`
    refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
    refine (hΦsm.forall n).congr (fun p hp => ?_)
    obtain ⟨-, h1, h2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    show (if p.2 ∈ Set.Ioo 0 (π / 2) then Φ p.1 p.2 else 0) = Φ p.1 p.2
    rw [if_pos ⟨h1, h2⟩]
  · -- `IsBslSol α F`
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro z hz θ hθ0 hθ2
      have hev : ∀ᶠ q in 𝓝 (z, θ),
          (if q.2 ∈ Set.Ioo 0 (π / 2) then Φ q.1 q.2 else 0) = Φ q.1 q.2 := by
        have hnb : ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (π / 2)) ∈ 𝓝 (z, θ) :=
          (isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨trivial, hθ0, hθ2⟩
        exact Filter.mem_of_superset hnb (fun q hq => if_pos hq.2)
      rw [Work.FTS.H2.PhiStarE5.bslOp_congr_of_eventuallyEq α hev, hΦeq z hz θ hθ0 hθ2]
      show (if 0 < z then F z θ else 0) = F z θ
      rw [if_pos hz]
    · intro z; exact if_neg (by simp)
    · intro z; exact if_neg (by simp [Real.pi_pos])
    · intro θ hθ
      rcases eq_or_lt_of_le hθ.1 with h | h
      · subst h
        have hz : (fun z : ℝ => (if (0 : ℝ) ∈ Set.Ioo 0 (π / 2) then Φ z 0 else 0))
            = fun _ => 0 := by
          funext z; exact if_neg (by simp)
        rw [hz]; exact tendsto_const_nhds
      · rcases eq_or_lt_of_le hθ.2 with h2 | h2
        · subst h2
          have hz : (fun z : ℝ =>
                (if Real.pi / 2 ∈ Set.Ioo 0 (Real.pi / 2) then Φ z (π / 2) else 0))
              = fun _ => 0 := by
            funext z; exact if_neg (by simp [Real.pi_pos])
          rw [hz]; exact tendsto_const_nhds
        · have hif : ∀ z : ℝ, (if θ ∈ Set.Ioo 0 (π / 2) then Φ z θ else 0) = Φ z θ :=
            fun z => if_pos ⟨h, h2⟩
          exact Tendsto.congr' (Eventually.of_forall (fun z => (hif z).symm))
            (hΦdec θ ⟨h, h2⟩)
  · -- the angular moment, from the mode series
    intro z hz
    have heq : Work.Elliptic.Fstar
          (fun z θ => if θ ∈ Set.Ioo 0 (π / 2) then Φ z θ else 0) z
        = Work.Elliptic.Fstar (Work.FTS.PhiStar.Series.psiSeries α F) z := by
      rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar]
      refine MeasureTheory.setIntegral_congr_ae measurableSet_Icc ?_
      refine ae_imp_eq_of_eqOn_Ioo (fun θ hθ => ?_)
      rw [if_pos hθ, hΦΨ z θ hz hθ.1 hθ.2, hPsiSeries z θ hz hθ, psiSeries_clampQ α hz]
    rw [heq]
    exact Honesty.Fstar_psiSeries_eq_zero_of_hkMem hα hα4 hsm h0F horth z hz
  · -- the mode-series identity on the open quadrant
    intro z hz θ hθ0 hθ1
    show (if θ ∈ Set.Ioo 0 (π / 2) then Φ z θ else 0)
      = Work.FTS.PhiStar.Series.psiSeries α F z θ
    rw [if_pos ⟨hθ0, hθ1⟩, hΦΨ z θ hz hθ0 hθ1, hPsiSeries z θ hz ⟨hθ0, hθ1⟩,
      psiSeries_clampQ α hz]

end Work.FTS.PhiStar.RouteB
end
end
