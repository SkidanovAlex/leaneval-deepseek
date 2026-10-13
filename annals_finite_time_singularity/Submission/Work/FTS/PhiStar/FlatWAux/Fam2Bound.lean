/-
# `Work.FTS.PhiStar.FlatWAux.Fam2Bound` — the `D_θ^i ∂_θ`-family of the flat estimate

Clause 2 of `FlatW 7 f` for `f z θ = (z+1)/z · (psiSeries α (RemSource α ψ) z θ / sin 2θ)`:
`|(z+1)^k ∂_z^k (D_θ^i (∂_θ f)) z θ| ≤ C α²` for `k + i + 1 ≤ 7`, with `C` independent of
`α` and `ψ`.

**Route.**  `Fam2DiffId` splits the left-hand side into the finite resummed sum and the
remainder series.  The finite sum is bounded with `PhiAjDivFlat` (`|Rl_j| ≤ CAF`) and
`ChiaLinvLop` (`|Lop^[i](Linv (chia ψ j))| ≤ Kchi j i`); the remainder is bounded termwise with
`RadGreenPhiAjFlat`, `CmodeDecay`, `QmLopBound` and summed with `ModeMajorantLop`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.FTS.PhiStar.FlatWAux.Defs
import Submission.Work.FTS.PhiStar.FlatWAux.Fam2DiffId
import Submission.Work.FTS.PhiStar.FlatWAux.RadGreenPhiAjFlat
import Submission.Work.FTS.PhiStar.FlatWAux.AngBoundU
import Submission.Work.FTS.PhiStar.FlatWAux.QmDerivBound
import Submission.Work.FTS.PhiStar.FlatWAux.QmLopBound
import Submission.Work.FTS.PhiStar.FlatWAux.PhiAjDivFlat
import Submission.Work.FTS.PhiStar.FlatWAux.ModeMajorantLop
import Submission.Work.FTS.PhiStar.FlatWAux.RadGreenExpansionPhiAj
import Submission.Work.FTS.PhiStar.FlatWAux.AngDeriv
import Submission.Work.FTS.PhiStar.FlatWAux.ChiaLinvLop
import Submission.Work.FTS.PhiStar.FlatWAux.ChiaContDiffOn
import Submission.Work.FTS.PhiStar.FlatWAux.MomentChia
import Submission.Work.FTS.PhiStar.FlatWAux.Linv_lop
import Submission.Work.FTS.PhiStar.FlatWAux.PsiExpansion
import Submission.Work.FTS.PhiStar.FlatW_psiDiv
import Submission.Work.FTS.PhiStar.Series.CmodeDecay
import Submission.Work.FTS.PhiStar.FlatWAux.eFamSupBound
import Submission.Work.FTS.PhiStar.FlatWAux.ModeExpansion
import Submission.Work.FTS.PhiStar.Series.RemSetup

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
