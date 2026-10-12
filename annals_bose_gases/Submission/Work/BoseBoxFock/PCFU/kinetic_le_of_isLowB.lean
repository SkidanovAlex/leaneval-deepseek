import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.PCFU.SlotPieceDefs
import Submission.Work.BoseBoxFock.PCFU.kinFormBLowParams
import Submission.Work.BoseBoxFock.PCFU.oneBodySplit
import Submission.Work.BoseBoxFock.PCFU.pinDirChiSlotSplit
import Submission.Work.BoseBoxFock.PCFU.windowMassConst_le
import Submission.Work.BoseBoxFock.exists_fderiv_chiScale_bound_inv
import Submission.Work.BoseBoxFock.q2wordAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseBoxFock.PCFU

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## The pointwise dictionary of the fibre derivative -/

lemma sum_norm_fibre_eq_sum_norm_slot {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (i : Fin n) (x : Submission.BoseGases.X n) :
    (∑ k : Fin 3, ‖fderiv ℝ (fun z : E3 => Φ (Function.update x i z)) (x i)
        (EuclideanSpace.single k (1 : ℝ))‖ ^ 2)
      = ∑ k : Fin 3, ‖fderiv ℝ (fun y : Submission.BoseGases.X n => ((Φ y : ℝ) : ℂ)) x
        (slotDirVec i k)‖ ^ 2 := by
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hb := Work.BoseFixB2.Polar.fderiv_fibre_apply (Ξ := Φ) hΦ i x (x i) k
  rw [Function.update_eq_self] at hb
  have h1 : fderiv ℝ (fun z : E3 => Φ (Function.update x i z)) (x i)
        (EuclideanSpace.single k (1 : ℝ))
      = fderiv ℝ Φ x (slotDirVec i k) := by
    change fderiv ℝ (Work.BoseKinLoc.fibre n i Φ x) (x i)
        (Submission.BoseGases.kcStdBasis k)
      = fderiv ℝ Φ x (Function.update (0 : Submission.BoseGases.X n) i
          (Submission.BoseGases.kcStdBasis k))
    exact hb
  rw [h1, Real.norm_eq_abs, sq_abs,
    ← Work.BoseBoxFock.norm_fderiv_ofReal_sq hΦ x (slotDirVec i k)]

theorem kinetic_le_of_isLowB (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R J ε₀ : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < BoseGases.a v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      (R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0 ∧
        2 * R ≤ Work.BoseBoxFock.ellH v μ) →
      J ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))),
        (n : ℝ) ≤ 2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 →
        0 < Work.BoseBoxFix.normB v μ n Φ →
        Work.BoseBoxFix.IsLowB v h J μ n Φ →
        ∀ i : Fin n,
          ∫ x in Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ),
            (Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) (x i)) ^ 2 *
              (∑ k : Fin 3, ‖fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 3) =>
                (Φ : Submission.BoseGases.X n → ℝ) (Function.update x i z)) (x i)
                (EuclideanSpace.single k (1 : ℝ))‖ ^ 2)
          ≤ C * μ ^ 2 * BoseGases.a v * (Work.BoseBoxFock.ellH v μ) ^ 3
              * Work.BoseBoxFix.normB v μ n Φ := by
  obtain ⟨M, hM0, hM⟩ := Work.BoseBoxFock.exists_fderiv_chiScale_bound_inv
  obtain ⟨C₀, hC₀0, hC₀⟩ := kinFormBLowParams (v := v) h hv hv1 hvrad hR hv_supp hav
  refine ⟨4 * C₀ + 4 * Work.BoseFixB1S.chiPlateau ^ 2 + 24 * M ^ 2, ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ 4 * C₀ := by linarith
    have h2 : (0 : ℝ) ≤ 4 * Work.BoseFixB1S.chiPlateau ^ 2 := by positivity
    have h3 : (0 : ℝ) ≤ 24 * M ^ 2 := by positivity
    linarith
  · intro μ hAdm hrange hJ n
    have hμ : 0 < μ := hAdm.1
    have ha : 0 < BoseGases.a v := hav
    have hOK : Work.BoseBox.ParamsOK (Work.BoseBox.paramsAt μ (BoseGases.a v))
        (μ * (BoseGases.a v) ^ 3) := hAdm.2.2
    obtain ⟨hℓpos0, hs_pos, hd_pos, hd_le1, heT0, heT1, hb_pos⟩ :=
      Work.BoseBoxFock.adm_param_facts v hav hAdm
    have hellH : Work.BoseBoxFock.ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) :=
      Work.BoseBoxFock.ellH_eq_sideAt_of_pos hμ ha
    obtain ⟨hRℓ0, h2R⟩ := hrange
    have ht1 : μ * (BoseGases.a v) ^ 3 ≤ 1 := Work.BoseBoxFock.paramsOK_fsParams_le_one hOK
    rw [hellH]
    set ℓ : ℝ := Work.BoseBox.sideAt μ (BoseGases.a v) with hℓdef
    set d : ℝ := (Work.BoseBox.paramsAt μ (BoseGases.a v)).d with hddef
    set s : ℝ := (Work.BoseBox.paramsAt μ (BoseGases.a v)).s with hsdef
    set εT : ℝ := (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT with heTdef
    set b : ℝ := (Work.BoseBox.paramsAt μ (BoseGases.a v)).b with hbdef
    have hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0 := by rw [← hellH]; exact hRℓ0
    intro Φ hnc hnorm hLow i
    have hΦc : ContDiff ℝ (⊤ : ℕ∞) (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff
    have hℓpos : 0 < ℓ := hℓpos0
    have hkpos : 0 < ℓ ^ (-3 : ℤ) := zpow_pos hℓpos _
    have hd_pos' : 0 < d := hd_pos
    have hs_pos' : 0 < s := hs_pos
    have heT0' : 0 ≤ εT := heT0
    have heT1' : εT ≤ 1 := heT1
    have hb_le' : 0 ≤ b := le_of_lt hb_pos
    have hnormB : Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
        = ∫ x in Submission.BoseGases.abox n ℓ, ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 := by
      rw [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
    rw [hnormB]
    have hD0 : 0 ≤ M / ℓ := div_nonneg hM0 hℓpos.le
    have hDbd : ∀ x w : E3, |fderiv ℝ (Submission.BoseGases.chiScale ℓ) x w| ≤ (M / ℓ) * ‖w‖ :=
      fun x w => hM ℓ hℓpos x w
    have h₁ : ∀ ψ : E3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
        (∫ z in Work.BoseK15.corpusBox.boxL ℓ, (Submission.BoseGases.chiScale ℓ z) ^ 2 *
            (∑ j : Fin 3, (fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis j)) ^ 2))
          ≤ 4 * Work.BoseKinLoc.fsT ℓ d s εT b 0 ψ
            + (16 * ((1 - εT) * ((2 * (s * ℓ))⁻¹) ^ 2 + εT * ((2 * (d * s * ℓ))⁻¹) ^ 2)
                * Work.BoseFixB1S.chiPlateau ^ 2 + 24 * (M / ℓ) ^ 2)
              * (∫ z in Work.BoseK15.corpusBox.boxL ℓ, ψ z ^ 2) :=
      oneBodySplit hℓpos hd_pos' hs_pos' hb_le' heT0' heT1' hD0 hDbd
    have hslot := pinDirChiSlotSplit (n := n) (ℓ := ℓ) (d := d) (s := s) (εT := εT) (b := b)
      (Φ := (Φ : Submission.BoseGases.X n → ℝ)) hℓpos hΦc i h₁
    have hcpx : ∀ (w : Submission.BoseGases.X n) (y : Submission.BoseGases.X n),
        fderiv ℝ (fun y : Submission.BoseGases.X n =>
            (((Φ : Submission.BoseGases.X n → ℝ) y : ℝ) : ℂ)) y w
          = ((fderiv ℝ (Φ : Submission.BoseGases.X n → ℝ) y w : ℝ) : ℂ) := by
      intro w y
      have h1 : HasFDerivAt
          (fun y : Submission.BoseGases.X n => (((Φ : Submission.BoseGases.X n → ℝ) y : ℝ) : ℂ))
          ((Complex.ofRealCLM).comp (fderiv ℝ (Φ : Submission.BoseGases.X n → ℝ) y)) y :=
        Complex.ofRealCLM.hasFDerivAt.comp _
          ((hΦc.differentiable (by simp) y).hasFDerivAt)
      rw [h1.fderiv, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
    have hcont (k : Fin 3) : Continuous (fun x : Submission.BoseGases.X n =>
        (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 *
          ‖fderiv ℝ (fun y : Submission.BoseGases.X n =>
              (((Φ : Submission.BoseGases.X n → ℝ) y : ℝ) : ℂ)) x (slotDirVec i k)‖ ^ 2) := by
      have hfun : (fun x : Submission.BoseGases.X n =>
          (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 *
            ‖fderiv ℝ (fun y : Submission.BoseGases.X n =>
                (((Φ : Submission.BoseGases.X n → ℝ) y : ℝ) : ℂ)) x (slotDirVec i k)‖ ^ 2)
          = fun x : Submission.BoseGases.X n =>
              (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 *
                (fderiv ℝ (Φ : Submission.BoseGases.X n → ℝ) x (slotDirVec i k)) ^ 2 := by
        funext x
        rw [hcpx (slotDirVec i k) x, ← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
        ring
      rw [hfun]
      exact (((Submission.BoseGases.chiScale_continuous ℓ).comp (continuous_apply i)).pow 2).mul
        (((hΦc.continuous_fderiv (by simp)).clm_apply continuous_const).pow 2)
    have hpt : ∀ x : Submission.BoseGases.X n,
        (∑ k : Fin 3, ‖fderiv ℝ (fun z : E3 =>
            (Φ : Submission.BoseGases.X n → ℝ) (Function.update x i z)) (x i)
            (EuclideanSpace.single k (1 : ℝ))‖ ^ 2)
          = ∑ k : Fin 3, ‖fderiv ℝ (fun y : Submission.BoseGases.X n =>
              (((Φ : Submission.BoseGases.X n → ℝ) y : ℝ) : ℂ)) x (slotDirVec i k)‖ ^ 2 :=
      fun x => sum_norm_fibre_eq_sum_norm_slot hΦc i x
    have hconv : (∫ x in Submission.BoseGases.abox n ℓ,
          (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 *
            (∑ k : Fin 3, ‖fderiv ℝ (fun z : E3 =>
              (Φ : Submission.BoseGases.X n → ℝ) (Function.update x i z)) (x i)
              (EuclideanSpace.single k (1 : ℝ))‖ ^ 2))
        = ∑ j : Fin 3, ∫ x in Submission.BoseGases.abox n ℓ,
            (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 *
              ‖fderiv ℝ (fun y : Submission.BoseGases.X n =>
                  (((Φ : Submission.BoseGases.X n → ℝ) y : ℝ) : ℂ)) x (slotDirVec i j)‖ ^ 2 := by
      rw [show (∫ x in Submission.BoseGases.abox n ℓ,
            (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 *
              (∑ k : Fin 3, ‖fderiv ℝ (fun z : E3 =>
                (Φ : Submission.BoseGases.X n → ℝ) (Function.update x i z)) (x i)
                (EuclideanSpace.single k (1 : ℝ))‖ ^ 2))
          = ∫ x in Submission.BoseGases.abox n ℓ,
              (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 *
                (∑ k : Fin 3, ‖fderiv ℝ (fun y : Submission.BoseGases.X n =>
                    (((Φ : Submission.BoseGases.X n → ℝ) y : ℝ) : ℂ)) x (slotDirVec i k)‖ ^ 2) from
        MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall (fun x => by dsimp only; rw [hpt x]))]
      rw [show (∫ x in Submission.BoseGases.abox n ℓ,
              (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 *
                (∑ k : Fin 3, ‖fderiv ℝ (fun y : Submission.BoseGases.X n =>
                    (((Φ : Submission.BoseGases.X n → ℝ) y : ℝ) : ℂ)) x (slotDirVec i k)‖ ^ 2))
          = ∫ x in Submission.BoseGases.abox n ℓ, ∑ k : Fin 3,
              (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 *
                ‖fderiv ℝ (fun y : Submission.BoseGases.X n =>
                    (((Φ : Submission.BoseGases.X n → ℝ) y : ℝ) : ℂ)) x (slotDirVec i k)‖ ^ 2 from
        MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall (fun x => by dsimp only; rw [Finset.mul_sum]))]
      rw [MeasureTheory.integral_finsetSum]
      intro k _
      exact integrableOn_abox_of_continuous hℓpos (hcont k)
    have hsingle_nn (j : Fin n) : 0 ≤ ∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x j) *
          Work.BoseKinLoc.fsT ℓ d s εT b 0
            (Work.BoseKinLoc.fibre n j (Φ : Submission.BoseGases.X n → ℝ) x) :=
      integral_nonneg (fun x => mul_nonneg (Work.BoseKinLoc.Word.kinFormB_indU_nonneg ℓ 0 (x j))
        (Work.BoseKinLoc.Word.fsT_nonneg_of_continuous hℓpos hd_pos' hs_pos' heT0' heT1' hb_le' 0
          (Work.BoseKinLoc.Word.kinFormB_fibre_continuous j x hΦc.continuous)))
    have hsingle : ℓ ^ (-3 : ℤ) * (∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x i) *
          Work.BoseKinLoc.fsT ℓ d s εT b 0
            (Work.BoseKinLoc.fibre n i (Φ : Submission.BoseGases.X n → ℝ) x))
        ≤ Work.BoseKinLoc.kinFormB n ℓ d s εT b (Φ : Submission.BoseGases.X n → ℝ) := by
      rw [Work.BoseKinLoc.kinFormB]
      exact mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun j _ => hsingle_nn j) (Finset.mem_univ i))
        (zpow_nonneg hℓpos.le _)
    have hkinB : Work.BoseKinLoc.kinFormB n ℓ d s εT b (Φ : Submission.BoseGases.X n → ℝ)
        ≤ C₀ * (BoseGases.a v) * μ ^ 2 * ℓ ^ 3
            * ∫ x in Submission.BoseGases.abox n ℓ, ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 := by
      have h1 := hC₀ μ hμ hOK hRℓ hJ n Φ hnc hnorm hLow
      rw [hnormB] at h1
      exact h1
    have hℓeq : ℓ = BoseGases.a v * (μ * (BoseGases.a v) ^ 3) ^ (-(163 / 323) : ℝ) :=
      Work.BoseBox.sideAt_eq_rpow ha hμ
    have hdeq : d = (μ * (BoseGases.a v) ^ 3) ^ ((6 : ℝ) / 323) := rfl
    have hseq : s = (μ * (BoseGases.a v) ^ 3) ^ ((1 : ℝ) / 323) := rfl
    have hw := windowMassConst_le (a := BoseGases.a v) (μ := μ) (ℓ := ℓ) (d := d) (s := s)
      (εT := εT) (M := M) (chiP := Work.BoseFixB1S.chiPlateau)
      ha hμ hℓpos hd_pos' hs_pos' heT0' heT1' hM0 Work.BoseFixB1S.chiPlateau_nonneg
      hℓeq hdeq hseq ht1
    have hNnn : 0 ≤ ∫ x in Submission.BoseGases.abox n ℓ,
        ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 :=
      integral_nonneg (fun x => sq_nonneg _)
    have hBmass : (16 * ((1 - εT) * ((2 * (s * ℓ))⁻¹) ^ 2 + εT * ((2 * (d * s * ℓ))⁻¹) ^ 2)
          * Work.BoseFixB1S.chiPlateau ^ 2 + 24 * (M / ℓ) ^ 2)
        * (∫ x in Submission.BoseGases.abox n ℓ, ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2)
        ≤ (4 * Work.BoseFixB1S.chiPlateau ^ 2 + 24 * M ^ 2)
          * (μ ^ 2 * BoseGases.a v * ℓ ^ 3)
          * (∫ x in Submission.BoseGases.abox n ℓ, ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2) :=
      mul_le_mul_of_nonneg_right hw hNnn
    rw [hconv]
    calc (∑ j : Fin 3, ∫ x in Submission.BoseGases.abox n ℓ,
            (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 *
              ‖fderiv ℝ (fun y : Submission.BoseGases.X n =>
                  (((Φ : Submission.BoseGases.X n → ℝ) y : ℝ) : ℂ)) x (slotDirVec i j)‖ ^ 2)
        ≤ 4 * (ℓ ^ (-3 : ℤ) * (∫ x in Submission.BoseGases.abox n ℓ,
              Work.BoseKinLoc.indU ℓ 0 (x i) *
                Work.BoseKinLoc.fsT ℓ d s εT b 0
                  (Work.BoseKinLoc.fibre n i (Φ : Submission.BoseGases.X n → ℝ) x)))
            + (16 * ((1 - εT) * ((2 * (s * ℓ))⁻¹) ^ 2 + εT * ((2 * (d * s * ℓ))⁻¹) ^ 2)
                * Work.BoseFixB1S.chiPlateau ^ 2 + 24 * (M / ℓ) ^ 2)
              * (∫ x in Submission.BoseGases.abox n ℓ,
                  ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2) := hslot
      _ ≤ 4 * (C₀ * (BoseGases.a v) * μ ^ 2 * ℓ ^ 3
              * ∫ x in Submission.BoseGases.abox n ℓ, ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2)
            + (4 * Work.BoseFixB1S.chiPlateau ^ 2 + 24 * M ^ 2)
              * (μ ^ 2 * BoseGases.a v * ℓ ^ 3)
              * (∫ x in Submission.BoseGases.abox n ℓ,
                  ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2) := by
          linarith [hsingle, hkinB, hBmass]
      _ = (4 * C₀ + 4 * Work.BoseFixB1S.chiPlateau ^ 2 + 24 * M ^ 2) * μ ^ 2 * BoseGases.a v
            * ℓ ^ 3 * (∫ x in Submission.BoseGases.abox n ℓ,
                ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2) := by
          ring

end Work.BoseBoxFock.PCFU
