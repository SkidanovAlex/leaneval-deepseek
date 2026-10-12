import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BSKinetic.Basic
import Submission.Work.BSKinetic.SlotAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Topology Real BigOperators ENNReal

namespace Work.BSKinetic.SlotSwap

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 8000000

/-! ## The slot fibre of a smooth state is smooth -/

private lemma contDiff_slotState1_aux {n : ℕ} {Φ : Submission.BoseGases.X (n + 1) → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) (r : Submission.BoseGases.X n) :
    ContDiff ℝ (⊤ : ENat) (Work.BSKinetic.slotState1 i Φ r) := by
  have hfib : ContDiff ℝ (⊤ : ENat)
      (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z, r))) :=
    hΦ.comp (Work.SmallBoxBridge.Fourier.contDiff_kcInsN_right i r)
  have h : Work.BSKinetic.slotState1 i Φ r
      = (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z, r)))
        ∘ (fun x : Submission.BoseGases.X 1 => x 0) := rfl
  rw [h]
  exact hfib.comp (by fun_prop)

/-- The one-body anchored big-box kinetic word of a slot fibre is the one-body form
`bsOneBody ℓ (fsKinCoeff c) 0` of the fibre. -/
private lemma bsOneBody_zero_eq_bigBoxWord1_aux {ℓ c : ℝ} (hℓ : 0 < ℓ) {n : ℕ}
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (i : Fin (n + 1)) (r : Submission.BoseGases.X n) :
    Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) 0
        (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z, r)))
      = Work.BSKinetic.bigBoxWord1 ℓ c (Work.BSKinetic.slotState1 i Φ r) := by
  have hcont : ContDiff ℝ (⊤ : ENat) (Work.BSKinetic.slotState1 i Φ r) :=
    contDiff_slotState1_aux hΦ i r
  have h1 : Work.UBBInputs9.tBwordKinBigU 1 ℓ c 0 (Work.BSKinetic.slotState1 i Φ r)
      = Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) 0
          (Work.BSKinetic.slotFun1 (Work.BSKinetic.slotState1 i Φ r)) :=
    bigKinU_one_eq_oneBody hℓ c 0 (Work.BSKinetic.slotState1 i Φ r) hcont
  have h2 : Work.BSKinetic.slotFun1 (Work.BSKinetic.slotState1 i Φ r)
      = fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z, r)) := rfl
  rw [Work.BSKinetic.bigBoxWord1,
    Work.BSKinetic.tBwordKinBig_eq_familyBigKin_zero 1 ℓ c
      (Work.BSKinetic.slotState1 i Φ r), h1, h2]

/-! ## The one-body anchored kinetic form of a slot fibre is a.e. strongly measurable -/

private lemma bsOneBody_zero_slot_aemeas {ℓ c : ℝ} (hℓ : 0 < ℓ) (n : ℕ)
    (Φ : Submission.BoseGases.X (n + 1) → ℝ) (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (i : Fin (n + 1)) :
    MeasureTheory.AEStronglyMeasurable
      (fun r : Submission.BoseGases.X n =>
        Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) 0
          (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z, r))))
      (Work.BSKinetic.boxMu n ℓ) := by
  classical
  -- joint continuity of the box mean of the slot fibre
  have hmean : Continuous (fun q : Submission.BoseGases.X n × ℝ³ =>
      Work.BSKinetic.bsMean ℓ 0
        (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z, q.1)))) := by
    have hcont : Continuous (Function.uncurry
        (fun (q : Submission.BoseGases.X n × ℝ³) (z : ℝ³) =>
          Φ (Submission.BoseGases.kcInsN n i (z, q.1)))) := by
      refine hΦ.continuous.comp ?_
      exact (Submission.BoseGases.kcInsN_cont i).comp
        (continuous_snd.prodMk continuous_fst.fst)
    have h := Commons.Analysis.Calculus.continuous_setIntegral_isCompact
      (Submission.BoseGases.acube_compact hℓ) hcont
    have hfun : (fun q : Submission.BoseGases.X n × ℝ³ =>
        Work.BSKinetic.bsMean ℓ 0
          (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z, q.1))))
        = fun q : Submission.BoseGases.X n × ℝ³ => (ℓ ^ 3)⁻¹ *
            ∫ z in Submission.BoseGases.acube ℓ,
              Φ (Submission.BoseGases.kcInsN n i (z, q.1)) := by
      funext q
      rw [Work.BSKinetic.bsMean]
      simp
    rw [hfun]
    exact h.const_mul _
  -- joint continuity of the mean-free part
  have hbsQc : Continuous (fun w : (Submission.BoseGases.X n × ℝ³) × ℝ³ =>
      Work.BSKinetic.bsQ ℓ 0
        (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z, w.1.1))) w.2) := by
    have hfun : (fun w : (Submission.BoseGases.X n × ℝ³) × ℝ³ =>
        Work.BSKinetic.bsQ ℓ 0
          (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z, w.1.1))) w.2)
        = fun w : (Submission.BoseGases.X n × ℝ³) × ℝ³ =>
            Φ (Submission.BoseGases.kcInsN n i (w.2, w.1.1))
            - Work.BSKinetic.bsMean ℓ 0
                (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z, w.1.1))) := rfl
    rw [hfun]
    exact (hΦ.continuous.comp ((Submission.BoseGases.kcInsN_cont i).comp
      (continuous_snd.prodMk continuous_fst.fst))).sub (hmean.comp continuous_fst)
  -- joint continuity of the window
  have hbsWinc : Continuous (fun w : (Submission.BoseGases.X n × ℝ³) × ℝ³ =>
      Work.BSKinetic.bsWin ℓ 0 w.2) := by
    have hfun : (fun w : (Submission.BoseGases.X n × ℝ³) × ℝ³ =>
        Work.BSKinetic.bsWin ℓ 0 w.2)
        = fun w : (Submission.BoseGases.X n × ℝ³) × ℝ³ =>
            Submission.BoseGases.chiScale ℓ w.2 := by
      funext w
      simp [Work.BSKinetic.bsWin]
    rw [hfun]
    exact (Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).continuous.comp continuous_snd
  -- the jointly continuous Fourier integrand
  let J : ((Submission.BoseGases.X n × ℝ³) × ℝ³) → ℂ := fun w =>
    Complex.exp (-(Complex.I * (inner ℝ w.1.2 w.2 : ℂ))) *
      ((Work.BSKinetic.bsWin ℓ 0 w.2 : ℂ) *
        (Work.BSKinetic.bsQ ℓ 0
          (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z, w.1.1))) w.2 : ℂ))
  have hJ : Continuous J := by
    change Continuous (fun w : (Submission.BoseGases.X n × ℝ³) × ℝ³ =>
      Complex.exp (-(Complex.I * (inner ℝ w.1.2 w.2 : ℂ))) *
        ((Work.BSKinetic.bsWin ℓ 0 w.2 : ℂ) *
          (Work.BSKinetic.bsQ ℓ 0
            (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z, w.1.1))) w.2 : ℂ)))
    refine Continuous.mul ?_ (Continuous.mul ?_ ?_)
    · exact Complex.continuous_exp.comp ((continuous_const.mul (Complex.continuous_ofReal.comp
        (continuous_inner.comp (continuous_fst.snd.prodMk continuous_snd)))).neg)
    · exact Complex.continuous_ofReal.comp hbsWinc
    · exact Complex.continuous_ofReal.comp hbsQc
  -- measurability of the `z`-integral
  have hK : MeasureTheory.AEStronglyMeasurable (fun q : Submission.BoseGases.X n × ℝ³ =>
      ∫ z : ℝ³, J (q, z)) ((Work.BSKinetic.boxMu n ℓ).prod MeasureTheory.volume) :=
    hJ.stronglyMeasurable.aestronglyMeasurable.integral_prod_right'
  -- multiply by the symbol
  have hfs : Continuous (fun p : ℝ³ => Submission.BoseGases.fsKinCoeff c ‖p‖) := by
    have hc : Continuous fun r : ℝ => Submission.BoseGases.fsKinCoeff c r := by
      have hfun : (fun r : ℝ => Submission.BoseGases.fsKinCoeff c r)
          = fun r : ℝ => (max (r - c) 0) ^ 2 := rfl
      rw [hfun]
      exact ((continuous_id.sub continuous_const).max continuous_const).pow 2
    exact hc.comp continuous_norm
  have hK2 : MeasureTheory.AEStronglyMeasurable (fun q : Submission.BoseGases.X n × ℝ³ =>
      Submission.BoseGases.fsKinCoeff c ‖q.2‖ * ‖(∫ z : ℝ³, J (q, z))‖ ^ 2)
      ((Work.BSKinetic.boxMu n ℓ).prod MeasureTheory.volume) := by
    have hf : MeasureTheory.AEStronglyMeasurable (fun q : Submission.BoseGases.X n × ℝ³ =>
        Submission.BoseGases.fsKinCoeff c ‖q.2‖) ((Work.BSKinetic.boxMu n ℓ).prod MeasureTheory.volume) :=
      ((hfs.comp continuous_snd).stronglyMeasurable).aestronglyMeasurable
    exact hf.mul ((hK.norm).pow 2)
  -- integrate over `p`
  have hK3 : MeasureTheory.AEStronglyMeasurable (fun r : Submission.BoseGases.X n =>
      ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³,
        Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖(∫ z : ℝ³, J ((r, p), z))‖ ^ 2) (Work.BSKinetic.boxMu n ℓ) := by
    have := hK2.integral_prod_right'
    exact this.const_mul _
  refine hK3.congr ?_
  filter_upwards with r
  rfl

theorem bigBoxWord1_slot_aemeas {ℓ c : ℝ} (hℓ : 0 < ℓ) (n : ℕ)
    (Φ : Submission.BoseGases.X (n + 1) → ℝ) (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (i : Fin (n + 1)) :
    MeasureTheory.AEStronglyMeasurable
      (fun r : Submission.BoseGases.X n =>
        Work.BSKinetic.bigBoxWord1 ℓ c (Work.BSKinetic.slotState1 i Φ r))
      (Work.BSKinetic.boxMu n ℓ) := by
  refine (bsOneBody_zero_slot_aemeas (c := c) hℓ n Φ hΦ i).congr ?_
  filter_upwards with r
  exact bsOneBody_zero_eq_bigBoxWord1_aux hℓ hΦ i r

end Work.BSKinetic.SlotSwap
