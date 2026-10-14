import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.TT.truncAux
import Submission.Work.FTS.EllipticEst.TopSlotTwoFts.ShiftZeroSlots2
import Submission.Work.FTS.EllipticEst.remov.wsAux
import Submission.Work.FTS.LocData.HkIntegrand_zfar_Fstar_le
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongPersist.L3Aux.bcoefRadBound
import Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.Spaces.mixed_mul_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TopSlotTwoFts

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The Step-4 slot

`s20M3 α Ψ = 8 ∫_z ∫_θ w²(∂_θ³Ψ)²σ₂ = 8 · L2Sq (D_θ(∂_θ²Ψ)·W)`, so the bound is the proved
`H2W.slot01Weak`. -/

/-- **The Step-4 slot is dominated by the pure slots and the source energy.** -/
theorem s20M3_le_pPure_HkSq :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      Work.FTS.EllipticEst.H2W.s20M3 α Ψ
        ≤ C * (Work.FTS.EllipticEst.H2W.pPure Ψ + Work.Spaces.HkSq α 2 F) := by
  obtain ⟨K, hKpos, hK⟩ := Work.FTS.EllipticEst.H2W.slot01Weak
  refine ⟨8 * K, by positivity, fun α F Ψ hα hα4 h => ?_⟩
  have hb := hK α F Ψ hα hα4 h
  have hM3 : Work.FTS.EllipticEst.H2W.s20M3 α Ψ
      = 8 * Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 0 1
          (Work.Spaces.pthIter 2 Ψ) z θ * Work.Spaces.Wt α z θ) :=
    Work.FTS.EllipticEst.H2W.s20M3_eq α hα hα4 Ψ
  rw [hM3, Work.FTS.EllipticEst.H2W.pPure]
  calc 8 * Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 0 1
        (Work.Spaces.pthIter 2 Ψ) z θ * Work.Spaces.Wt α z θ)
      ≤ 8 * (K * ((∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
            Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) +
          Work.Spaces.HkSq α 2 F)) :=
        mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = (8 * K) * ((∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
            Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) +
          Work.Spaces.HkSq α 2 F) := by ring

/-- **The source and lower-order half of the Step-5 right-hand side.** -/
theorem s20sum_le (hsrc : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      Work.FTS.EllipticEst.H2W.s20J2 α F Ψ
          + (Work.FTS.EllipticEst.H2W.s20A2 Ψ + Work.FTS.EllipticEst.H2W.s20A1 Ψ
              + Work.FTS.EllipticEst.H2W.s20A0 Ψ)
        ≤ C * (Work.FTS.EllipticEst.H2W.pPure Ψ + Work.Spaces.HkSq α 2 F)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      Work.FTS.EllipticEst.H2W.s20J2 α F Ψ + Work.FTS.EllipticEst.H2W.s20M3 α Ψ
          + (Work.FTS.EllipticEst.H2W.s20A2 Ψ + Work.FTS.EllipticEst.H2W.s20A1 Ψ
            + Work.FTS.EllipticEst.H2W.s20A0 Ψ)
        ≤ C * (Work.FTS.EllipticEst.H2W.pPure Ψ + Work.Spaces.HkSq α 2 F) := by
  obtain ⟨CJ, hCJpos, hJ⟩ := hsrc
  obtain ⟨C3, hC3pos, h3⟩ := s20M3_le_pPure_HkSq
  refine ⟨CJ + C3, by linarith, fun α F Ψ hα hα4 h => ?_⟩
  have h1 := hJ α F Ψ hα hα4 h
  have h2 := h3 α F Ψ hα hα4 h
  linarith [h1, h2]

/-! ## The pointwise decomposition of `Tk α 2 (∂_θθΨ)` -/

/-- The pointwise bound `(D_θ²(∂_θθΨ)·W)² ≤ s20F4 α Ψ + s20F3 α Ψ` on the closed domain. -/
theorem Tk_B_pointwise (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) {Ψ : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ) (z θ : ℝ) (hz : z ∈ Work.Spaces.Iz)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.DthIter 2 (Work.Spaces.pthIter 2 Ψ) z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ
        + Work.FTS.EllipticEst.H2W.s20F3 α Ψ z θ := by
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h | h
  · -- at `z = 0` both sides vanish because `w 0 = 0`
    rw [← h]
    simp only [Work.FTS.EllipticEst.H2W.s20F4, Work.FTS.EllipticEst.H2W.s20F3,
      Work.Spaces.Wt, Work.Spaces.w]
    norm_num
  · have h2 : ∀ θ' ∈ Set.Ioo 0 (Real.pi / 2),
        DifferentiableAt ℝ (fun t => deriv (fun s => Work.Spaces.pthIter 2 Ψ z s) t) θ' := by
      intro θ' hθ'
      have h1 : ContDiffOn ℝ 2 (fun θ'' => Work.Spaces.pthIter 2 Ψ z θ'')
          (Set.Ioo 0 (Real.pi / 2)) :=
        Work.FTS.EllipticEst.remov.ws_contDiffOn_slice
          (show Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) from hsm.pth.pth) h
      have h2' : ContDiffOn ℝ 1 (deriv (fun θ'' => Work.Spaces.pthIter 2 Ψ z θ''))
          (Set.Ioo 0 (Real.pi / 2)) :=
        h1.deriv_of_isOpen isOpen_Ioo (by norm_num)
      have h3 : DifferentiableOn ℝ (deriv (fun θ'' => Work.Spaces.pthIter 2 Ψ z θ''))
          (Set.Ioo 0 (Real.pi / 2)) := h2'.differentiableOn (by norm_num)
      exact (h3.differentiableAt (isOpen_Ioo.mem_nhds hθ')).hasDerivAt.differentiableAt
    have hpt := Work.FTS.EllipticEst.Mine.Tk_pointwise_le_closed α hα hα4
      (Work.Spaces.pthIter 2 Ψ) z θ hθ h2
    have e4 : deriv (fun θ' => deriv (fun t => Work.Spaces.pthIter 2 Ψ z t) θ') θ
        = Work.Spaces.pthIter 4 Ψ z θ := rfl
    have e3 : deriv (fun t => Work.Spaces.pthIter 2 Ψ z t) θ
        = Work.Spaces.pthIter 3 Ψ z θ := rfl
    rw [e4, e3] at hpt
    simpa only [Work.FTS.EllipticEst.H2W.s20F4, Work.FTS.EllipticEst.H2W.s20F3] using hpt

/-! ## The B-slot -/

/-- **The level-`2` `B`-slot**: `Tk α 2 (∂_θθΨ) ≤ C HkSq α 2 F` for data of the weak class,
granted the level-`0` estimate `EllWeak0`. -/
theorem Tk_B_le (h0 : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllWeak0 C) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      Work.FTS.EllipticEst.remov.Step.Tk α 2 (Work.Spaces.pthIter 2 Ψ)
        ≤ C * Work.Spaces.HkSq α 2 F := by
  -- the three inputs of `topSlotB_two_of_pieces`
  obtain ⟨CZ, hCZpos, hZ⟩ := ShiftZeroSlots2 h0
  have hpure : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ))
        ≤ C * Work.Spaces.HkSq α 2 F := by
    refine ⟨CZ, hCZpos, fun α F Ψ hα hα4 h => ?_⟩
    have hb := hZ α F Ψ hα hα4 h 2 (le_refl 2)
    have hz : 0 ≤ α ^ 4 * Work.Spaces.HkSq α 0
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 2 Ψ) z θ) :=
      mul_nonneg (by positivity) (Work.Spaces.HkSq_nonneg α 0 _)
    linarith [hb, hz]
  obtain ⟨CJ, hCJpos, hJ⟩ := Work.FTS.EllipticEst.H2W.Step5.s20_source
  obtain ⟨CZ', hCZ'pos, hpureb⟩ := hpure
  obtain ⟨Cp, hCppos, hpPure⟩ :=
    Work.FTS.EllipticEst.Cores.pPure_le_of_pure_two h0 ⟨CZ', hCZ'pos, hpureb⟩
  obtain ⟨Cm4, hCm4pos, hm4⟩ :=
    Work.FTS.EllipticEst.Cores.topSlotB_two_of_pieces h0
      Work.FTS.EllipticEst.Cores.topSlotB_two_step5
      (s20sum_le ⟨CJ, hCJpos, hJ⟩)
      ⟨CZ', hCZ'pos, hpureb⟩
  obtain ⟨C3, hC3pos, hM3⟩ := s20M3_le_pPure_HkSq
  refine ⟨2 * Cm4 + C3 * (Cp + 1) + 1, by positivity, fun α F Ψ hα hα4 h => ?_⟩
  have hsm : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  obtain ⟨hz4, hzin4, hz3, hzin3⟩ := Work.FTS.EllipticEst.H2W.Step5.s20_honesty α F Ψ hα hα4 h
  have hRinner : ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ
        + Work.FTS.EllipticEst.H2W.s20F3 α Ψ z θ) Work.Spaces.Iθ :=
    fun z hz => (hz4 z hz).add (hz3 z hz)
  have hRouter : MeasureTheory.Integrable (fun z => ∫ θ in Work.Spaces.Iθ,
      (Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ
        + Work.FTS.EllipticEst.H2W.s20F3 α Ψ z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    refine (hzin4.add hzin3).congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
    exact (MeasureTheory.integral_add (hz4 z hz) (hz3 z hz)).symm
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DthIter 2 (Work.Spaces.pthIter 2 Ψ) z θ
            * Work.Spaces.Wt α z θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ
            + Work.FTS.EllipticEst.H2W.s20F3 α Ψ z θ) := by
    intro z hz
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => sq_nonneg _) (hRinner z hz) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
    exact Tk_B_pointwise α hα hα4 hsm z θ hz hθ
  have hTkB : Work.FTS.EllipticEst.remov.Step.Tk α 2 (Work.Spaces.pthIter 2 Ψ)
      ≤ ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ
            + Work.FTS.EllipticEst.H2W.s20F3 α Ψ z θ) := by
    rw [Work.FTS.EllipticEst.remov.Step.Tk]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => integral_nonneg fun θ => sq_nonneg _) hRouter ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => hinner z hz
  have hsplit : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ
          + Work.FTS.EllipticEst.H2W.s20F3 α Ψ z θ))
      = Work.FTS.EllipticEst.H2W.s20M4 α Ψ + Work.FTS.EllipticEst.H2W.s20M3 α Ψ := by
    have h1 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ
            + Work.FTS.EllipticEst.H2W.s20F3 α Ψ z θ))
        = ∫ z in Work.Spaces.Iz, ((∫ θ in Work.Spaces.Iθ,
              Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ)
            + ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.H2W.s20F3 α Ψ z θ) := by
      refine MeasureTheory.integral_congr_ae ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
      exact MeasureTheory.integral_add (hz4 z hz) (hz3 z hz)
    rw [h1, MeasureTheory.integral_add hzin4 hzin3]
    rfl
  rw [hsplit] at hTkB
  -- the two slot bounds
  have hHK : 0 ≤ Work.Spaces.HkSq α 2 F := Work.Spaces.HkSq_nonneg α 2 F
  have h4 : Work.FTS.EllipticEst.H2W.s20M4 α Ψ ≤ 2 * Cm4 * Work.Spaces.HkSq α 2 F := by
    have hh := hm4 α F Ψ hα hα4 h
    rw [Work.FTS.EllipticEst.Cores.s20M4_eq_two_mul]
    linarith [hh]
  have h3 : Work.FTS.EllipticEst.H2W.s20M3 α Ψ ≤ C3 * (Cp + 1) * Work.Spaces.HkSq α 2 F := by
    have h1 := hM3 α F Ψ hα hα4 h
    have h2 := hpPure α F Ψ hα hα4 h
    have hp0 : 0 ≤ Work.FTS.EllipticEst.H2W.pPure Ψ := Work.FTS.EllipticEst.H2W.pPure_nonneg Ψ
    have hpk : Work.FTS.EllipticEst.H2W.pPure Ψ + Work.Spaces.HkSq α 2 F
        ≤ (Cp + 1) * Work.Spaces.HkSq α 2 F := by nlinarith [h2, hHK]
    calc Work.FTS.EllipticEst.H2W.s20M3 α Ψ
        ≤ C3 * (Work.FTS.EllipticEst.H2W.pPure Ψ + Work.Spaces.HkSq α 2 F) := h1
      _ ≤ C3 * ((Cp + 1) * Work.Spaces.HkSq α 2 F) :=
          mul_le_mul_of_nonneg_left hpk hC3pos.le
      _ = C3 * (Cp + 1) * Work.Spaces.HkSq α 2 F := by ring
  have hfin : Work.FTS.EllipticEst.remov.Step.Tk α 2 (Work.Spaces.pthIter 2 Ψ)
      ≤ (2 * Cm4 + C3 * (Cp + 1) + 1) * Work.Spaces.HkSq α 2 F := by
    calc Work.FTS.EllipticEst.remov.Step.Tk α 2 (Work.Spaces.pthIter 2 Ψ)
        ≤ Work.FTS.EllipticEst.H2W.s20M4 α Ψ + Work.FTS.EllipticEst.H2W.s20M3 α Ψ := hTkB
      _ ≤ 2 * Cm4 * Work.Spaces.HkSq α 2 F + C3 * (Cp + 1) * Work.Spaces.HkSq α 2 F :=
          add_le_add h4 h3
      _ ≤ (2 * Cm4 + C3 * (Cp + 1) + 1) * Work.Spaces.HkSq α 2 F := by
          nlinarith [hHK]
  exact hfin

end

end Work.FTS.EllipticEst.TopSlotTwoFts
