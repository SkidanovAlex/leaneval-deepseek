import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongEps.LocUnif.mixed_rect_L2_bounds
import Submission.Work.FTS.StrongEps.LocUnif.rect_deriv_bounds
import Submission.Work.FTS.StrongEps.LocUnif.basis_apply_two
import Submission.Work.FTS.StrongLWP.Sobolev.EqcProduct
import Submission.Work.FTS.StrongEps.HQoAux.integral_sq_sum4_abs_le
import Submission.Work.FTS.StrongEps.HQoAux.integral_sq_basis_second_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.HQoAux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem cut_slot_L2_bounds {α : ℝ} (hα : 0 < α) {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α 6 F)
    {zlo' zhi' tlo' thi' : ℝ} (hzlo' : 0 < zlo') (hzi' : zlo' ≤ zhi') (htlo' : 0 < tlo')
    (hthi' : thi' < Real.pi / 2)
    {χ : ℝ × ℝ → ℝ} (hχsm : ContDiff ℝ 2 χ) (hχnn : ∀ x, 0 ≤ χ x) (hχle1 : ∀ x, χ x ≤ 1)
    (hχzero : ∀ x, x ∉ Set.Icc zlo' zhi' ×ˢ Set.Icc tlo' thi' → χ x = 0)
    {M : ℝ} (hM1 : ∀ x, ‖fderiv ℝ χ x‖ ≤ M) (hM2 : ∀ x, ‖fderiv ℝ (fderiv ℝ χ) x‖ ≤ M) :
    ∃ C1 C2 : ℝ, 0 < C1 ∧ 0 < C2 ∧ ∀ (b a : ℕ), a + b ≤ 4 →
      ((∫ x : ℝ × ℝ, (χ x * Function.uncurry (Work.Spaces.mixed b a F) x) ^ 2)
          ≤ C1 * Work.Spaces.HkSq α 6 F) ∧
      ((∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ (fun y : ℝ × ℝ =>
            χ y * Function.uncurry (Work.Spaces.mixed b a F) y)) x‖ ^ 2)
          ≤ C2 * Work.Spaces.HkSq α 6 F) := by
  classical
  -- the rectangle carrying the support of `χ`
  set s : Set (ℝ × ℝ) := Set.Icc zlo' zhi' ×ˢ Set.Icc tlo' thi' with hsdef
  have hsc : IsClosed s := by rw [hsdef]; exact isClosed_Icc.prod isClosed_Icc
  have hsmeas : MeasurableSet s := hsc.measurableSet
  have hscpt : IsCompact s := by rw [hsdef]; exact isCompact_Icc.prod isCompact_Icc
  have hsQ0 : s ⊆ Work.FTS.EllipticEst.Q0 := by
    intro p hp
    rw [hsdef] at hp
    rw [Work.FTS.EllipticEst.mem_Q0]
    exact ⟨lt_of_lt_of_le hzlo' hp.1.1, lt_of_lt_of_le htlo' hp.2.1,
      lt_of_le_of_lt hp.2.2 hthi'⟩
  -- the constant of `mixed_rect_L2_bounds` (independent of `α`, `F`, `b`, `a`)
  obtain ⟨C, hCpos, hCbound⟩ :=
    Work.FTS.StrongEps.LocUnif.mixed_rect_L2_bounds (a := zlo') (b := zhi')
      (c := tlo') (d := thi') hzlo' hzi' htlo' hthi'
  have hKn : 0 ≤ Work.Spaces.HkSq α 6 F := Work.Spaces.HkSq_nonneg α 6 F
  refine ⟨C, 3 * (16 + 17 * M ^ 2) * C, hCpos, ?_, ?_⟩
  · have h16 : (0 : ℝ) < 16 + 17 * M ^ 2 := by nlinarith [sq_nonneg M]
    have h3 : (0 : ℝ) < 3 * (16 + 17 * M ^ 2) := by linarith
    exact mul_pos h3 hCpos
  · intro b a hab
    have hab' : b + a ≤ 4 := by omega
    have hCb := hCbound α hα F hF hmem b a hab'
    have hGsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.mixed b a F) := hF.mixed b a
    have hG2 : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.mixed b a F))
        Work.FTS.EllipticEst.Q0 :=
      hGsm.of_le Work.FTS.StrongEps.LocUnif.two_le_smoothOrder
    have hcont : ContinuousOn (Function.uncurry (Work.Spaces.mixed b a F)) s :=
      hG2.continuousOn.mono hsQ0
    have hI0 : IntegrableOn
        (fun x : ℝ × ℝ => (Function.uncurry (Work.Spaces.mixed b a F) x) ^ 2) s :=
      ContinuousOn.integrableOn_compact hscpt (hcont.pow 2)
    -- ## the first conjunct
    have hb0 : ∫ x in s, (Function.uncurry (Work.Spaces.mixed b a F) x) ^ 2
        ≤ C * Work.Spaces.HkSq α 6 F := by
      rw [hsdef] at hI0 ⊢
      rw [Work.FTS.StrongLWP.Sobolev.eqc_setIntegral_rect_eq hI0]
      exact hCb.1
    -- ## the second conjunct
    have hfd1 : ContDiffOn ℝ 1 (fderiv ℝ (Function.uncurry (Work.Spaces.mixed b a F)))
        Work.FTS.EllipticEst.Q0 :=
      hG2.fderiv_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 (by norm_num)
    have hgd : ∀ y ∈ Work.FTS.EllipticEst.Q0,
        DifferentiableAt ℝ (Function.uncurry (Work.Spaces.mixed b a F)) y := fun y hy =>
      (hG2.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hy)).differentiableAt (by norm_num)
    have hgd2 : ∀ y ∈ Work.FTS.EllipticEst.Q0,
        DifferentiableAt ℝ (fderiv ℝ (Function.uncurry (Work.Spaces.mixed b a F))) y :=
      fun y hy =>
        (hfd1.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hy)).differentiableAt
          (by norm_num)
    have hI1 : IntegrableOn
        (fun x : ℝ × ℝ => ‖fderiv ℝ (Function.uncurry (Work.Spaces.mixed b a F)) x‖ ^ 2) s :=
      ContinuousOn.integrableOn_compact hscpt ((hfd1.continuousOn.mono hsQ0).norm.pow 2)
    -- the dominating function for the second derivative
    set E : ℝ × ℝ → ℝ := fun x =>
        |Work.Spaces.pzIter 2 (Work.Spaces.mixed b a F) x.1 x.2|
          + |Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.mixed b a F)) x.1 x.2|
          + |Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.mixed b a F)) x.1 x.2|
          + |Work.Spaces.pthIter 2 (Work.Spaces.mixed b a F) x.1 x.2| with hEdef
    have hE : ∀ x ∈ s, ‖fderiv ℝ (fderiv ℝ (Function.uncurry (Work.Spaces.mixed b a F))) x‖
        ≤ E x := by
      intro x hx
      exact Work.FTS.StrongEps.LocUnif.norm_fderiv_fderiv_le_basis
        Work.FTS.EllipticEst.isOpen_Q0 hG2 (hsQ0 hx)
    have hcontE : ContinuousOn E s := by
      have hp1 : ContinuousOn
          (fun x : ℝ × ℝ => Work.Spaces.pzIter 2 (Work.Spaces.mixed b a F) x.1 x.2) s :=
        (hGsm.pzIter 2).continuousOn.mono hsQ0
      have hp2 : ContinuousOn
          (fun x : ℝ × ℝ => Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.mixed b a F)) x.1 x.2)
          s := ((hGsm.pth).pz).continuousOn.mono hsQ0
      have hp3 : ContinuousOn
          (fun x : ℝ × ℝ => Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.mixed b a F)) x.1 x.2)
          s := ((hGsm.pz).pth).continuousOn.mono hsQ0
      have hp4 : ContinuousOn
          (fun x : ℝ × ℝ => Work.Spaces.pthIter 2 (Work.Spaces.mixed b a F) x.1 x.2) s :=
        ((hGsm.pth).pth).continuousOn.mono hsQ0
      exact ((hp1.abs.add hp2.abs).add hp3.abs).add hp4.abs
    have hI2 : IntegrableOn (fun x => E x ^ 2) s :=
      ContinuousOn.integrableOn_compact hscpt (hcontE.pow 2)
    -- the four individual `L²`-bounds of the second partials
    have hA1 : IntegrableOn
        (fun x : ℝ × ℝ => (Work.Spaces.pzIter 2 (Work.Spaces.mixed b a F) x.1 x.2) ^ 2) s :=
      ContinuousOn.integrableOn_compact hscpt (((hGsm.pzIter 2).continuousOn.mono hsQ0).pow 2)
    have hA2 : IntegrableOn
        (fun x : ℝ × ℝ => (Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.mixed b a F)) x.1 x.2) ^ 2)
        s :=
      ContinuousOn.integrableOn_compact hscpt
        ((((hGsm.pth).pz).continuousOn.mono hsQ0).pow 2)
    have hA3 : IntegrableOn
        (fun x : ℝ × ℝ => (Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.mixed b a F)) x.1 x.2) ^ 2)
        s :=
      ContinuousOn.integrableOn_compact hscpt
        ((((hGsm.pz).pth).continuousOn.mono hsQ0).pow 2)
    have hA4 : IntegrableOn
        (fun x : ℝ × ℝ => (Work.Spaces.pthIter 2 (Work.Spaces.mixed b a F) x.1 x.2) ^ 2) s :=
      ContinuousOn.integrableOn_compact hscpt
        ((((hGsm.pth).pth).continuousOn.mono hsQ0).pow 2)
    have hb2 : ∫ x in s, E x ^ 2 ≤ 16 * C * Work.Spaces.HkSq α 6 F :=
      Work.FTS.StrongEps.HQoAux.integral_sq_basis_second_le
        (G := Work.Spaces.mixed b a F) (a := zlo') (b := zhi') (c := tlo') (d := thi')
        (C := C) (K := Work.Spaces.HkSq α 6 F)
        hA1 hA2 hA3 hA4
        hCb.2.2.2.1 hCb.2.2.2.2.1 hCb.2.2.2.2.2.1 hCb.2.2.2.2.2.2
    -- the bound for the first derivative of the datum
    obtain ⟨hRD1, hRD2⟩ :=
      Work.FTS.StrongEps.LocUnif.rect_deriv_bounds (F := F) (α := α) (C := C)
        (a' := zlo') (b' := zhi') (c' := tlo') (d' := thi') b a hsQ0 hF
        hCb.2.1 hCb.2.2.1 hCb.2.2.2.1 hCb.2.2.2.2.1 hCb.2.2.2.2.2.1 hCb.2.2.2.2.2.2
    have hb1' : ∫ x in s, ‖fderiv ℝ (Function.uncurry (Work.Spaces.mixed b a F)) x‖ ^ 2
        ≤ 4 * C * Work.Spaces.HkSq α 6 F := hRD1
    have hM0 : ∀ x, ‖χ x‖ ≤ (1 : ℝ) := fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hχnn x)]; exact hχle1 x
    have hmain : ∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ (fun y : ℝ × ℝ =>
          χ y * Function.uncurry (Work.Spaces.mixed b a F) y)) x‖ ^ 2
        ≤ 3 * ((1 ^ 2 * ∫ x in s, E x ^ 2)
            + ((2 * M) ^ 2 * ∫ x in s,
                ‖fderiv ℝ (Function.uncurry (Work.Spaces.mixed b a F)) x‖ ^ 2)
            + M ^ 2 * ∫ x in s, (Function.uncurry (Work.Spaces.mixed b a F) x) ^ 2) :=
      Work.FTS.StrongLWP.Sobolev.eqc_integral_fderiv_fderiv_mul_sq_le
        (χ := χ) (g := Function.uncurry (Work.Spaces.mixed b a F)) (s := s)
        (U := Work.FTS.EllipticEst.Q0) (M0 := 1) (M1 := M) (M2 := M) (E := E)
        hχsm hsc hχzero hM0 hM1 hM2 Work.FTS.EllipticEst.isOpen_Q0 hsQ0 hgd hgd2 hE hI0 hI1 hI2
    constructor
    · calc ∫ x : ℝ × ℝ, (χ x * Function.uncurry (Work.Spaces.mixed b a F) x) ^ 2
          ≤ ∫ x in s, (Function.uncurry (Work.Spaces.mixed b a F) x) ^ 2 :=
            Work.FTS.StrongLWP.Sobolev.eqc_integral_mul_sq_le hχzero hχle1 hχnn hsmeas hI0
        _ ≤ C * Work.Spaces.HkSq α 6 F := hb0
    · have e1 : (1 : ℝ) ^ 2 * (∫ x in s, E x ^ 2)
          ≤ (1 : ℝ) ^ 2 * (16 * C * Work.Spaces.HkSq α 6 F) := by
        rw [one_pow, one_mul, one_mul]; exact hb2
      have e2 : (2 * M) ^ 2 * (∫ x in s,
            ‖fderiv ℝ (Function.uncurry (Work.Spaces.mixed b a F)) x‖ ^ 2)
          ≤ (2 * M) ^ 2 * (4 * C * Work.Spaces.HkSq α 6 F) :=
        mul_le_mul_of_nonneg_left hb1' (sq_nonneg (2 * M))
      have e3 : M ^ 2 * (∫ x in s, (Function.uncurry (Work.Spaces.mixed b a F) x) ^ 2)
          ≤ M ^ 2 * (C * Work.Spaces.HkSq α 6 F) :=
        mul_le_mul_of_nonneg_left hb0 (sq_nonneg M)
      have hsum : (1 : ℝ) ^ 2 * (∫ x in s, E x ^ 2)
            + (2 * M) ^ 2 * (∫ x in s,
                ‖fderiv ℝ (Function.uncurry (Work.Spaces.mixed b a F)) x‖ ^ 2)
            + M ^ 2 * (∫ x in s, (Function.uncurry (Work.Spaces.mixed b a F) x) ^ 2)
          ≤ (1 : ℝ) ^ 2 * (16 * C * Work.Spaces.HkSq α 6 F)
            + (2 * M) ^ 2 * (4 * C * Work.Spaces.HkSq α 6 F)
            + M ^ 2 * (C * Work.Spaces.HkSq α 6 F) := by
        linarith [e1, e2, e3]
      calc ∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ (fun y : ℝ × ℝ =>
            χ y * Function.uncurry (Work.Spaces.mixed b a F) y)) x‖ ^ 2
          ≤ 3 * ((1 ^ 2 * ∫ x in s, E x ^ 2)
              + ((2 * M) ^ 2 * ∫ x in s,
                  ‖fderiv ℝ (Function.uncurry (Work.Spaces.mixed b a F)) x‖ ^ 2)
              + M ^ 2 * ∫ x in s, (Function.uncurry (Work.Spaces.mixed b a F) x) ^ 2) := hmain
        _ ≤ 3 * ((1 : ℝ) ^ 2 * (16 * C * Work.Spaces.HkSq α 6 F)
              + (2 * M) ^ 2 * (4 * C * Work.Spaces.HkSq α 6 F)
              + M ^ 2 * (C * Work.Spaces.HkSq α 6 F)) :=
            mul_le_mul_of_nonneg_left hsum (by norm_num)
        _ = (3 * (16 + 17 * M ^ 2) * C) * Work.Spaces.HkSq α 6 F := by ring

end Work.FTS.StrongEps.HQoAux
