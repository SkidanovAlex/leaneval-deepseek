/-
Copyright: work module for the Elgindi finite-time singularity project.

# `S20LowerAlt`: the lower-order angular block of `Step5/s20_source`, proved directly

This module proves

  `s20A2 Ψ + s20A1 Ψ + s20A0 Ψ ≤ C · pPure Ψ`

for data of the weak class `TT.EllWeakPos α 2 F Ψ` (`0 < α ≤ 1/4`), with `C` universal.  It is
the `Ψ`-half of `Step5/s20_source` that does not involve the source `F`:

* `s20A2` is *exactly* the `j = 0` summand of `pPure` (the identity `(w/s^{η/2})² = w² sEta`
  plus `MeasureTheory.integral_const_mul`, pulling the radial weight out of the `θ`-integral);
* `s20A1`, `s20A0` are controlled by the same summand through the *proved* slice Poincaré
  inequality `H2W.sliceEtaPoincare` applied to the slices `θ ↦ Ψ z θ` (the endpoint limits are
  `H2W.psi_slice_limits`, the `sEta`-honesty is the third conjunct of
  `remov.SourceBound.weakSliceSlots`), together with `sEta ≥ 1` a.e. on `Iθ` to remove the
  weight from `∫ Ψ²` and `∫ (∂_θΨ)²`.

The declaration is named `s20src_lower_own` (rather than `s20_lower`) so that this module may
be imported alongside the sibling `Step5/s20_lower` of the delegation, which carries the same
statement under that name.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Final.Rep.H2W.Step5.S20SrcAux
import Submission.Work.H2W.weakSliceContinuousKit
import Submission.Work.FTS.EllipticEst.H2W.sliceEtaPoincare

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.Step5

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **`s20A2` is the `j = 0` summand of `pPure`.** -/
theorem s20src_A2_eq_pSlot (Ψ : ℝ → ℝ → ℝ) :
    Work.FTS.EllipticEst.H2W.s20A2 Ψ = s20src_pSlot 0 Ψ := by
  unfold Work.FTS.EllipticEst.H2W.s20A2 s20src_pSlot s20src_slotZ s20src_slotFun
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  exact (MeasureTheory.integral_const_mul ((Work.Spaces.w z) ^ 2)
    (fun θ => (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 0 Ψ) z θ) ^ 2
      * Work.FTS.EllipticEst.sEta θ)).symm

theorem s20src_lower_own : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      Work.FTS.EllipticEst.H2W.s20A2 Ψ + Work.FTS.EllipticEst.H2W.s20A1 Ψ
          + Work.FTS.EllipticEst.H2W.s20A0 Ψ
        ≤ C * Work.FTS.EllipticEst.H2W.pPure Ψ := by
  obtain ⟨C0, hC0pos, hC0⟩ := Work.FTS.EllipticEst.H2W.sliceEtaPoincare
  refine ⟨1 + 2 * C0, by positivity, fun α F Ψ hα hα4 h => ?_⟩
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  -- ### the per-slice Poincaré bound
  have hslice : ∀ z : ℝ, 0 < z →
      (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)
          ≤ C0 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ) ∧
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
          ≤ C0 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ) := by
    intro z hz
    have hsm : Work.FTS.EllipticEst.SmoothOpen Ψ := hΨso
    have hu : ∀ n : ℕ, ContDiffOn ℝ n (fun θ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) :=
      fun n => (hΨso.curry_θ hz).of_le (by simp [Work.Stability.smoothOrder])
    obtain ⟨hlim0, hlim1⟩ := Work.H2W.psi_slice_limits hα h z hz
    obtain ⟨-, -, hInt2, -, -, -, -, -⟩ :=
      Work.FTS.EllipticEst.remov.SourceBound.weakSliceSlots (α := α) (k := 2) le_rfl h z hz
    obtain ⟨hInt0, hInt1, hbnd0, hbnd1⟩ := hC0 (fun θ => Ψ z θ) hu hlim0 hlim1 hInt2
    have hone : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        1 ≤ Work.FTS.EllipticEst.sEta θ := s20src_one_le_sEta_ae
    have hb0 : (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)
        ≤ C0 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) := by
      have hmono : (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)
          ≤ ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
        MeasureTheory.integral_mono_of_nonneg
          (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
          (f := fun θ => (Ψ z θ) ^ 2)
          (g := fun θ => (Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          (Filter.Eventually.of_forall fun θ => sq_nonneg _) hInt0
          (by
            filter_upwards [hone] with θ hθ
            nlinarith [sq_nonneg (Ψ z θ)])
      simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth] using
        le_trans hmono hbnd0
    have hb1 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
        ≤ C0 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) := by
      have hmono : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
          ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ :=
        MeasureTheory.integral_mono_of_nonneg
          (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
          (f := fun θ => (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
          (g := fun θ => (Work.Spaces.pthIter 1 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          (Filter.Eventually.of_forall fun θ => sq_nonneg _) hInt1
          (by
            filter_upwards [hone] with θ hθ
            nlinarith [sq_nonneg (Work.Spaces.pthIter 1 Ψ z θ)])
      simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth] using
        le_trans hmono hbnd1
    exact ⟨hb0, hb1⟩
  -- ### the `z`-integrability of the majorant
  have hBsEta : MeasureTheory.IntegrableOn
      (fun z => s20src_slotZ (Work.Spaces.pthIter 2 Ψ) Work.FTS.EllipticEst.sEta z)
      Work.Spaces.Iz :=
    s20src_integrableOn_slotZ_sEta_DzIter hΨso h.memB 0 (by norm_num)
  have hmaj : MeasureTheory.IntegrableOn
      (fun z => C0 * ((Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ))) Work.Spaces.Iz :=
    (hBsEta.const_mul C0).congr (Filter.Eventually.of_forall fun z => by
      have h : s20src_slotZ (Work.Spaces.pthIter 2 Ψ) Work.FTS.EllipticEst.sEta z
          = (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
        unfold s20src_slotZ s20src_slotFun
        exact MeasureTheory.integral_const_mul _ _
      simp only [h])
  -- ### the two `z`-level comparisons
  have hA0 : Work.FTS.EllipticEst.H2W.s20A0 Ψ
      ≤ C0 * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ)) := by
    have hpt : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)
          ≤ C0 * ((Work.Spaces.w z) ^ 2 *
            (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ)) := by
      filter_upwards [s20src_ae_pos_mem_Iz] with z hz
      have h1 := (hslice z hz).1
      have hw : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
      nlinarith [h1, hw]
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z _ =>
        mul_nonneg (sq_nonneg _)
          (integral_nonneg_of_ae (Filter.Eventually.of_forall fun θ => sq_nonneg _)))
      hmaj hpt
    rw [MeasureTheory.integral_const_mul] at hmono
    exact hmono
  have hA1 : Work.FTS.EllipticEst.H2W.s20A1 Ψ
      ≤ C0 * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ)) := by
    have hpt : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
          ≤ C0 * ((Work.Spaces.w z) ^ 2 *
            (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ)) := by
      filter_upwards [s20src_ae_pos_mem_Iz] with z hz
      have h1 := (hslice z hz).2
      have hw : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
      nlinarith [h1, hw]
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z _ =>
        mul_nonneg (sq_nonneg _)
          (integral_nonneg_of_ae (Filter.Eventually.of_forall fun θ => sq_nonneg _)))
      hmaj hpt
    rw [MeasureTheory.integral_const_mul] at hmono
    exact hmono
  -- ### the identification of the majorant with `pPure`'s `j = 0` summand
  have hpull : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ)) = s20src_pSlot 0 Ψ := by
    unfold s20src_pSlot s20src_slotZ s20src_slotFun
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    exact (MeasureTheory.integral_const_mul ((Work.Spaces.w z) ^ 2)
      (fun θ => (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 0 Ψ) z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ)).symm
  -- ### the summand bound
  have hp0 : s20src_pSlot 0 Ψ
      ≤ Work.FTS.EllipticEst.H2W.pPure Ψ := by
    rw [s20src_pPure_eq_three Ψ]
    linarith [s20src_pSlot_nonneg 0 Ψ, s20src_pSlot_nonneg 1 Ψ, s20src_pSlot_nonneg 2 Ψ]
  have hsum : Work.FTS.EllipticEst.H2W.s20A2 Ψ + Work.FTS.EllipticEst.H2W.s20A1 Ψ
        + Work.FTS.EllipticEst.H2W.s20A0 Ψ
      ≤ (1 + 2 * C0) * Work.FTS.EllipticEst.H2W.pPure Ψ := by
    rw [s20src_A2_eq_pSlot Ψ]
    rw [hpull] at hA0 hA1
    nlinarith [hA0, hA1, hp0, hC0pos.le, s20src_pSlot_nonneg 0 Ψ]
  exact hsum

end Work.FTS.EllipticEst.H2W.Step5
