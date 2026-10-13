import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Final.Rep.H2W.slot20_bound
import Submission.Work.FTS.EllipticEst.Mine.FSlotsTwoD
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.Mine.SlotDefs
import Submission.Work.FTS.EllipticEst.Final.Rep.H2W.Step5.S20SrcAux
import Submission.Work.FTS.EllipticEst.Final.Rep.H2W.Step5.s20_Fslot
import Submission.Work.FTS.EllipticEst.Final.Rep.H2W.Step5.S20LowerAlt
import Submission.Work.H2W.weakSliceContinuousKit

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.Step5

open MeasureTheory Set Filter
open scoped Real Topology

set_option maxHeartbeats 1600000

/-- **The source slot of `s20J2`.**  The `σ₄`-weighted second angular slot of the source
`Gsrc α F Ψ` is bounded by `pPure Ψ + HkSq α 2 F`: the `F`-part is the sibling `s20_Fslot`, and
the two `Ψ`-parts (the `Az Ψ = z²∂_z²Ψ`- and the `D_zΨ`-slot) are dominated by the `j = 1, 2`
summands of `pPure` by the commutation of `∂_θ²` with `D_z` on the open quadrant. -/
theorem s20src_J2_le : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      Work.FTS.EllipticEst.H2W.s20J2 α F Ψ
        ≤ C * (Work.FTS.EllipticEst.H2W.pPure Ψ + Work.Spaces.HkSq α 2 F) := by
  obtain ⟨CF, hCFpos, hFslot⟩ := s20_Fslot
  refine ⟨3 * CF + 12, by positivity, fun α F Ψ hα hα4 h => ?_⟩
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hFso : Work.FTS.EllipticEst.SmoothOpen F := Work.H2W.smoothOpen_source h
  obtain ⟨hFint_raw, hFbd_raw⟩ := hFslot α F hα hα4 hFso h.memF
  have hFint : MeasureTheory.IntegrableOn
      (fun z => s20src_slotZ (Work.Spaces.pthIter 2 F)
        (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z) Work.Spaces.Iz := by
    simpa only [s20src_slotZ, s20src_slotFun] using hFint_raw
  have hFbd : (∫ z in Work.Spaces.Iz, s20src_slotZ (Work.Spaces.pthIter 2 F)
        (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z)
      ≤ CF * Work.Spaces.HkSq α 2 F := by
    simpa only [s20src_slotZ, s20src_slotFun] using hFbd_raw
  have hAzint := s20src_integrableOn_slotZ_sigma4_Az hΨso h.memB hα4
  have hAzbd := s20src_slotZ_sigma4_Az_le hΨso h.memB hα4
  have hΛint := s20src_integrableOn_slotZ_sigma4_DzIter hΨso h.memB hα4 1 (by norm_num)
  have hΛbd := s20src_slotZ_sigma4_DzIter_le hΨso h.memB hα4 1 (by norm_num)
  have hcmp : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      s20src_slotZ (Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ))
          (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z
        ≤ 3 * (s20src_slotZ (Work.Spaces.pthIter 2 F)
              (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z
            + α ^ 4 * s20src_slotZ (Work.Spaces.pthIter 2 (Az Ψ))
              (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z
            + (α * (5 + α)) ^ 2 * s20src_slotZ
              (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
              (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z) := by
    filter_upwards [s20src_ae_pos_mem_Iz] with z hz
    exact s20src_slotZ_Gsrc_le hα hα4 hFso h.memF hΨso h.memB hz
  have hmaj : MeasureTheory.IntegrableOn
      (fun z => 3 * (s20src_slotZ (Work.Spaces.pthIter 2 F)
            (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z
          + α ^ 4 * s20src_slotZ (Work.Spaces.pthIter 2 (Az Ψ))
            (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z
          + (α * (5 + α)) ^ 2 * s20src_slotZ
            (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
            (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z)) Work.Spaces.Iz :=
    (((hFint.add (hAzint.const_mul (α ^ 4))).add
      (hΛint.const_mul ((α * (5 + α)) ^ 2))).const_mul 3).congr
      (Filter.Eventually.of_forall fun z => by
        simp only [Pi.add_apply, Pi.mul_apply]; try ring)
  have hmain : (∫ z in Work.Spaces.Iz, s20src_slotZ (Work.Spaces.pthIter 2
        (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ))
        (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z)
      ≤ ∫ z in Work.Spaces.Iz, 3 * (s20src_slotZ (Work.Spaces.pthIter 2 F)
            (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z
          + α ^ 4 * s20src_slotZ (Work.Spaces.pthIter 2 (Az Ψ))
            (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z
          + (α * (5 + α)) ^ 2 * s20src_slotZ
            (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
            (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z) :=
    MeasureTheory.integral_mono_of_nonneg
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z _ =>
        s20src_slotZ_nonneg (fun θ' hθ' => s20src_sigma4_nonneg α hθ') z)
      hmaj hcmp
  have hval : (∫ z in Work.Spaces.Iz, 3 * (s20src_slotZ (Work.Spaces.pthIter 2 F)
          (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z
        + α ^ 4 * s20src_slotZ (Work.Spaces.pthIter 2 (Az Ψ))
          (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z
        + (α * (5 + α)) ^ 2 * s20src_slotZ
          (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
          (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z))
      = 3 * ((∫ z in Work.Spaces.Iz, s20src_slotZ (Work.Spaces.pthIter 2 F)
              (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z)
          + α ^ 4 * (∫ z in Work.Spaces.Iz, s20src_slotZ (Work.Spaces.pthIter 2 (Az Ψ))
              (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z)
          + (α * (5 + α)) ^ 2 * (∫ z in Work.Spaces.Iz,
              s20src_slotZ (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
                (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z)) := by
    have hI12 : MeasureTheory.IntegrableOn
        (fun z => s20src_slotZ (Work.Spaces.pthIter 2 F)
            (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z
          + α ^ 4 * s20src_slotZ (Work.Spaces.pthIter 2 (Az Ψ))
            (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z) Work.Spaces.Iz :=
      hFint.add (hAzint.const_mul (α ^ 4))
    have hI3 : MeasureTheory.IntegrableOn
        (fun z => (α * (5 + α)) ^ 2 * s20src_slotZ
            (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
            (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z) Work.Spaces.Iz :=
      hΛint.const_mul ((α * (5 + α)) ^ 2)
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hI12 hI3,
      MeasureTheory.integral_add hFint (hAzint.const_mul (α ^ 4)),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    try ring
  have hIΦ : 0 ≤ ∫ z in Work.Spaces.Iz, s20src_slotZ (Work.Spaces.pthIter 2 (Az Ψ))
        (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z :=
    integral_nonneg fun z =>
      s20src_slotZ_nonneg (fun θ' hθ' => s20src_sigma4_nonneg α hθ') z
  have hIΛ : 0 ≤ ∫ z in Work.Spaces.Iz, s20src_slotZ (Work.Spaces.pthIter 2
        (Work.Spaces.DzIter 1 Ψ))
        (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z :=
    integral_nonneg fun z =>
      s20src_slotZ_nonneg (fun θ' hθ' => s20src_sigma4_nonneg α hθ') z
  have hIF : 0 ≤ ∫ z in Work.Spaces.Iz, s20src_slotZ (Work.Spaces.pthIter 2 F)
        (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z :=
    integral_nonneg fun z =>
      s20src_slotZ_nonneg (fun θ' hθ' => s20src_sigma4_nonneg α hθ') z
  have hα4le : α ^ 4 ≤ 1 := by
    have h1 : α ≤ 1 := by linarith
    exact pow_le_one₀ hα.le h1
  have hc2 : (α * (5 + α)) ^ 2 ≤ 2 := by
    have hx : α * (5 + α) ≤ 7 / 5 := by nlinarith [hα.le, hα4]
    have hx0 : 0 ≤ α * (5 + α) := by nlinarith [hα.le]
    nlinarith [hx, hx0]
  have hHk : 0 ≤ Work.Spaces.HkSq α 2 F := Work.Spaces.HkSq_nonneg α 2 F
  have h0 := s20src_pSlot_nonneg 0 Ψ
  have h1 := s20src_pSlot_nonneg 1 Ψ
  have h2 := s20src_pSlot_nonneg 2 Ψ
  have hpure := s20src_pPure_eq_three Ψ
  have hAzQ : α ^ 4 * (∫ z in Work.Spaces.Iz, s20src_slotZ (Work.Spaces.pthIter 2 (Az Ψ))
        (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z)
      ≤ 2 * (s20src_pSlot 2 Ψ + s20src_pSlot 1 Ψ) :=
    calc α ^ 4 * (∫ z in Work.Spaces.Iz,
            s20src_slotZ (Work.Spaces.pthIter 2 (Az Ψ))
              (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z)
        ≤ 1 * (∫ z in Work.Spaces.Iz, s20src_slotZ (Work.Spaces.pthIter 2 (Az Ψ))
              (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z) :=
          mul_le_mul_of_nonneg_right hα4le hIΦ
      _ = (∫ z in Work.Spaces.Iz, s20src_slotZ (Work.Spaces.pthIter 2 (Az Ψ))
              (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z) := by ring
      _ ≤ 2 * (s20src_pSlot 2 Ψ + s20src_pSlot 1 Ψ) := hAzbd
  have hΛQ : (α * (5 + α)) ^ 2 * (∫ z in Work.Spaces.Iz,
        s20src_slotZ (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
          (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z)
      ≤ 2 * s20src_pSlot 1 Ψ :=
    calc (α * (5 + α)) ^ 2 * (∫ z in Work.Spaces.Iz,
            s20src_slotZ (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
              (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z)
        ≤ 2 * (∫ z in Work.Spaces.Iz, s20src_slotZ (Work.Spaces.pthIter 2
              (Work.Spaces.DzIter 1 Ψ))
              (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z) :=
          mul_le_mul_of_nonneg_right hc2 hIΛ
      _ ≤ 2 * s20src_pSlot 1 Ψ := mul_le_mul_of_nonneg_left hΛbd (by norm_num)
  have hFQ : (∫ z in Work.Spaces.Iz, s20src_slotZ (Work.Spaces.pthIter 2 F)
        (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z)
      ≤ CF * Work.Spaces.HkSq α 2 F := hFbd
  have hCF : 0 ≤ CF := hCFpos.le
  have key : 3 * ((∫ z in Work.Spaces.Iz, s20src_slotZ (Work.Spaces.pthIter 2 F)
            (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z)
        + α ^ 4 * (∫ z in Work.Spaces.Iz, s20src_slotZ (Work.Spaces.pthIter 2 (Az Ψ))
            (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z)
        + (α * (5 + α)) ^ 2 * (∫ z in Work.Spaces.Iz,
            s20src_slotZ (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
              (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z))
      ≤ (3 * CF + 12) * (Work.FTS.EllipticEst.H2W.pPure Ψ + Work.Spaces.HkSq α 2 F) := by
    rw [hpure]
    have e1 : 3 * ((∫ z in Work.Spaces.Iz, s20src_slotZ (Work.Spaces.pthIter 2 F)
              (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z)
          + α ^ 4 * (∫ z in Work.Spaces.Iz, s20src_slotZ (Work.Spaces.pthIter 2 (Az Ψ))
              (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z)
          + (α * (5 + α)) ^ 2 * (∫ z in Work.Spaces.Iz,
              s20src_slotZ (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
                (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z))
        ≤ 3 * (CF * Work.Spaces.HkSq α 2 F
            + (2 * (s20src_pSlot 2 Ψ + s20src_pSlot 1 Ψ) + 2 * s20src_pSlot 1 Ψ)) := by
      have h := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hFQ hAzQ) hΛQ)
        (by norm_num : (0 : ℝ) ≤ 3)
      linarith [h]
    have e2 : 3 * (CF * Work.Spaces.HkSq α 2 F
          + (2 * (s20src_pSlot 2 Ψ + s20src_pSlot 1 Ψ) + 2 * s20src_pSlot 1 Ψ))
        ≤ (3 * CF + 12) * (s20src_pSlot 0 Ψ + s20src_pSlot 1 Ψ + s20src_pSlot 2 Ψ
            + Work.Spaces.HkSq α 2 F) := by
      nlinarith [h0, h1, h2, hHk, hCF]
    linarith [e1, e2]
  rw [s20src_s20J2_eq α F Ψ]
  linarith [hmain, hval.le, key]

theorem s20_source : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      Work.FTS.EllipticEst.H2W.s20J2 α F Ψ
          + (Work.FTS.EllipticEst.H2W.s20A2 Ψ + Work.FTS.EllipticEst.H2W.s20A1 Ψ
              + Work.FTS.EllipticEst.H2W.s20A0 Ψ)
        ≤ C * (Work.FTS.EllipticEst.H2W.pPure Ψ + Work.Spaces.HkSq α 2 F) := by
  obtain ⟨CJ, hCJpos, hJ⟩ := s20src_J2_le
  obtain ⟨CA, hCApos, hA⟩ := s20src_lower_own
  refine ⟨2 * max CJ CA, by positivity, fun α F Ψ hα hα4 h => ?_⟩
  have hR : 0 ≤ Work.FTS.EllipticEst.H2W.pPure Ψ + Work.Spaces.HkSq α 2 F :=
    add_nonneg (Work.FTS.EllipticEst.H2W.pPure_nonneg Ψ) (Work.Spaces.HkSq_nonneg α 2 F)
  have hp : 0 ≤ Work.FTS.EllipticEst.H2W.pPure Ψ := Work.FTS.EllipticEst.H2W.pPure_nonneg Ψ
  have hk : 0 ≤ Work.Spaces.HkSq α 2 F := Work.Spaces.HkSq_nonneg α 2 F
  have hM : 0 ≤ max CJ CA := le_trans hCJpos.le (le_max_left CJ CA)
  have hJm : Work.FTS.EllipticEst.H2W.s20J2 α F Ψ
      ≤ max CJ CA * (Work.FTS.EllipticEst.H2W.pPure Ψ + Work.Spaces.HkSq α 2 F) :=
    (hJ α F Ψ hα hα4 h).trans (mul_le_mul_of_nonneg_right (le_max_left CJ CA) hR)
  have hAm : Work.FTS.EllipticEst.H2W.s20A2 Ψ + Work.FTS.EllipticEst.H2W.s20A1 Ψ
        + Work.FTS.EllipticEst.H2W.s20A0 Ψ
      ≤ max CJ CA * (Work.FTS.EllipticEst.H2W.pPure Ψ + Work.Spaces.HkSq α 2 F) :=
    ((hA α F Ψ hα hα4 h).trans
      (mul_le_mul_of_nonneg_right (le_max_right CJ CA) hp)).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hk) hM)
  nlinarith [hJm, hAm]

end Work.FTS.EllipticEst.H2W.Step5
