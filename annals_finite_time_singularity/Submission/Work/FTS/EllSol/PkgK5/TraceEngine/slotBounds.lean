import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.EllipticEst.Core.i0Aux.Basic
import Submission.Work.EllipticEst.Core.i0Aux.Honest
import Submission.Work.EllipticEst.Core.i0Aux.i0_fubini_package
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllSol.PkgK5.TraceEngine.SlotEngineBasic
import Submission.Work.FTS.EllSol.PkgK5.TraceEngine.SlotEngineCore

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.PkgK5.TraceEngine

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! # `TraceEngine.slotBounds`

The three slots of the trace engine: the weighted `L²`-masses of `D_z(D_z^rV)`,
`∂_θ²(D_z^rV)` and `D_z²(D_z^rV) + b·D_z(D_z^rV)` (`b z = (z-3)/(1+z)`, `|b| ≤ 3` on `Iz`)
are honest on `Iz ×ˢ Iθ` and bounded by the corresponding `ℋ^k`-norms.

The first two slots are `Work.FTS.EllSol.PkgK5.TraceEngine.slotAux_slotZ_prod` and
`slotAux_slotT_prod`; the third is the sum of the `D_z²`-slot (`slotAux_slotD2_prod`) and the
`D_z`-slot, combined by the pointwise convexity `(X+bY)² ≤ 2X² + 18Y²`
(`Work.Blocks.sq_add_b_mul_sq_le`, `Work.Blocks.abs_bcoef_le`). -/

theorem slotBounds {k : ℕ} {α : ℝ} {V : ℝ → ℝ → ℝ} (hV : Work.FTS.EllipticEst.SmoothOpen V)
    (hdd : Work.Spaces.HkMem α k (Work.Spaces.DzIter 2 V))
    (htt : Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 V))
    (hd : Work.Spaces.HkMem α k (Work.Spaces.Dz V))
    (r : ℕ) (hr : r ≤ k) :
    (MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2 * (Work.Spaces.Dz (Work.Spaces.DzIter r V) p.1 p.2) ^ 2)
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      ∧ (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
          * Work.FTS.EllipticEst.thEta p.2 * (Work.Spaces.Dz (Work.Spaces.DzIter r V) p.1 p.2) ^ 2)
        ≤ Work.Spaces.HkSq α k (Work.Spaces.Dz V))
    ∧ (MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2
        * (Work.Spaces.pthIter 2 (Work.Spaces.DzIter r V) p.1 p.2) ^ 2)
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      ∧ (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
          * Work.FTS.EllipticEst.thEta p.2
          * (Work.Spaces.pthIter 2 (Work.Spaces.DzIter r V) p.1 p.2) ^ 2)
        ≤ Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V))
    ∧ (MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2
        * (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) p.1 p.2
            + ((p.1 - 3) / (1 + p.1)) * Work.Spaces.Dz (Work.Spaces.DzIter r V) p.1 p.2) ^ 2)
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      ∧ (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
          * Work.FTS.EllipticEst.thEta p.2
          * (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) p.1 p.2
              + ((p.1 - 3) / (1 + p.1)) * Work.Spaces.Dz (Work.Spaces.DzIter r V) p.1 p.2) ^ 2)
        ≤ 18 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
          + 18 * Work.Spaces.HkSq α k (Work.Spaces.Dz V)) := by
  have hZ := slotAux_slotZ_prod (k := k) (r := r) (α := α) (V := V) hV hd hr
  have hT := slotAux_slotT_prod (k := k) (r := r) (α := α) (V := V) hV htt hr
  have hD2 := slotAux_slotD2_prod (k := k) (r := r) (α := α) (V := V) hV hdd hr
  -- the third slot: continuity of the combined integrand on the open quadrant
  have hcont3 : ContinuousOn (Function.uncurry (fun z θ : ℝ =>
      (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ
        * (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) z θ
            + ((z - 3) / (1 + z)) * Work.Spaces.Dz (Work.Spaces.DzIter r V) z θ) ^ 2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hX : ContinuousOn
        (fun p : ℝ × ℝ => Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := ((hV.DzIter r).DzIter 2).continuousOn
    have hY : ContinuousOn
        (fun p : ℝ × ℝ => Work.Spaces.Dz (Work.Spaces.DzIter r V) p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := ((hV.DzIter r).Dz).continuousOn
    have hb : ContinuousOn (fun p : ℝ × ℝ => (p.1 - 3) / (1 + p.1))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      refine ContinuousOn.div (continuousOn_fst.sub continuousOn_const)
        (continuousOn_const.add continuousOn_fst) ?_
      intro p hp
      have hp1 : (0 : ℝ) < p.1 := hp.1
      exact ne_of_gt (by linarith)
    refine (slotAux_continuousOn_w2_thEta.mul ((hX.add (hb.mul hY)).pow 2)).congr ?_
    intro p hp
    rfl
  -- the pointwise convexity
  have hpt3 : ∀ p ∈ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
      (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
        * (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) p.1 p.2
            + ((p.1 - 3) / (1 + p.1)) * Work.Spaces.Dz (Work.Spaces.DzIter r V) p.1 p.2) ^ 2
      ≤ 2 * ((Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
            * (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) p.1 p.2) ^ 2)
        + 18 * ((Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
            * (Work.Spaces.Dz (Work.Spaces.DzIter r V) p.1 p.2) ^ 2) := by
    intro p hp
    obtain ⟨hz, hθ⟩ := Set.mem_prod.mp hp
    have hS : 0 ≤ Work.FTS.EllipticEst.thEta p.2 :=
      Work.EllipticEst.Core.i0Aux.thEta_nonneg_Iθ hθ
    have hWnn : 0 ≤ (Work.Spaces.w p.1) ^ 2 := sq_nonneg _
    have hb : |(p.1 - 3) / (1 + p.1)| ≤ 3 := Work.Blocks.abs_bcoef_le p.1 hz
    have hkey := Work.Blocks.sq_add_b_mul_sq_le
      (X := Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) p.1 p.2)
      (Y := Work.Spaces.Dz (Work.Spaces.DzIter r V) p.1 p.2)
      (b := (p.1 - 3) / (1 + p.1)) hb
    have hmul := mul_le_mul_of_nonneg_left hkey (mul_nonneg hWnn hS)
    calc (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
          * (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) p.1 p.2
              + ((p.1 - 3) / (1 + p.1)) * Work.Spaces.Dz (Work.Spaces.DzIter r V) p.1 p.2) ^ 2
        = ((Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2)
          * (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) p.1 p.2
              + ((p.1 - 3) / (1 + p.1))
                * Work.Spaces.Dz (Work.Spaces.DzIter r V) p.1 p.2) ^ 2 := by
          ring
      _ ≤ ((Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2)
            * (2 * (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) p.1 p.2) ^ 2
              + 18 * (Work.Spaces.Dz (Work.Spaces.DzIter r V) p.1 p.2) ^ 2) := hmul
      _ = 2 * ((Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
            * (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) p.1 p.2) ^ 2)
          + 18 * ((Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
            * (Work.Spaces.Dz (Work.Spaces.DzIter r V) p.1 p.2) ^ 2) := by ring
  have hdom : IntegrableOn (fun p : ℝ × ℝ => 2 * ((Work.Spaces.w p.1) ^ 2
      * Work.FTS.EllipticEst.thEta p.2
      * (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) p.1 p.2) ^ 2)
      + 18 * ((Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
      * (Work.Spaces.Dz (Work.Spaces.DzIter r V) p.1 p.2) ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    (hD2.1.const_mul 2).add (hZ.1.const_mul 18)
  have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * Work.FTS.EllipticEst.thEta p.2
      * (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) p.1 p.2
          + ((p.1 - 3) / (1 + p.1)) * Work.Spaces.Dz (Work.Spaces.DzIter r V) p.1 p.2) ^ 2)
      ((volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
    rw [slotAux_volume_restrict_dom]
    exact Work.Spaces.aesm_of_continuousOn_Qd _ hcont3
  have hInt3 : IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * Work.FTS.EllipticEst.thEta p.2
      * (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) p.1 p.2
          + ((p.1 - 3) / (1 + p.1)) * Work.Spaces.Dz (Work.Spaces.DzIter r V) p.1 p.2) ^ 2)
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine MeasureTheory.Integrable.mono' hdom haesm ?_
    refine MeasureTheory.ae_restrict_of_forall_mem slotAux_measurableSet_dom (fun p hp => ?_)
    obtain ⟨hz, hθ⟩ := Set.mem_prod.mp hp
    have hnn3 : 0 ≤ (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
        * (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) p.1 p.2
            + ((p.1 - 3) / (1 + p.1)) * Work.Spaces.Dz (Work.Spaces.DzIter r V) p.1 p.2) ^ 2 :=
      mul_nonneg (mul_nonneg (sq_nonneg _)
        (Work.EllipticEst.Core.i0Aux.thEta_nonneg_Iθ hθ)) (sq_nonneg _)
    rw [Real.norm_of_nonneg hnn3]
    exact hpt3 p hp
  have hC3 : (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
      * Work.FTS.EllipticEst.thEta p.2
      * (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) p.1 p.2
          + ((p.1 - 3) / (1 + p.1)) * Work.Spaces.Dz (Work.Spaces.DzIter r V) p.1 p.2) ^ 2)
      ≤ 18 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
        + 18 * Work.Spaces.HkSq α k (Work.Spaces.Dz V) := by
    have hmono := MeasureTheory.setIntegral_mono_on hInt3 hdom slotAux_measurableSet_dom hpt3
    rw [MeasureTheory.integral_add (hD2.1.const_mul 2) (hZ.1.const_mul 18),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hmono
    have hA₀ : 0 ≤ Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V) :=
      Work.Spaces.HkSq_nonneg α k _
    have hB₀ : 0 ≤ Work.Spaces.HkSq α k (Work.Spaces.Dz V) :=
      Work.Spaces.HkSq_nonneg α k _
    linarith [hmono, hD2.2, hZ.2, hA₀, hB₀]
  exact ⟨⟨hZ.1, hZ.2⟩, ⟨hT.1, hT.2⟩, ⟨hInt3, hC3⟩⟩

end Work.FTS.EllSol.PkgK5.TraceEngine
