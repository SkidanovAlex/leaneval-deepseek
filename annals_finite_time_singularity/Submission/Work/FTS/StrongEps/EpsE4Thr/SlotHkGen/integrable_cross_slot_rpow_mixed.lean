/-
Copyright: work module for the Elgindi finite-time singularity project.

# Integrability of the crossed slot pairing against `w²·sin(2θ)^c`, mixed slots

Companion of `Work.FTS.StrongEps.EpsE4Thr.integrable_cross_slot_rpow` for a slot
`(a,b)` with `b ≥ 1` (at least one angular derivative) and the exponent range `c ≥ -γ(α)`
(stronger than the `c ≥ -η` of the `b = 0` case, exactly what the mixed slot needs).

The statement is the one used by the `H^k`-generic slot recursion; the measure is spelled out
as the product `(volume.restrict I_z).prod (volume.restrict I_θ)`, i.e. `EpsE4Thr.mup`.

The proof is immediate from the general assembly `EpsE4Thr.integrable_mixed_pairing`
(AM–GM on the open quadrant against the `ℋ⁴`-integrands): the only pointwise ingredient is the
mixed-slot domination `SlotWt.mixedSlot_weight_le_HkIntegrand4`, applicable because `b ≥ 1`,
and the a.e. strong measurability is `SlotWt.aesm_mixed_pair_weight`.  Everything below is
`sorry`-free.
-/
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.integrable_cross_slot_rpow
import Submission.Work.FTS.StrongEps.EpsE4Thr.SlotHkGen.integral_slot_sq_rpow_le_HkSq_gen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.StrongEps.EpsE4Thr.SlotHkGen

theorem integrable_cross_slot_rpow_mixed {α c : ℝ} {a b : ℕ} {f h : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hc : -(Work.Spaces.gam α) ≤ c) (hb : 1 ≤ b) (hab : a + b ≤ 4)
    (hsmf : Work.FTS.EllipticEst.SmoothOpen f) (hsmh : Work.FTS.EllipticEst.SmoothOpen h)
    (hmemf : Work.Spaces.HkMem α 4 f) (hmemh : Work.Spaces.HkMem α 4 h) :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.mixed a b f p.1 p.2 * Work.Spaces.mixed a b h p.1 p.2
        * (Work.Spaces.w p.1 ^ 2 * Real.sin (2 * p.2) ^ c))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hmain := Work.FTS.StrongEps.EpsE4Thr.integrable_mixed_pairing (α := α) (c := c)
    (f := f) (h := h) (j := a) (i := b) hsmf hsmh hmemf hmemh
    (fun z θ _ hθ hθ2 =>
      Work.FTS.StrongEps.EpsE4Thr.SlotWt.mixedSlot_weight_le_HkIntegrand4
        (α := α) (c := c) (g := f) (a := b) (b := a) hα hc hb (by omega) ⟨hθ, hθ2⟩)
    (fun z θ _ hθ hθ2 =>
      Work.FTS.StrongEps.EpsE4Thr.SlotWt.mixedSlot_weight_le_HkIntegrand4
        (α := α) (c := c) (g := h) (a := b) (b := a) hα hc hb (by omega) ⟨hθ, hθ2⟩)
    (Work.FTS.StrongEps.EpsE4Thr.SlotWt.aesm_mixed_pair_weight (c := c) hsmf hsmh)
  simpa only [Work.FTS.StrongEps.EpsE4Thr.mup, Work.FTS.StrongEps.EpsE4Thr.crossWt]
    using hmain

end Work.FTS.StrongEps.EpsE4Thr.SlotHkGen
