/-
Copyright: work module for the Elgindi finite-time singularity project.

**STATE (current stretch — read `Cores/NOTES_aSlotsTwo_T1_T3_done_T2_wall.md` and the header of
`Cores/aSlotsTwoPieces.lean`).**
The target splits into its three summands (`A := z²∂_z²Ψ`):
`α⁴ Tk α 1 A`, `α⁴ Tk α 1 (D_z A)`, `α⁴ Tk α 2 A`.  All the *definitions and plumbing* of this
file have been moved to `Cores/aSlotsTwoDefs.lean` (so that the slot estimates of
`Cores/aSlotsTwoPieces.lean`, which need them, can be imported here without a cycle), and the
three slot estimates live in `Cores/aSlotsTwoPieces.lean`:

* `aSlotsTwoT1x` — **PROVED** (sorry-free, axioms `[propext, Classical.choice, Quot.sound]`);
* `aSlotsTwoT2x` — the workspace's open *shifted `A`-slot*; reduced (proved reductions) to the
  light-weight mixed-slot interpolation `TT.interpGamma_core` / `Prop.mixedSlotInterpEta`;
* `aSlotsTwoT3x` — provable from `T1` by the sharp `D_θ²`-split plus `shiftZeroSlots_clean`.

This file is now the one-line assembly of the three.

# `Cores/aSlotsTwo` — the `α⁴`-weighted `A`-slots of the level-`2` elliptic estimate

The target of this file is the statement (unchanged, at the bottom)

```
theorem aSlotsTwo (h0 : ∃ C, 0 < C ∧ TT.EllWeak0 C) :
  ∃ C > 0, ∀ α F Ψ, 0 < α → α ≤ 1/4 → TT.EllWeakPos α 2 F Ψ →
    α⁴ (Tk α 1 A + 3 Tk α 1 (D_z A) + Tk α 2 A) ≤ C · HkSq α 2 F,      A := z²∂_z²Ψ,
```

i.e. the `A`-half of the `Tk`-residual of Elgindi's `prop:H2` at level `2`
(`Tk α k f = ∫∫ (D_θ^k f · Wt α)²`).

## The decomposition, and why each term is what it is

Write `A := z²∂_z²Ψ` and `T1 := Tk α 1 A`, `T2 := Tk α 1 (D_z A)`, `T3 := Tk α 2 A`.

* `Tk α 1 f = ∫∫(D_θf · Wt)² = ∫∫(∂_θf)² w² sin(2θ)^{2-γ}` and, on the open quadrant,
  `D_θD_z = D_zD_θ`, so `T2 = ∫∫(mixed 1 1 A · Wt)²` — the `(1,1)` slot of `A`;
  `T3 = ∫∫(mixed 0 2 A · Wt)²`.  Hence `T1 + T2 + T3 ≤ HkSq α 2 A` (three of its slots,
  `Work.Spaces.L2Sq_mixed_le_HkSq`), and the target is *equivalent* to the `A`-half of the
  level-`2` elliptic estimate `α²|A|_{ℋ²} ≤ C|F|_{ℋ²}` (the radial slots of `A` being the easy
  half, from `TT.EllWeak0` and the shifted level-`0` slots).
* `D_z A = z²∂_z²(D_zΨ)` on the open quadrant (`Dz_zsq_pzIter_two_agree`,
  `Tk_one_Dz_A_eq` below), so `T2` is the level-`1` `A`-slot of the *radially shifted* datum
  `(D_zF, D_zΨ)`.

## References (all proved and imported)

`Cores.aSlotsTwoDefs`: `Dz_zsq_pzIter_two_agree`, `Tk_one_Dz_A_eq`, `shiftZeroSlots_clean`,
`HkSq_zero_pthIter_two_DzIter_one_le`, `HkSq_zero_pthIter_two_DzIter_two_le`,
`aSlotsTwo_of_pieces`, `Tk_le_two_split`-style plumbing, `sin_sq_mul_Wt_sq_self`,
`pthIter_two_sq_sig4_le_self`, `bcoef`-free `w`-lemmas.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.EllipticEst.Cores.aSlotsTwoDefs
import Submission.Work.FTS.EllipticEst.Cores.aSlotsTwoPieces

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section

/-- **The requested lemma**, assembled from the three slot estimates of
`Cores/aSlotsTwoPieces`. -/
theorem aSlotsTwo (h0 : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllWeak0 C) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      α ^ 4 * (Work.FTS.EllipticEst.remov.Step.Tk α 1
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + 3 * Work.FTS.EllipticEst.remov.Step.Tk α 1
            (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
          + Work.FTS.EllipticEst.remov.Step.Tk α 2
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
        ≤ C * Work.Spaces.HkSq α 2 F := by
  obtain ⟨C₁, hC₁pos, h₁⟩ := aSlotsTwoT1x h0
  obtain ⟨C₂, hC₂pos, h₂⟩ := aSlotsTwoT2x h0
  obtain ⟨C₃, hC₃pos, h₃⟩ := aSlotsTwoT3x h0
  refine ⟨C₁ + 3 * C₂ + C₃, by linarith, fun α F Ψ hα hα4 hwk => ?_⟩
  have e₁ := h₁ α F Ψ hα hα4 hwk
  have e₂ := h₂ α F Ψ hα hα4 hwk
  have e₃ := h₃ α F Ψ hα hα4 hwk
  have hnn : 0 ≤ Work.Spaces.HkSq α 2 F := Work.Spaces.HkSq_nonneg α 2 F
  rw [show α ^ 4 * (Work.FTS.EllipticEst.remov.Step.Tk α 1
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        + 3 * Work.FTS.EllipticEst.remov.Step.Tk α 1
          (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
        + Work.FTS.EllipticEst.remov.Step.Tk α 2
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
      = α ^ 4 * Work.FTS.EllipticEst.remov.Step.Tk α 1
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        + 3 * (α ^ 4 * Work.FTS.EllipticEst.remov.Step.Tk α 1
          (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)))
        + α ^ 4 * Work.FTS.EllipticEst.remov.Step.Tk α 2
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) from by ring]
  nlinarith [e₁, e₂, e₃, hnn]

end

end Work.FTS.EllipticEst.Cores
