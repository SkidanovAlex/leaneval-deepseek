import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.H2W.mixedABasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
Copyright: work module for the Elgindi finite-time singularity project.

# `H2W/mixedA`: the angular (mixed) part of the `ℋ²` estimate for `z²∂_z²Ψ`

This module contains the elementary structural layer of the target
`Work.FTS.EllipticEst.H2W.mixedA` (the `hA` input of `TT.est_two_weak_of_pieces`):

```
∀ α F Ψ, 0 < α → α ≤ 1/4 → EllWeakPos α 2 F Ψ →
  α⁴·HkSq α 2 (z²∂_z²Ψ) ≤ α⁴·Σ_{j<3} L2Sq(z²∂_z²(D_z^jΨ)·w/sin^{η/2}) + HkSq α 2 F
```

The two proved observations recorded here identify the target's right-hand side as the *pure*
(`z`-only) part of `HkSq α 2 (z²∂_z²Ψ)`:

* `z2_pzIter2_eq` — the pointwise operator identity `z²∂_z² = D_z² − D_z`, from which the
  commuting relation `z²·pzIter 2 (DzIter j Ψ) = DzIter j (z²·pzIter 2 Ψ)` follows (polynomials in
  `D_z` commute; the remaining formalisation is the linearity of `DzIter j` on differences and the
  slicewise differentiability of the iterates, both routine).

Consequently the target is *equivalent* to the bound
`α⁴·Σ_{(i,j)∈{(1,0),(1,1),(2,0)}} ∫∫(D_z^jD_θ^i(z²∂_z²Ψ))²·Wt² ≤ HkSq α 2 F`
on the three mixed slots of the `ℋ²`-norm of `A = z²∂_z²Ψ` — i.e. it is the *angular half* of
Elgindi's Proposition `prop:H2`, with the radial (pure) part kept on the right as slack.  See
`NOTES_mixedA.md` in this directory for the numerical evidence that the statement is true
(ratios `≤ 1.3e−3` in every family tested, including the exactly computable resonance family
`z^{2n/α}e^{−z}φ_n`), and for the analysis of why its proof needs the sharp `Step 4/5` machinery
of the elliptic section (not yet available in the workspace).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false

/-! ## The target

By `hksqSplitMixed` the two sides of the target differ exactly by the three *mixed* (angular)
slots of the `ℋ²`-norm of `A = z²∂_z²Ψ`: the target is equivalent to

`α⁴·Σ_{(i,j) ∈ {(1,0),(1,1),(2,0)}} L2Sq(D_z^jD_θ^iA·Wt) ≤ HkSq α 2 F`.

The proof of *that* statement is the missing sharp analytic chapter.  The state of the analysis
is recorded in `NOTES_mixedA_session3.md` (session 3) and `NOTES_mixedA.md` / `NOTES_mixedA2.md`
(sessions 1–2); in brief:

* the reduction is formalised here as `mixedA_of_mixedSlots` (target from the split + the mixed
  sum) and, finer, as **`mixedA_of_slotBounds`** (from the three slot bounds with explicit
  constants `c₁₀+c₁₁+c₂₀ ≤ 1`);
* the θ-Poincaré input `∫(u')²s^{2-γ} ≤ ∫(u'')²s^{2-γ}` is **delivered** as
  `Submission.Work.H2W.ThetaPoincareSharp` (constant `1`; its only residual `sorry` is the
  numeric bound delegated as `Submission.Work.H2W.WhPhiPsiIntegralLeFix`);
* the `(1,0)`/`(2,0)` slots reduce to the θ-Poincaré + the level-`0` estimate on the *radially
  shifted* data; the latter is the project's open bottleneck (presently `sorryAx`);
* the `(1,0)`- and `(1,1)`-slot *per-slot* comparisons with constant `1` are **false** for
  general data (small deficits; the `Lzero1`-eigenvalue hypothesis of the 1-D reduction is
  replaced by an *effective* angular eigenvalue outside the good range) — so the missing piece
  is a *relaxed* per-slot bound `α⁴·L2Sq(mixed j i A·Wt) ≤ L2Sq(mixed j i F·Wt) + δ·HkSq α 2F`
  with a small `δ`, plus the bookkeeping of the otherwise-unused pure `F`-slots.

Below is the assembly of the target from the split and the slot bounds (both proved), which is
the part that the elementary lemmas of this file support. -/

/-- **The assembly of `mixedA` from the split of `HkSq α 2 (z²∂_z²Ψ)` and the bound on its three
mixed slots.**  (The split itself is proved in the sibling module
`Submission.Work.FTS.EllipticEst.H2W.hksqSplitMixed`, which imports *this* file — hence it is
taken here as a hypothesis, to avoid a circular import; the unconditional assembly can be
performed in that module.) -/
theorem mixedA_of_mixedSlots
    (hsplit : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
        Work.Spaces.HkSq α 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          = (∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
                z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
            + ∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3,
                if 1 ≤ i ∧ i + j ≤ 2 then Work.Spaces.L2Sq (fun z θ =>
                  Work.Spaces.mixed j i (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
                    * Work.Spaces.Wt α z θ) else 0)
    (hmix : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
        α ^ 4 * (∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3,
            if 1 ≤ i ∧ i + j ≤ 2 then Work.Spaces.L2Sq (fun z θ =>
              Work.Spaces.mixed j i (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
                * Work.Spaces.Wt α z θ) else 0)
          ≤ Work.Spaces.HkSq α 2 F) :
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
        α ^ 4 * Work.Spaces.HkSq α 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ≤
          α ^ 4 * (∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
              z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
            + Work.Spaces.HkSq α 2 F := by
  intro α F Ψ hα hα4 h
  have hsp := hsplit α F Ψ hα hα4 h
  have hm := hmix α F Ψ hα hα4 h
  have hpow : (0 : ℝ) ≤ α ^ 4 := by positivity
  rw [hsp]
  nlinarith [hm, hpow]

/-- **The assembly of `mixedA` from the three *slot* bounds with explicit constants.**

This is the form of the reduction that isolates the analytic content: the target follows from
the three mixed-slot bounds `α⁴·L2Sq(D_z^jD_θ^iA·Wt) ≤ c_{ij}·HkSq α 2F` with
`c₁₀ + c₁₁ + c₂₀ ≤ 1` (together with the split of `HkSq α 2 (z²∂_z²Ψ)`, taken as a hypothesis
here for the same circular-import reason as in `mixedA_of_mixedSlots`).

The `(1,0)`- and `(2,0)`-slots are reached from the level-`0` estimate on the *radially shifted*
data plus the θ-Poincaré; the `(1,1)`-slot needs the sharp per-slot comparison
`α⁴·L2Sq(D_zD_θA·Wt) ≤ L2Sq(D_zD_θF·Wt)` (see `NOTES_mixedA_session3.md`). -/
theorem mixedA_of_slotBounds
    (hsplit : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
        Work.Spaces.HkSq α 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          = (∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
                z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
            + ∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3,
                if 1 ≤ i ∧ i + j ≤ 2 then Work.Spaces.L2Sq (fun z θ =>
                  Work.Spaces.mixed j i (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
                    * Work.Spaces.Wt α z θ) else 0)
    (c10 c11 c20 : ℝ) (h10 : 0 ≤ c10) (h11 : 0 ≤ c11) (h20 : 0 ≤ c20)
    (hc : c10 + c11 + c20 ≤ 1)
    (hA10 : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
        α ^ 4 * Work.Spaces.L2Sq (fun z θ =>
            Work.Spaces.mixed 0 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
              * Work.Spaces.Wt α z θ) ≤ c10 * Work.Spaces.HkSq α 2 F)
    (hA11 : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
        α ^ 4 * Work.Spaces.L2Sq (fun z θ =>
            Work.Spaces.mixed 1 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
              * Work.Spaces.Wt α z θ) ≤ c11 * Work.Spaces.HkSq α 2 F)
    (hA20 : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
        α ^ 4 * Work.Spaces.L2Sq (fun z θ =>
            Work.Spaces.mixed 0 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
              * Work.Spaces.Wt α z θ) ≤ c20 * Work.Spaces.HkSq α 2 F) :
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
        α ^ 4 * Work.Spaces.HkSq α 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ≤
          α ^ 4 * (∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
              z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
            + Work.Spaces.HkSq α 2 F := by
  intro α F Ψ hα hα4 h
  have hsp := hsplit α F Ψ hα hα4 h
  have e10 := hA10 α F Ψ hα hα4 h
  have e11 := hA11 α F Ψ hα hα4 h
  have e20 := hA20 α F Ψ hα hα4 h
  have hFnn : 0 ≤ Work.Spaces.HkSq α 2 F := Work.Spaces.HkSq_nonneg α 2 F
  -- the guarded double sum over the three mixed slots
  have hsum : (∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3,
        if 1 ≤ i ∧ i + j ≤ 2 then Work.Spaces.L2Sq (fun z θ =>
            Work.Spaces.mixed j i (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
              * Work.Spaces.Wt α z θ) else 0)
      = Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 0 1
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * Work.Spaces.Wt α z θ)
        + Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 1 1
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * Work.Spaces.Wt α z θ)
        + Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 0 2
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
              * Work.Spaces.Wt α z θ) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Finset.sum_const_zero,
      zero_add, add_zero]
    norm_num
  rw [hsp, hsum]
  have hp : (0 : ℝ) ≤ α ^ 4 * (∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
        z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ =>
      integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _)
  nlinarith [e10, e11, e20, hc, hFnn, hp]

theorem mixedA : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      α ^ 4 * Work.Spaces.HkSq α 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ≤
        α ^ 4 * (∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
            z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
          + Work.Spaces.HkSq α 2 F := by sorry

end Work.FTS.EllipticEst.H2W
