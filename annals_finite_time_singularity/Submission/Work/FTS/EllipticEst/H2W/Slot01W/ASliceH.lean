/-
Copyright: work module for the Elgindi finite-time singularity project.

# A clean-room copy of `Work.FTS.EllipticEst.H2W.aSliceHonest`

The lemma `aSliceHonest` of `Submission/Work/FTS/EllipticEst/H2W/aSliceHonest.lean` states that
for a datum of the weak class `TT.EllWeakPos α 2 F Ψ` the angular slice
`θ ↦ (∂_θ²(z²∂_z²Ψ (z,·)))(θ)²·sin(2θ)^{-η}` is integrable on `Iθ`, for every `z ∈ Iz`.

This module reproves the *same statement under the same name*
(`Work.FTS.EllipticEst.H2W.aSliceHonest`) using only currently-buildable modules: the honesty
`HkMem α 0 (∂_θ²(z²∂_z²Ψ))` is taken from `AeDataAof.HkMem_zero_pthIter2_zsq_pzIter2` (which is
derived from `HkMem α 2 (∂_θ²Ψ)`, the field `memB` of the class), and the per-slice integrability
is the general slice extractor `ws_slot_slice` of `remov/wsAux`.

The original file needs `RPFresh/excess_finite` (currently not buildable), so the statement is
reproved here; the statement itself is unchanged.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.H2W.AeDataAof
import Submission.Work.FTS.EllipticEst.remov.wsAux
import Submission.Work.FTS.EllipticEst.TT.Slot11.MomentChainAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false

/-- **Honesty of the angular slice of `z² ∂_z²Ψ` at level `2`** (weak hypothesis class).

For every datum of `TT.EllWeakPos α 2 F Ψ` and every `z ∈ Iz`, the slice
`θ ↦ (∂_θ²(z²∂_z²Ψ(z,·)))(θ)²·sin(2θ)^{-η}` is integrable on `Iθ`. -/
theorem aSliceHonest : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      ∀ z ∈ Work.Spaces.Iz,
        MeasureTheory.IntegrableOn (fun θ =>
            (deriv (fun t => deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') t) θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
  intro α F Ψ hα hα4 h z hz
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · -- at `z = 0` the slice is identically zero
    subst hz0
    have hzero : (fun θ : ℝ =>
        (deriv (fun t => deriv (fun θ' => (0 : ℝ) ^ 2 * Work.Spaces.pzIter 2 Ψ 0 θ') t) θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) = fun _ => (0 : ℝ) := by
      have hfun : (fun θ' : ℝ => (0 : ℝ) ^ 2 * Work.Spaces.pzIter 2 Ψ 0 θ')
          = fun _ => (0 : ℝ) := by
        funext t; ring
      funext θ
      rw [hfun]
      simp
    rw [hzero]
    exact integrableOn_zero
  · -- the `ℋ⁰`-honesty of `∂_θ²(z²∂_z²Ψ)` gives the slice
    have hsq : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
      Work.H2W.MomentAe.smoothOpen_zsq hΨ
    have hmem : Work.Spaces.HkMem α 0
        (Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :=
      Work.FTS.EllipticEst.H2W.AeDataAofAux.HkMem_zero_pthIter2_zsq_pzIter2
        (α := α) hΨ h.memB
    have hsm2 : Work.FTS.EllipticEst.SmoothOpen
        (Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :=
      (hsq.pth).pth
    have hslot := Work.FTS.EllipticEst.remov.ws_slot_slice (g := Work.Spaces.pthIter 2
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) hsm2 hmem 0 (by omega) hzpos
    show MeasureTheory.IntegrableOn (fun θ =>
        (Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ
    simpa only [Work.Spaces.DzIter_zero] using hslot

end Work.FTS.EllipticEst.H2W
