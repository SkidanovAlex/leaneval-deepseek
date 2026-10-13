/-
# `Prop.l0_second_sharp` — the second-order angular estimate from the angular Step-2 `Prop`

Sibling reduction of the target `Work.FTS.EllipticEst.Prop.l0_second` (the weak-class form of
Step 2 of Elgindi's `prop:H2`): from the angular Step-2 estimate `Prop.Step2Ang` (the `Prop` of
`Prop/l0_step2abs.lean`, equivalent to `Ae.Step2`:

  `AeData α u G → HkSq α 0 (∂_θθu) ≤ C (HkSq α 0 G + α² HkSq α 0 (z∂_zu))`)

together with the first-order estimate `hfirst`, the target holds.  The proof is the squaring of
`nrm α (∂_θθu) ≤ C₂(nrm α G + α nrm α (z∂_zu))` with the Step-1 bound `α nrm α (z∂_zΨ) ≤ C₁ nrm α F`
supplied by `hfirst`.

This module is the interface consumed by `Cores/Level0Clean.l0_second_clean`; it is kept separate
from `Prop/l0_second.lean` only to stay inside the project's per-file size limit.

## Retired siblings

An earlier version of this module also carried `i1_bare_of_sharp` and `l0_second_of_i1sharp`, the
reductions of the target from the *sharp* `I₁` form of `Prop/i1_sharp.lean`.  They have been
retired with the interface they fed: the hypothesis `AngAWeak.AeI1` (the bare `I₁` coercivity in
`AeData` with only `HkMem α 0 (z∂_zu)`) is **false** — see
`H2W/AeWAux/NOTES_aeI1Data_FALSE.md` — and the corrected route (`Prop.i1_bare_hh`, whose extra
hypothesis is the *diagonal* second-order honesty `HkMem α 0 (∂_θθ(z∂_zΨ))`, a conjunct of the
strengthened class `TT.EllWeakPos`) is what `Prop/l0_second.lean` now uses, through the assembly
`Prop.l0_second_of_i1hh`.
-/

import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.Honest.Gap9Open
import Submission.Work.FTS.EllipticEst.Honest.SigmaPoincare
import Submission.Work.FTS.EllipticEst.TT.weakIPMems
import Submission.Work.FTS.EllipticEst.AngAWeak.Basic
import Submission.Work.FTS.EllipticEst.H2W.AeWAux.aeI4Of
import Submission.Work.FTS.EllipticEst.H2W.AeWAux.i4SliceIneq
import Submission.Work.FTS.EllipticEst.remov.AeIPMemsSlim
import Submission.Work.FTS.EllipticEst.H2W.Ae.Assembly
import Submission.Work.FTS.EllipticEst.AngSecond.IP_cauchy_schwarz
import Submission.Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem
import Submission.Work.FTS.EllipticEst.Honest.hksq_eq_w2_sliceIntegral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Prop

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 4000000
/-- **The target from the angular half of Step 2.**  Assuming the angular Step-2 estimate
`Prop.Step2Ang` (the `Prop` of `Prop/l0_step2abs.lean`:
`HkSq α 0 (∂_θθu) ≤ C(HkSq α 0 G + α²HkSq α 0 (z∂_zu))` in the class `H2W.Ae.AeData`) and the
first-order estimate `hfirst`, the second-order angular estimate of `l0_second` holds.

The proof is the squaring of `nrm α (∂_θθu) ≤ C₂(nrm α G + α nrm α (z∂_zu))` with the
first-order bound `α nrm α (z∂_zΨ) ≤ C₁ nrm α F` supplied by `hfirst`. -/
theorem l0_second_of_step2ang (C₁ : ℝ) (hC₁ : 0 < C₁)
    (hI : ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
        Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u)
          ≤ C * (Work.Spaces.HkSq α 0 G
              + α ^ 2 * Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz u z θ)))
    (hfirst : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ →
      Work.Spaces.HkMem α 0 Ψ ∧
      Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ) ∧
      Work.Spaces.HkMem α 0 (fun z θ => Ψ z θ / Real.cos θ) ∧
      Real.sqrt (Work.Spaces.HkSq α 0 Ψ)
        + α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ))
        + Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => Ψ z θ / Real.cos θ))
        ≤ C₁ * Real.sqrt (Work.Spaces.HkSq α 0 F)) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ →
      Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ))
        ≤ C * (Real.sqrt (Work.Spaces.HkSq α 0 F)
            + α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ))) := by
  obtain ⟨C₂, hC₂pos, hI'⟩ := hI
  refine ⟨Real.sqrt (C₂ * (1 + C₁ ^ 2)) + 1, by positivity, ?_⟩
  intro α F Ψ hα hα4 hW
  obtain ⟨hmemΨ, hmemU, hmemPb, hstep1⟩ := hfirst α F Ψ hα hα4 hW
  have haeΨ : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar Ψ z = 0 := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall fun z hz => hW.orthPsi z hz
  have haeF : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar F z = 0 := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall fun z hz => hW.orthF z hz
  have hAe : Work.FTS.EllipticEst.H2W.Ae.AeData α Ψ F :=
    ⟨hα, hα4, fun z hz θ h0 h1 => hW.eq z hz θ h0 h1, hW.zero, hW.pi_half, hW.smooth,
      hW.memF, hW.memA, hW.memB, haeΨ, haeF⟩
  have hkey := hI' α Ψ F hAe
  set U : ℝ → ℝ → ℝ := fun z θ => z * Work.Spaces.pz Ψ z θ with hU
  have hU2 : α ^ 2 * Work.Spaces.HkSq α 0 U ≤ C₁ ^ 2 * Work.Spaces.HkSq α 0 F := by
    have h1 : α * Real.sqrt (Work.Spaces.HkSq α 0 U)
        ≤ C₁ * Real.sqrt (Work.Spaces.HkSq α 0 F) := by
      have h2 : α * Real.sqrt (Work.Spaces.HkSq α 0 U)
          ≤ Real.sqrt (Work.Spaces.HkSq α 0 Ψ)
              + α * Real.sqrt (Work.Spaces.HkSq α 0 U)
              + Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => Ψ z θ / Real.cos θ)) := by
        have h3 : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 0 Ψ) := Real.sqrt_nonneg _
        have h4 : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => Ψ z θ / Real.cos θ)) :=
          Real.sqrt_nonneg _
        linarith
      have h5 : Real.sqrt (Work.Spaces.HkSq α 0 Ψ)
            + α * Real.sqrt (Work.Spaces.HkSq α 0 U)
            + Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => Ψ z θ / Real.cos θ))
          ≤ C₁ * Real.sqrt (Work.Spaces.HkSq α 0 F) := by
        rw [hU]; exact hstep1
      linarith
    have h2 := pow_le_pow_left₀ (mul_nonneg hα.le (Real.sqrt_nonneg _)) h1 2
    rw [mul_pow, mul_pow, Real.sq_sqrt (Work.FTS.EllipticEst.Honest.HkSq_zero_nonneg α U),
      Real.sq_sqrt (Work.FTS.EllipticEst.Honest.HkSq_zero_nonneg α F)] at h2
    exact h2
  have hSq : Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ)
      ≤ (C₂ * (1 + C₁ ^ 2)) * Work.Spaces.HkSq α 0 F := by
    have hG0 : 0 ≤ Work.Spaces.HkSq α 0 F :=
      Work.FTS.EllipticEst.Honest.HkSq_zero_nonneg α F
    have h1 : Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ)
        ≤ C₂ * (Work.Spaces.HkSq α 0 F + C₁ ^ 2 * Work.Spaces.HkSq α 0 F) := by
      have h2 : Work.Spaces.HkSq α 0 F + α ^ 2 * Work.Spaces.HkSq α 0 U
          ≤ Work.Spaces.HkSq α 0 F + C₁ ^ 2 * Work.Spaces.HkSq α 0 F := by linarith
      calc Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ)
          ≤ C₂ * (Work.Spaces.HkSq α 0 F + α ^ 2 * Work.Spaces.HkSq α 0 U) := hkey
        _ ≤ C₂ * (Work.Spaces.HkSq α 0 F + C₁ ^ 2 * Work.Spaces.HkSq α 0 F) :=
            mul_le_mul_of_nonneg_left h2 hC₂pos.le
    have h3 : C₂ * (Work.Spaces.HkSq α 0 F + C₁ ^ 2 * Work.Spaces.HkSq α 0 F)
        = (C₂ * (1 + C₁ ^ 2)) * Work.Spaces.HkSq α 0 F := by ring
    linarith [h1, h3.le, h3.ge]
  have hK0 : 0 ≤ C₂ * (1 + C₁ ^ 2) := by positivity
  have hB := Real.sqrt_le_sqrt hSq
  rw [Real.sqrt_mul hK0] at hB
  have hfin : Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ))
      ≤ (Real.sqrt (C₂ * (1 + C₁ ^ 2)) + 1)
        * (Real.sqrt (Work.Spaces.HkSq α 0 F)
          + α * Real.sqrt (Work.Spaces.HkSq α 0 U)) := by
    have h2 : Real.sqrt (C₂ * (1 + C₁ ^ 2)) * Real.sqrt (Work.Spaces.HkSq α 0 F)
        ≤ (Real.sqrt (C₂ * (1 + C₁ ^ 2)) + 1)
          * (Real.sqrt (Work.Spaces.HkSq α 0 F)
            + α * Real.sqrt (Work.Spaces.HkSq α 0 U)) := by
      have h3 : 0 ≤ Real.sqrt (C₂ * (1 + C₁ ^ 2)) := Real.sqrt_nonneg _
      have h4 : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 0 F) := Real.sqrt_nonneg _
      have h5 : 0 ≤ α * Real.sqrt (Work.Spaces.HkSq α 0 U) :=
        mul_nonneg hα.le (Real.sqrt_nonneg _)
      nlinarith [h3, h4, h5]
    linarith [hB, h2]
  rw [hU] at hfin
  exact hfin



end Work.FTS.EllipticEst.Prop
