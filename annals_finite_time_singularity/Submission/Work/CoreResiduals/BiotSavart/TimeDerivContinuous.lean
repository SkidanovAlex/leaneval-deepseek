/-
# `Work.CoreResiduals.TimeDerivLocallyContinuous` — the weak time-regularity clause

The window theorem `Work.CoreResiduals.BiotSavart.biotSavartSpacetimeC1_holds` proves the joint `C¹`
statement for the Biot–Savart reconstruction of a spacetime vorticity satisfying
`BSAdmissibleOnWindow ω R T` together with `TimeDerivLocallyLipschitz ω T` — the hypothesis that the
slices `t ↦ ∂ₜω(y,t)` are locally *Lipschitz* in `t`, uniformly in `y`.

For the **strip** bundle (`BSAdmissibleStripFull α ω R S`) the second-order time-clause available is
`TimeDerivStripHolder α ω S`, which gives only that the slices `∂ₜω(y,·)` are `α`-Hölder in `t` on
the strip, and for `α < 1` an `α`-Hölder function need not be locally Lipschitz (think
`t ↦ t^α` near `0`).  The Lipschitz clause can therefore *not* be obtained from the strip bundle;
what is available — and what is what the proof of the window theorem actually uses (see
`biotSavartSpacetimeC1_holds`: `TimeDerivLocallyLipschitz` is used only to derive the continuity in
`t` of the slices `∂ₜω(y,·)`) — is the plain *continuity* of those slices:

`TimeDerivLocallyContinuous ω T`.

This is a genuine weakening (`timeDerivLocallyContinuous_of_locallyLipschitz`), so the window
theorem with `TimeDerivLocallyContinuous` in place of `TimeDerivLocallyLipschitz` is a strict
generalisation of `biotSavartSpacetimeC1_holds`.

The reason the *strip* statement needs the weaker form: to cover the endpoints `t = 0` and `t = S`
of the strip one glues `ω` to an affine-in-`t` extension outside `[0,S]`; at the junction the glued
field is differentiable with the right derivative (the strip bundle gives the two-sided
derivative at its endpoint times), but its `∂ₜ`-slices are *not* Lipschitz across the junction —
they are `α`-Hölder on the strip side and constant on the affine side, and `|t - t'|^α` cannot be
dominated by `|t - t'|` near the junction.  They are, however, continuous across the junction.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.CoreResiduals.Defs
import Submission.Work.CoreResiduals.BiotSavart.biotSavartSpacetimeC1_holds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Metric Filter Topology Set
open scoped Topology

namespace Work.CoreResiduals

/-- **The weak second-order time-clause of the window bundle.**  The `∂ₜ`-slices
`t ↦ ∂ₜω(y,t)` of the spacetime vorticity `ω` are continuous in `t`, locally around every time of
the half-window `preWindow T`, uniformly in the point `y`.

This is the local form of continuity in `t`; it is implied by the Lipschitz clause
`TimeDerivLocallyLipschitz` (see `timeDerivLocallyContinuous_of_locallyLipschitz`) and it is what
the joint `C¹` statement actually needs (the Lipschitz clause is used in
`biotSavartSpacetimeC1_holds` only through the continuity of those slices). -/
def TimeDerivLocallyContinuous (ω : R3 → ℝ → R3) (T : ℝ) : Prop :=
  ∀ t₀ ∈ Work.ConstructionInstance.preWindow T, ∃ ε : ℝ, 0 < ε ∧
    ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε), ∀ y : R3,
      ContinuousAt (fun s : ℝ => FiniteTimeSingularity.timeDeriv ω y s) t

/-- **Local Lipschitzness is stronger than local continuity.**  Directly from the Lipschitz bound:
on the interval `Ioo (t₀ - ε) (t₀ + ε)` the function `t ↦ ∂ₜω(y,t)` satisfies
`‖f t - f t₀‖ ≤ N * |t - t₀|`, hence is continuous at every point of that interval
(`continuousAt_of_norm_sub_le_mul_abs`). -/
theorem timeDerivLocallyContinuous_of_locallyLipschitz {ω : R3 → ℝ → R3} {T : ℝ}
    (h : TimeDerivLocallyLipschitz ω T) : TimeDerivLocallyContinuous ω T := by
  intro t₀ ht₀
  obtain ⟨ε, hε, N, hN⟩ := h t₀ ht₀
  refine ⟨ε, hε, fun t ht y => ?_⟩
  exact BiotSavart.continuousAt_of_norm_sub_le_mul_abs (isOpen_Ioo.mem_nhds ht)
    (fun s hs => hN s hs t ht y)

end Work.CoreResiduals
