import Mathlib
import Submission.Work.Smooth.Jordan.All

/-!
# The index on the two sides of a simple closed curve

This file collects the elementary index-theoretic consequences of the separation theory that are
proved from the *sibling* chapter `Submission/Work/Smooth/Jordan` alone: the index of a closed
curve is locally constant off the trace (`ind_local`), integer valued (`wind_mem_int`), vanishes
outside a large disc (`ind_vanishes_at_infinity`) and is constant on preconnected sets
(`ind_const_on_preconnected`).

* `ind_eq_zero_of_unbounded` — the index vanishes identically on every **unbounded** preconnected
  subset of the complement of the trace.  This is the value of the index on the unbounded side of a
  simple closed curve.
-/

open Set
open Work.Smooth.Jordan

namespace Work.Smooth.JordanSeparation

noncomputable section

/-- **The index vanishes on an unbounded preconnected subset of the complement.**

`ind c` is constant on the preconnected set `W` (`ind_const_on_preconnected`); picking a point of
`W` of norm larger than the bound of `ind_vanishes_at_infinity` shows that constant to be `0`. -/
theorem ind_eq_zero_of_unbounded (c : SmoothPlaneCurve) {W : Set ℂ} (hW : IsPreconnected W)
    (hsub : W ⊆ c.traceᶜ) (hunbdd : ∀ R : ℝ, ∃ x ∈ W, R < ‖x‖) :
    ∀ x ∈ W, ind c x = 0 := by
  obtain ⟨R, hR⟩ := ind_vanishes_at_infinity c
  obtain ⟨x₀, hx₀W, hx₀R⟩ := hunbdd R
  have hzero : ind c x₀ = 0 := hR x₀ hx₀R
  intro x hx
  rw [ind_const_on_preconnected c hW hsub hx hx₀W, hzero]

end

end Work.Smooth.JordanSeparation
