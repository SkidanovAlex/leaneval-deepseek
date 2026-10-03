import Mathlib
import Submission.Work.Peluse.UControl.HistInit

/-!
# The reachability argument of phase 1

While the chain has a live slot that is *not* a descendant of the top slot, the deterministic
selection picks a slot of degree `< d` (Peluse's Lemma 4.4), so `histPhase1Step'` applies and keep
the invariant.  A state satisfying `Phase1` can never be *linear* (its `P`-descendant has degree
`d ≥ 2`), so the chain — which stops exactly at the linear states — must reach a `Phase1Done` state.
This file collects the transport-independent part of that argument; the well-founded recursion itself
is `HState.step` together with `histStep_lt` (`histWeightStepEq` is what proves the decrease).
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Polynomial

/-- A chain state together with its history length (which grows at every step). -/
abbrev HState (d : ℕ) := Σ n : ℕ, HistData d n

/-- The stopping condition of the chain: every live slot is linear in `y`. -/
def HistData.IsLinearX {d n : ℕ} (X : HistData d n) : Prop :=
  ∀ x ∈ X.H, (X.Q x.1 x.2).natDegree ≤ 1

lemma HistData.H_nonempty_of_not_linear {d n : ℕ} (X : HistData d n) (h : ¬ X.IsLinearX) :
    X.H.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hne
  exact h (fun x hx => by rw [hne] at hx; exact absurd hx (by simp))

/-- At a state which is not `Phase1Done` there is a non-`P` slot, and the selected one has degree
`< d`. -/
lemma Phase1.degree_sel_lt {d n : ℕ} {lc : ℤ} {X : HistData d n} (h : Phase1 d n lc X)
    (hnd : ¬ Phase1Done X) (hne : X.H.Nonempty) :
    (X.Q (X.sel hne).1 (X.sel hne).2).natDegree < d := by
  obtain ⟨x, hx, hxne⟩ : ∃ x ∈ X.H, x.1 ≠ (Sum.inr 0 : InitIdx d) := by
    by_contra hc
    exact hnd (fun y hy => by
      by_contra hy'
      exact hc ⟨y, hy, hy'⟩)
  refine lt_of_le_of_lt ?_ (h.nP x hx hxne)
  rw [X.sel_degree hne]
  exact X.minDeg_le hne x hx

/-- A phase-1 state is never linear (its `P`-descendant has degree `d ≥ 2`). -/
lemma Phase1.not_linear {d n : ℕ} {lc : ℤ} {X : HistData d n} (hd2 : 2 ≤ d)
    (h : Phase1 d n lc X) : ¬ X.IsLinearX := by
  intro hl
  have h1 := hl ((Sum.inr 0 : InitIdx d), 0) (h.pLive 0)
  rw [h.pDeg 0] at h1
  omega

/-- One step of the phase-1 chain, at the deterministic selection. -/
def HState.step {d : ℕ} (X : HState d) (hne : X.2.H.Nonempty) : HState d :=
  ⟨X.1 + 1, X.2.step (X.2.sel hne).1 (X.2.sel hne).2 (X.2.sel_mem_H hne)⟩

/-- The phase-1 invariant is preserved by one step at the deterministic selection. -/
lemma Phase1.step_sel {d n : ℕ} {lc : ℤ} (hd1 : 1 ≤ d) {X : HistData d n}
    (h : Phase1 d n lc X) (hnd : ¬ Phase1Done X) (hne : X.H.Nonempty) :
    Phase1 d (n + 1) lc (X.step (X.sel hne).1 (X.sel hne).2 (X.sel_mem_H hne)) :=
  histPhase1Step' hd1 X h (X.sel hne).1 (X.sel hne).2 (X.sel_mem_H hne)
    (h.degree_sel_lt hnd hne)

end

end Work.Peluse.UControl
