import Mathlib
import Submission.Work.BoxShrink.PinchOff.Perp

/-!
# The local cancellation move of the push-off

The push-off of the box region off a transverse and tame trace, inside the box, is a *local* move at
each crossing of a loop with the trace, iterated.  The local move — eliminate a detour of a loop
through the other side of the trace — is the following elementary fact about paths.

Let `U` be an **open convex** region of a real normed space, and let the trace of the slicing plane
in `U` be the level set `U ∩ {f = 0}` of a nonzero *linear* functional `f` (this is what a
transversality hypothesis gives after a local straightening of the trace).  Then:

* a path in `U` whose endpoints lie *strictly* on one side of `{f = 0}` can be replaced, relative to
  its endpoints and inside `U`, by a path which does not meet `{f = 0}` — the straight segment
  (`exists_path_avoiding_of_convex`).

That is exactly the cancellation move: applied to the "detour" of a loop, i.e. to the piece of the
loop from a crossing `x` with the trace to the next crossing `y` together with the pieces of the
loop just before `x` and just after `y` (whose endpoints lie strictly on one side of the trace, by
the definition of `x`, `y` as crossings), it produces a loop homotopic to the original one with two
fewer crossings with the trace.  The residual `TracePerpSlice` is the statement that this can be
iterated to exhaustion, i.e. that the crossings of every loop of the box region can be paired
consecutively in such a way that each detour lies inside a convex chart contained in the box.

The *hypothesis* of non-vanishing crossing number of the residual enters the pairing (not the local
move): the algebraic crossing number of the loop with each *component* of the trace must vanish, and
component-wise vanishing numbers are what allows the crossings on a component to be paired.  At the
parent chapter's counterexample (`Work.BoxShrink.Bubble.standard_counterexample`: the standard torus,
`s = 5/2`, `c = 0`, `σ = swap 1 2`, `u = 0`, where both endpoint hypotheses hold and the span form of
the residual fails) the trace is a pair of meridians and the longitude loop which fails to be
pushable has crossing number `±1` with each of them: the local move is inapplicable there, exactly as
it should be.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The local cancellation move**: two points of an open convex region lying strictly on one side
of a hyperplane can be joined by a path of the region which never meets the hyperplane. -/
theorem exists_path_avoiding_of_convex {U : Set E} (hU : IsOpen U) (hc : Convex ℝ U)
    {f : E →L[ℝ] ℝ} {p q : E} (hp : p ∈ U) (hq : q ∈ U) (hfp : 0 < f p) (hfq : 0 < f q) :
    ∃ γ : ℝ → E, Continuous γ ∧ γ 0 = p ∧ γ 1 = q ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ U ∧ 0 < f (γ t) := by
  refine ⟨fun t => (1 - t) • p + t • q, ?_, by simp, by simp, ?_⟩
  · fun_prop
  · intro t ht
    rw [Set.mem_Icc] at ht
    have hconv : (1 - t) • p + t • q ∈ U :=
      hc hp hq (by linarith [ht.1]) (by linarith [ht.2]) (by ring)
    refine ⟨hconv, ?_⟩
    have hval : f ((1 - t) • p + t • q) = (1 - t) * f p + t * f q := by
      rw [map_add, map_smul, map_smul]
      rfl
    rw [hval]
    have hmin : 0 < min (f p) (f q) := lt_min hfp hfq
    have hle : min (f p) (f q) ≤ (1 - t) * f p + t * f q := by
      rcases le_total (f p) (f q) with h | h
      · rw [min_eq_left h]; nlinarith [ht.1, ht.2]
      · rw [min_eq_right h]; nlinarith [ht.1, ht.2]
    linarith

/-- The same, with the "trace" an arbitrary set `L` contained in the hyperplane and containing the
segment's complement: the path avoids `L` whenever it stays strictly on one side. -/
theorem exists_path_avoiding_of_convex_subset {U L : Set E} (hU : IsOpen U) (hc : Convex ℝ U)
    {f : E →L[ℝ] ℝ} {p q : E} (hp : p ∈ U) (hq : q ∈ U) (hfp : 0 < f p) (hfq : 0 < f q)
    (hL : L ⊆ {x : E | f x = 0}) :
    ∃ γ : ℝ → E, Continuous γ ∧ γ 0 = p ∧ γ 1 = q ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ U ∧ γ t ∉ L := by
  obtain ⟨γ, hcont, h0, h1, hpos⟩ := exists_path_avoiding_of_convex hU hc hp hq hfp hfq
  refine ⟨γ, hcont, h0, h1, fun t ht => ⟨(hpos t ht).1, fun hmem => ?_⟩⟩
  exact absurd (hL hmem) (ne_of_gt (hpos t ht).2)

end

end Work.BoxShrink.PinchOff
