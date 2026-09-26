import Submission.Work.BoxShrink.Bubble.HalfDefs
import Submission.Work.BoxShrink.Bubble.Flow
import Submission.Work.BoxShrink.Bubble.Reduce
import Submission.Work.BoxShrink.Pinch.BubbleHalfRefuted

/-!
# The parameter-plane flow route is impossible

The assignment's plan for the push-off (`Submission/Work/BoxShrink/Bubble/PLAN.md`, §"The plan")
asks for a `2πℤ²`-periodic continuous flow `Φ_flow : ℝ → ℝ² → ℝ²` of the parameter plane carrying
the preimage of the box region into the preimage of the union of the two half-regions.  The sibling
chapter's interface `Work.BoxShrink.Bubble.slicePushOff_of_planeFlow` turns such a flow into
`Work.BoxShrink.Bubble.SlicePushOff`, and `SlicePushOff` gives Pardon's Lemma 3 conclusion
`Work.BoxShrink.Bubble.BubbleHalf` **unconditionally** (with no hypothesis on the two cuts at all).

This module records that consequence, and its contrapositive:

* `Work.BoxShrink.Pinch.bubbleHalf_of_planeFlow` — any such flow at any box/plane configuration
  already gives `BubbleHalf` there;
* `Work.BoxShrink.Pinch.not_exists_planeFlow_of_not_bubbleHalf` — hence **no such flow exists at any
  configuration at which the box region carries an essential loop but Pardon's conclusion fails**.

That second statement is not vacuous, and it is the reason the flow route has to be abandoned: at
the standard round torus with the small box (`s = 3/2`, `c = 0`, `σ = swap 1 2`, `u = 0`) the box
region *does* carry an essential loop (`Work.BoxShrink.Pinch.boxRegion_essential`) while Pardon's
conclusion *fails* (`Work.BoxShrink.Pinch.BubbleHalfRefuted`, whose two halves are inessential).
Both are proved, from source, in `BubbleHalfRefuted.lean`, so the impossibility below is
*unconditional* (`not_exists_planeFlow_standard_small`).

So the flow route is *refuted*, not merely hard: and with it every "deformation" route for the
push-off — a homotopy or isotopy of the loops of the box region off the cutting plane would give the
same conclusion (`Work.BoxShrink.Pinch.bubbleHalf_of_splits`, and the warning at the head of
`Work.BoxShrink.Pinch.HalfSplit`).  The push-off is a *topological* statement (Pardon's Lemma 2.3:
the invariant `im (H₁ (F ∩ int S_t)) → H₁ (F)` cannot jump from the whole of `H₁ (F)` to nothing in
a single `2`-surgery), and that is the route which `SliceSpanStep.lean` isolates.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Pinch

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-- **The plane flow of the plan already gives Pardon's Lemma 3 conclusion.**  A continuous
equivariant `Φ` carrying the box region into the union of the two half-regions at time `1` gives
`SlicePushOff` (`Work.BoxShrink.Bubble.slicePushOff_of_planeFlow`), and `SlicePushOff` gives
`BubbleHalf` — with *no* hypothesis on the two cuts. -/
theorem bubbleHalf_of_planeFlow {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (Φ : ℝ → ℝ × ℝ → ℝ × ℝ) (hcont : Continuous (Function.uncurry Φ))
    (hperiod : ∀ (r : ℝ) (q : ℝ × ℝ) (k l : ℤ),
      Φ r (q.1 + k * (2 * Real.pi), q.2 + l * (2 * Real.pi)) =
        ((Φ r q).1 + k * (2 * Real.pi), (Φ r q).2 + l * (2 * Real.pi)))
    (hmaps : ∀ q : ℝ × ℝ,
      P.psi q.1 q.2 ∈ Work.BoxShrink.Core.boxRegion P s c σ →
        P.psi (Φ 1 q).1 (Φ 1 q).2 ∈
          Work.BoxShrink.Core.upperRegion P s c σ u ∪ Work.BoxShrink.Core.lowerRegion P s c σ u) :
    Work.BoxShrink.Bubble.BubbleHalf P s c σ u :=
  fun hbox =>
    Work.BoxShrink.Bubble.containsEssentialLoop_half_of_slicePushOff
      (Work.BoxShrink.Bubble.slicePushOff_of_planeFlow Φ hcont hperiod hmaps) hbox

/-- **No plane flow exists where Pardon's conclusion fails.**  If the box region carries an
essential loop and `BubbleHalf` fails, there is no continuous, `2πℤ²`-equivariant flow of the
parameter plane carrying the box region into the union of the two half-regions.  This is the
contrapositive of `bubbleHalf_of_planeFlow`, and it is the rigorous statement that the flow route of
`PLAN.md` cannot be carried out (witnessed by the standard small-box configuration, see the module
docstring). -/
theorem not_exists_planeFlow_of_not_bubbleHalf {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hbox : P.ContainsEssentialLoop (Work.BoxShrink.Core.boxRegion P s c σ))
    (hb : ¬ Work.BoxShrink.Bubble.BubbleHalf P s c σ u) :
    ¬ ∃ Φ : ℝ → ℝ × ℝ → ℝ × ℝ,
        Continuous (Function.uncurry Φ) ∧
        (∀ (r : ℝ) (q : ℝ × ℝ) (k l : ℤ),
          Φ r (q.1 + k * (2 * Real.pi), q.2 + l * (2 * Real.pi)) =
            ((Φ r q).1 + k * (2 * Real.pi), (Φ r q).2 + l * (2 * Real.pi))) ∧
        (∀ q : ℝ × ℝ,
          P.psi q.1 q.2 ∈ Work.BoxShrink.Core.boxRegion P s c σ →
            P.psi (Φ 1 q).1 (Φ 1 q).2 ∈
              Work.BoxShrink.Core.upperRegion P s c σ u ∪
                Work.BoxShrink.Core.lowerRegion P s c σ u) := by
  rintro ⟨Φ, hcont, hperiod, hmaps⟩
  exact hb (bubbleHalf_of_planeFlow Φ hcont hperiod hmaps)

/-- **No parameter-plane flow exists at the standard small box**, unconditionally: the flow would
give `BubbleHalf` (`bubbleHalf_of_planeFlow`) there, but the box region is essential
(`BubbleHalfRefuted.boxRegion_essential`) while `BubbleHalf` fails (`BubbleHalfRefuted`).  This is
the rigorous refutation of the flow route of the assignment's plan. -/
theorem not_exists_planeFlow_standard_small :
    ¬ ∃ Φ : ℝ → ℝ × ℝ → ℝ × ℝ,
        Continuous (Function.uncurry Φ) ∧
        (∀ (r : ℝ) (q : ℝ × ℝ) (k l : ℤ),
          Φ r (q.1 + k * (2 * Real.pi), q.2 + l * (2 * Real.pi)) =
            ((Φ r q).1 + k * (2 * Real.pi), (Φ r q).2 + l * (2 * Real.pi))) ∧
        (∀ q : ℝ × ℝ,
          Work.CoreTopology.standard.psi q.1 q.2 ∈
              Work.BoxShrink.Core.boxRegion Work.CoreTopology.standard (3 / 2) 0 (Equiv.swap 1 2) →
            Work.CoreTopology.standard.psi (Φ 1 q).1 (Φ 1 q).2 ∈
              Work.BoxShrink.Core.upperRegion Work.CoreTopology.standard (3 / 2) 0 (Equiv.swap 1 2) 0 ∪
                Work.BoxShrink.Core.lowerRegion Work.CoreTopology.standard (3 / 2) 0 (Equiv.swap 1 2) 0) :=
  not_exists_planeFlow_of_not_bubbleHalf (P := Work.CoreTopology.standard) (s := 3 / 2) (c := 0)
    (σ := Equiv.swap 1 2) (u := 0) boxRegion_essential BubbleHalfRefuted

end

end Work.BoxShrink.Pinch
