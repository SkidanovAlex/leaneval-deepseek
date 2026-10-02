import Submission.Work.PTGeometric.SourceBlocks

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the block formula for the iterated concatenation of a list of loops

`Work.PTGeometric.genLoopListConcat i l` is the iterated concatenation of the list of cube loops `l`
along the coordinate `i` (`GenLoop.transAt i` applied from the right), and
`Work.PTGeometric.genLoopListConcatStep i l t` computes the *block* of the cube point `t`: the index
`k` of the element of the list that is consulted, together with the reparametrised cube point `u` at
which it is read (`k = l.length` meaning that the recursion has run off the end of the list, in which
case the value of the concatenation is the basepoint `x`).

This file records the resulting **block formula**

`genLoopListConcat i l t = l[k] u`  (or `x` if `k = l.length`),

which is the statement needed downstream to identify the zero set of an iterated concatenation with
the union of the elements' zero sets.

## Main results

* `Work.PTGeometric.genLoopListConcatStep_nil`, `..._cons_le`, `..._cons_gt` — the three defining
  equations of the recursion, in the two branches of the coordinate test;
* `Work.PTGeometric.dite_get_cons` — the list bookkeeping that shifts the index when a new element is
  consed on;
* `Work.PTGeometric.genLoopListConcat_eq_get` — the block formula.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Topology unitInterval
open Function Set

namespace Work.PTGeometric

noncomputable section

variable {N : Type*} [DecidableEq N] {X : Type} [TopologicalSpace X] {x : X}

/-- The recursion on the empty list: the block index is `0` and the point is unchanged. -/
theorem genLoopListConcatStep_nil (i : N) (t : N → Set.Icc (0 : ℝ) 1) :
    genLoopListConcatStep (X := X) (x := x) i [] t = (0, t) := by
  simp only [genLoopListConcatStep]

/-- The recursion on a first half (`t i ≤ 1/2`): it descends into the tail at the reparametrised
point and increments the block index. -/
theorem genLoopListConcatStep_cons_le (i : N) (g : GenLoop N X x)
    (l : List (GenLoop N X x)) (t : N → Set.Icc (0 : ℝ) 1)
    (h : ((t i : Set.Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 2) :
    genLoopListConcatStep (X := X) (x := x) i (g :: l) t =
      ((genLoopListConcatStep i l
          (Function.update t i (Set.projIcc (0 : ℝ) 1 (by norm_num) (2 * (t i : ℝ))))).1 + 1,
        (genLoopListConcatStep i l
          (Function.update t i (Set.projIcc (0 : ℝ) 1 (by norm_num) (2 * (t i : ℝ))))).2) := by
  simp only [genLoopListConcatStep, if_pos h]

/-- The recursion on a second half (`1/2 < t i`): it stops, with block index `0`, at the
reparametrised point. -/
theorem genLoopListConcatStep_cons_gt (i : N) (g : GenLoop N X x)
    (l : List (GenLoop N X x)) (t : N → Set.Icc (0 : ℝ) 1)
    (h : ¬ (((t i : Set.Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 2)) :
    genLoopListConcatStep (X := X) (x := x) i (g :: l) t =
      (0, Function.update t i (Set.projIcc (0 : ℝ) 1 (by norm_num) (2 * (t i : ℝ) - 1))) := by
  simp only [genLoopListConcatStep, if_neg h]

omit [DecidableEq N] in
/-- **The list bookkeeping of the block formula**: consing one more element in front shifts the block
index by one and replaces the head of the list by the new element.  This is the form in which the
block formula is applied at a reparametrised point in the induction step. -/
theorem dite_get_cons (g : GenLoop N X x) (l : List (GenLoop N X x)) (n : ℕ)
    (u : N → Set.Icc (0 : ℝ) 1) :
    (if h : n < l.length then l.get ⟨n, h⟩ u else x) =
      (if h : n + 1 < (g :: l).length then (g :: l).get ⟨n + 1, h⟩ u else x) := by
  by_cases h : n < l.length
  · have h' : n + 1 < (g :: l).length := by simpa using Nat.succ_lt_succ h
    rw [dif_pos h, dif_pos h', List.get_cons_succ]
  · have h' : ¬ (n + 1 < (g :: l).length) := by simpa using h
    rw [dif_neg h, dif_neg h']

/-- **The block formula for the iterated concatenation of a list of loops.**  At the cube point `t`
the concatenation `genLoopListConcat i l` reads the element `l[k]` of the list at the reparametrised
point `u`, where `(k, u) = genLoopListConcatStep i l t`; if the recursion has run off the end of the
list (`k = l.length`) the value is the basepoint `x`. -/
theorem genLoopListConcat_eq_get {N : Type*} [DecidableEq N] {X : Type} [TopologicalSpace X]
    {x : X} (i : N) (l : List (GenLoop N X x)) (t : N → Set.Icc (0 : ℝ) 1) :
    Work.PTGeometric.genLoopListConcat i l t =
      (if h : (Work.PTGeometric.genLoopListConcatStep i l t).1 < l.length
       then (l.get ⟨(Work.PTGeometric.genLoopListConcatStep i l t).1, h⟩)
         ((Work.PTGeometric.genLoopListConcatStep i l t).2)
       else x) := by
  induction l generalizing t with
  | nil =>
    rw [genLoopListConcat_nil, genLoopListConcatStep_nil]
    simp
  | cons g l ih =>
    rw [genLoopListConcat_cons]
    by_cases hc : ((t i : Set.Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 2
    · rw [genLoop_transAt_apply_of_le i (genLoopListConcat i l) g hc,
        genLoopListConcatStep_cons_le i g l t hc]
      dsimp only
      rw [← dite_get_cons g l _ _]
      exact ih _
    · rw [genLoop_transAt_apply_of_gt i (genLoopListConcat i l) g hc,
        genLoopListConcatStep_cons_gt i g l t hc]
      dsimp only
      simp

end

end Work.PTGeometric
