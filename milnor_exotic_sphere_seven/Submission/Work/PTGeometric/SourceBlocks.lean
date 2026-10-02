import Submission.Work.PTGeometric.ConcatLoop

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the block formula for the iterated concatenation of a list of loops

`Work.PTGeometric.genLoopListConcat i l` is the iterated concatenation of a list of cube loops along
the coordinate `i`; its class is the product of the classes of the list.  For the geometric half of
Pontryagin–Thom one must know *where* the concatenation agrees with which element of the list and
with which reparametrisation of the cube: the zero set of the concatenation is the union of the
elements' zero sets, each sitting in its own dyadic block of the cube.

This file fixes the recursion that computes, for a cube point `t`, the index `k` of the block and the
reparametrised point `u` at which the element is read:
`genLoopListConcat i l t = l[k] u`, with `l[k]` the `k`-th element of the list (`k = l.length` meaning
that the recursion has run off the end of the list, in which case the value is the basepoint).

## Main definitions

* `Work.PTGeometric.genLoopListConcatStep`
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Topology unitInterval
open Function Set

namespace Work.PTGeometric

noncomputable section

variable {N : Type*} [DecidableEq N] {X : Type} [TopologicalSpace X] {x : X}

/-- **The recursion computing the block of a cube point in the iterated concatenation.**

Given a cube point `t`, the iterated concatenation `genLoopListConcat i l` either consults the
element `l[k]` of the list at the reparametrised point `u` (when `k < l.length`), or is the basepoint
(when `k = l.length`).  The recursion reads the coordinate `i` of `t`: on the first half (with the
coordinate reparametrised by `2·`) it descends into the tail of the list and increments the index, and
on the second half it stops with index `0` and the coordinate reparametrised by `2· - 1`. -/
def genLoopListConcatStep (i : N) :
    List (GenLoop N X x) → (N → Set.Icc (0 : ℝ) 1) → ℕ × (N → Set.Icc (0 : ℝ) 1)
  | [], t => (0, t)
  | g :: l, t =>
    if ((t i : Set.Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 2 then
      let r := genLoopListConcatStep i l
        (Function.update t i (Set.projIcc (0 : ℝ) 1 (by norm_num) (2 * (t i : ℝ))))
      (r.1 + 1, r.2)
    else
      (0, Function.update t i (Set.projIcc (0 : ℝ) 1 (by norm_num) (2 * (t i : ℝ) - 1)))

end

end Work.PTGeometric
