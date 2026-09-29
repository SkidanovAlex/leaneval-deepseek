import Mathlib
import Submission.Work.Layout.SortDefs

/-!
# `dupInt`: definitions factored out so that the step lemmas can be proved in parallel

`Sk.dupInt S B T d` (defined in `Submission/Work/Layout/SortDefs.lean`) copies the top `int` of stack
`S` onto stack `B`, keeping `S`, using `T` as a reversal buffer and `d` as the pending counter of
`mvA`.

It is `mvA S T d` (which replaces the top value `v` of `S` by `v.enc.reverse ++ [gMark]` on `T`)
followed by the loop below, which pops the glyphs of `T` one at a time — pushing each one on `S` and
on `B` — and stops when the boundary marker `gMark` is popped.
-/

set_option autoImplicit false

namespace Work.Layout
namespace Sk

open HvdH

/-- Body of the `dupInt` loop: pop the top glyph of `T`; when it is the boundary marker `gMark`,
stop the loop, otherwise push it on `S` **and** on `B` and continue. -/
def dupIntBody (S B T : Stk) : Cmd :=
  .seq (.pop T rK)
    (.ite rK gMark (.set rF gMark)
      (.seq (.push S rK) (.seq (.push B rK) (.set rF Glyph.cons))))

/-- `dupInt`, in terms of the loop body `dupIntBody`. -/
theorem dupInt_eq (S B T d : Stk) :
    dupInt S B T d =
      .seq (mvA S T d) (.seq (.set rF Glyph.cons) (.loop rF Glyph.cons (dupIntBody S B T))) := rfl

/-- The stacks the `dupInt` loop body touches. -/
theorem cmdTouches_dupIntBody (S B T : Stk) : cmdTouches (dupIntBody S B T) = {S, T, B} := by
  simp only [dupIntBody, cmdTouches]
  ext k
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton, Finset.notMem_empty,
    or_false]
  tauto

/-- The stacks `dupInt` touches. -/
theorem cmdTouches_dupInt (S B T d : Stk) : cmdTouches (dupInt S B T d) = {S, T, B, d} := by
  simp only [dupInt_eq, dupIntBody, cmdTouches, cmdTouches_mvA]
  ext k
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton, Finset.notMem_empty,
    or_false]
  tauto

end Sk
end Work.Layout
