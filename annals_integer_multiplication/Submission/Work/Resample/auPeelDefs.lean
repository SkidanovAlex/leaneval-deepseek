import Mathlib
import Submission.Work.Resample.pbDefs
import Submission.Work.Kernel.mapListPhaseA
import Submission.Work.Layout.Move
import Submission.Work.Layout.mvVal_ev_full

/-!
# The "peel" word: moving a whole list value from stack 0 onto a fixed stack `T`

`Work.Resample.auPeel` needs the following word: given a list value `ofList xs` on top of stack 0 it
moves its elements one by one onto a fixed stack `T ≠ 0` (reversing them in the process), leaving
`rest` on stack 0 and keeping the previous content of `T` below the moved block.

The program is the phase-A loop of `Work.Kernel.mapList` with the destination stack `1` replaced by
`T` and the `mvVal` scratch stacks `4, 5` replaced by two fresh stacks `c, d`:

* `peelBody T c d`: peek the top glyph of stack 0; on `nil` pop it and stop; otherwise pop it and
  move the exposed value to stack `T` (through `c`, `d`), then continue;
* `peelProg T c d`: initialise the loop register and run the body.

This file only fixes the definitions and the elementary size bookkeeping; the `Ev`-level proofs
(the two loop-body cases and the loop itself) live in `Submission/Work/Resample/auPeel.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.Resample

open HvdH
open Work.Layout

/-- Body of the peel loop: peek the top glyph of stack 0; at `nil` pop it and stop, otherwise pop
it and move the exposed value to stack `T` (through the scratch stacks `c`, `d`). -/
def peelBody (T c d : Stk) : Cmd :=
  .seq (.peek 0 rA)
    (.ite rA Glyph.nil
      (.seq (.pop 0 rA) (.set rLoopG Glyph.eos))
      (.seq (.pop 0 rA) (.seq (mvVal 0 T c d) (.set rLoopG Glyph.cons))))

/-- Peel the whole list value on top of stack 0 onto stack `T` (reversing it). -/
def peelProg (T c d : Stk) : Cmd :=
  seqs [.set rLoopG Glyph.cons, .loop rLoopG Glyph.cons (peelBody T c d)]

/-! ## Elementary facts -/

/-- Two scratch stacks distinct from `0`, from `T ≠ 0` and from each other. -/
theorem peelScratch (T : Stk) (hT : T ≠ 0) :
    ∃ c d : Stk, c ≠ d ∧ c ≠ 0 ∧ c ≠ T ∧ d ≠ 0 ∧ d ≠ T := by
  by_cases h1 : T = 1
  · subst h1; exact ⟨2, 3, by decide, by decide, by decide, by decide, by decide⟩
  · by_cases h2 : T = 2
    · subst h2; exact ⟨1, 3, by decide, by decide, by decide, by decide, by decide⟩
    · exact ⟨1, 2, by decide, by decide, Ne.symm h1, by decide, Ne.symm h2⟩

/-- `vsz` of a list value. -/
theorem peelVsz_ofList (l : List Val) : vsz (ofList l) = l.length + (l.map vsz).sum + 1 := by
  induction l with
  | nil => simp [ofList, vsz, Val.enc]
  | cons v vs ih =>
    have h : vsz (ofList (v :: vs)) = vsz v + vsz (ofList vs) + 1 := by
      show (Val.cons v (ofList vs)).enc.length = _
      simp only [Val.enc, List.length_cons, List.length_append, vsz]
    rw [h, ih]
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    ring

/-- Every value has size at least one, so the number of elements is at most the total size. -/
theorem peelLen_le_sum (l : List Val) : l.length ≤ (l.map vsz).sum := by
  induction l with
  | nil => simp
  | cons v vs ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    have := one_le_vsz v
    omega

end Work.Resample
