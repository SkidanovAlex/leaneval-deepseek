/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The decoration of a repeated block, at an arbitrary starting level

`decor c i L` is the running-weight decoration of a word `L`: the letter `(x, true)` read at running
weight `i` becomes the symbol `((x, i), true)` and the letter `(x, false)` read at running weight `i`
becomes `((x, i - c x), false)`.  Because the running level advances by the weight of the letters
already read (`decor_append`), the decoration of a repeated block `L` at level `i` is the
concatenation of the decorations of the individual copies, each read again at level `i` -- provided
the block `L` has vanishing total weight `lsig c L = 0`, so that the running level returns to `i`
after every copy.

This is the level-`i` strengthening of `decor_flatten_replicate` (which fixes `i = 0`); it is the
form needed when a block occurs inside a larger word rather than at the beginning.
-/

import Mathlib
import Submission.Work.OROneRel.MagnusGenDefs
import Submission.Work.OROneRel.decor_pow_flatMap

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- **The decoration of a repeated block, at level `i`.**  If the block `L` has vanishing total
weight `lsig c L = 0`, then the running level returns to `i` after each copy, and the decoration of
the concatenation of `n` copies of `L` is the concatenation of the decorations of the individual
copies, each read at level `i`. -/
theorem decor_flatten_replicate_at (c : α → ℤ) (L : List (α × Bool)) (hL : lsig c L = 0)
    (i : ℤ) (n : ℕ) :
    Work.OROneRel.decor c i (List.flatten (List.replicate n L)) =
      List.flatten (List.replicate n (Work.OROneRel.decor c i L)) := by
  induction n with
  | zero => simp [decor]
  | succ n ih =>
    simp only [List.replicate_succ, List.flatten_cons]
    rw [decor_append, hL, add_zero, ih]

theorem decor_flatten_replicate_gen {α : Type*} (c : α → ℤ) (L : List (α × Bool))
    (hL : Work.OROneRel.lsig c L = 0) (i : ℤ) (n : ℕ) :
    Work.OROneRel.decor c i (List.flatten (List.replicate n L)) =
      List.flatten (List.replicate n (Work.OROneRel.decor c i L)) :=
  decor_flatten_replicate_at c L hL i n

end Work.OROneRel
