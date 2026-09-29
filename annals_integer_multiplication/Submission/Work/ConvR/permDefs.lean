import Mathlib
import Submission.HvdH.Interfaces

/-!
# Definitions for the value-stack permutation word (`Work.ConvR.permTop`)

The word `permTop` reorders a stack `head ++ tail` (`head.length = n`) into
`σ.map (fun i => head.getD i .nil) ++ tail` where `σ` is a permutation of `List.range n`.

The program is a straight-line sequence of `KernelLib.roll`s: processing the elements of
`t = σ.reverse` in order, each is rolled to the front.  The positions are static (they only
depend on `t`), and after step `j` the front of the list holds the `j` moved elements (most
recent first) while the rest of the original `head` keeps its relative order, followed by `tail`.

This file only fixes the vocabulary; the two combinatorial facts live in
`Submission/Work/ConvR/foldRollPosList.lean` and `Submission/Work/ConvR/posListLt.lean`.
-/

set_option autoImplicit false

namespace Work.ConvR

open HvdH

/-- Move the element at position `p` of `w` to the front (the list-level action of `roll p`). -/
def rollL (p : ℕ) (w : List Val) : List Val := w.getD p .nil :: w.eraseIdx p

/-- Execute `rollL` at the positions `ps`, in order. -/
def foldRoll : List ℕ → List Val → List Val
  | [], w => w
  | p :: ps, w => foldRoll ps (rollL p w)

/-- The straight-line program: a `roll` at each position of `ps`, in order. -/
def rollList (rollP : ℕ → Cmd) : List ℕ → Cmd
  | [] => .skip
  | p :: ps => .seq (rollP p) (rollList rollP ps)

/-- Processing positions for the list `t` of original indices (in order): at step `j` the current
list is `prefix ++ (head with the indices `t.take j` removed) ++ tail`, so the element `t_j`
sits at position `j + #{i < t_j : i ∉ t.take j} = j + t_j - #{l < j : t_l < t_j}`. -/
def posList (t : List ℕ) : List ℕ :=
  (List.range t.length).map
    (fun j => j + t.getD j 0 - ((t.take j).filter (fun i => i < t.getD j 0)).length)

/-- `[0, m)` with the elements of `S` deleted, in increasing order.  This is the complement of
the moved set in the invariant above. -/
def remIdx (S : List ℕ) (m : ℕ) : List ℕ := (List.range m).filter (fun i => i ∉ S)

end Work.ConvR
