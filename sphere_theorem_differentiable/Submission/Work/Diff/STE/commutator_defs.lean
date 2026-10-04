import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Definitions for the commutator estimate (`Work.Diff.STE.commutator_estimate`)

The Leibniz rule for iterated partial derivatives `pdList` is organised by an explicit
enumeration of the ways of distributing the `k` derivatives between the two factors:

* `splits l` lists all pairs of complementary subsequences `(p.1, p.2)` of `l`.

With the `List.foldr` convention of `pdList` (the *head* of the list is the outermost
derivative), the Leibniz rule reads

  `pdList l (fun y => F y * g y) = fun y => ∑ p ∈ splits l, ∂^{p.1}F y * ∂^{p.2}g y`.

This file only contains the definition (`splits`); the statements about it live in the
sibling files of this area.
-/

noncomputable section

namespace Work.Diff.STE

/-- All ways of splitting a list into two complementary (order preserving) subsequences:
`splits [i, j] = [([i,j],[]), ([i],[j]), ([j],[i]), ([],[i,j])]`.
This is the index set of the iterated Leibniz rule for `pdList`. -/
def splits {α : Type*} : List α → List (List α × List α)
  | [] => [([], [])]
  | i :: l => (splits l).map (fun p => (i :: p.1, p.2)) ++ (splits l).map (fun p => (p.1, i :: p.2))

end Work.Diff.STE
