import Submission.Work.Skeleton.Basic
import Submission.Work.Skeleton.Minimal
import Submission.Work.Skeleton.Reduction

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# A0 — Skeleton: assembly

This module is the entry point of Area A0.  It contains

* `Work.Skeleton.minSimpleOdd_false` — **the single remaining hole of the whole project**:
  the statement that no minimal counterexample exists (the Feit–Thompson theorem itself,
  in the form in which the rest of the project proves it);
* `Work.Skeleton.feit_thompson_univ` — the odd order theorem in a fixed universe, obtained
  from `feit_thompson_of_no_min` applied to `minSimpleOdd_false`.

`Submission.feit_thompson` (the top-level target) is wired to `feit_thompson_univ`, so that
the only hole in the dependency cone of the target is `minSimpleOdd_false` in this file.

The names are also exported into the `FT` namespace, the shared namespace convention of the
Feit–Thompson project.
-/

namespace Work.Skeleton

universe u

/-- **The single open hole of the Feit–Thompson drive.**  There is no minimal counterexample
to the odd order theorem: no finite group of odd order is simple, nonabelian with all proper
subgroups solvable.

Proving this statement (using the local analysis, character theory and coherence areas of the
project) completes the proof of `Submission.feit_thompson`. -/
theorem minSimpleOdd_false (G : Type u) [Group G] [Finite G] : ¬ MinSimpleOdd G := by
  sorry

/-- The odd order theorem in a fixed universe `u`, assembled from
`feit_thompson_of_no_min` and `minSimpleOdd_false`. -/
theorem feit_thompson_univ {G : Type u} [Group G] [Finite G] (hodd : Odd (Nat.card G)) :
    Group.IsSolvable G :=
  feit_thompson_of_no_min (fun G _ _ => minSimpleOdd_false G) hodd

end Work.Skeleton

namespace FT

export Work.Skeleton (MinSimpleOdd feit_thompson_of_no_min minSimpleOdd_false feit_thompson_univ)

end FT
