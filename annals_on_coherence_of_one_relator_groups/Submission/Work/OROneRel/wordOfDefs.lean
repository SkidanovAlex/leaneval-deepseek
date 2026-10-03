/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# `wordOf`: the shared reduced-word function

`wordOf r` is the reduced word of `r : FreeGroup α`, with `Classical.decEq α` fixed as the decidable
equality, so that no statement that mentions it has to carry a `DecidableEq α` hypothesis.  It is
`FreeGroup.toWord`, with the instance argument hidden.

This declaration used to exist **twice** in the workspace -- verbatim in
`Submission/Work/OROneRel/MagnusGenDefs.lean` and in
`Submission/Work/OROneRel/weinbaumMonoDefs.lean` -- which made it impossible for any file to import
both the Magnus-rewriting / `ℤ`-cover development and the Weinbaum (pad) development, and in
particular prevented the free-kernel route to the two-letter cases of the Magnus step
(`kernel_cpChi_free`, `mmStepData_of_coprime_powers`, `magnusStepData_cpRelator`) from being combined
with the machinery on which the target `magnus_step_root_no_eps_zero` rests.  It now lives here, in a
leaf module that both sides import, so that the two cones *share* the declaration without being
merged (merging them by import would drag unrelated duplicate names, e.g. `RhoRewrite.rew`, into each
other's scope).  See `NOTES_magnus_step_root_no_eps_zero.md`, SESSION 5 § 3.
-/

import Mathlib

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- The reduced word of an element of a free group, with `Classical.decEq α` as the decidable
equality (a name that hides the decidability instance). -/
noncomputable def wordOf (u : FreeGroup α) : List (α × Bool) :=
  letI := Classical.decEq α
  u.toWord

/-- `wordOf` represents the element it is taken of. -/
theorem mk_wordOf (u : FreeGroup α) : FreeGroup.mk (wordOf u) = u := by
  classical
  rw [wordOf, FreeGroup.mk_toWord]

end Work.OROneRel
