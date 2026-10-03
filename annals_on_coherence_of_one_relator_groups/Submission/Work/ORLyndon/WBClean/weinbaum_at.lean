import Mathlib
import Submission.Work.OROneRel.Interface
import Submission.Work.OROneRel.weinbaumDefs
import Submission.Work.ORLyndon.WBClean.weinbaumAt_of_expSum_eq_zero
import Submission.Work.ORLyndon.WBClean.weinbaumAt_of_expSum_ne_zero


/-!
# Import-hygiene copy of `Submission.Work.OROneRel.weinbaum_at`

**This file is a verbatim copy** of `Submission/Work/OROneRel/weinbaum_at.lean`, moved into the *nested*
namespace `Work.OROneRel.WBClean` (so that inside it every unqualified name still resolves through
the parent namespace to the untouched `Work.OROneRel` development).  The reason is *import hygiene*:
the original reaches `Submission.Work.OROneRel.mrslAux`, which redeclares the public theorem
`Work.OROneRel.toWord_pow_of_isCyclicallyReduced` already declared by
`Submission.Work.OROneRel.magnus_step_root` — a dependency of
`Submission.Work.ORLyndon.epsNeZeroDescent` — so no module can import both cones.  Here the
duplicated theorem is renamed `Work.OROneRel.WBClean.toWord_pow_of_isCyclicallyReduced_wbc` and the
imports inside the copied chain are redirected; nothing else is changed.

Consumer: `Submission/Work/ORLyndon/occTerm_distinct_clean.lean`.  Everything in
`Submission/Work/ORLyndon/WBClean/` (and that file) can be deleted as soon as the duplicate
declaration is removed on the `OROneRel` side.
-/
/-!
# Weinbaum's theorem

`Work.OROneRel.WBClean.weinbaum_at` is the unconditional form of Weinbaum's theorem (1972): for a cyclically
reduced relator `r` which is not a proper power, no nontrivial subword `v` of a power of `r` with
`relatorNorm v < relatorNorm r` is trivial in the one-relator group `⟨α | r⟩`.

The definitions and the general reductions live in `Submission.Work.OROneRel.weinbaumDefs`; the two
cases of the final case split are

* `Work.OROneRel.WBClean.weinbaumAt_of_expSum_eq_zero` (some generator occurring in `r` has exponent sum
  zero -- the Magnus/Moldavanskii case);
* `Work.OROneRel.WBClean.weinbaumAt_of_expSum_ne_zero` (every generator occurring in `r` has nonzero
  exponent sum -- the abelianisation/`Freiheitssatz`/padding case),

and the assembly `Work.OROneRel.weinbaum_at_of_cases` (also in `weinbaumDefs`) combines them.
-/

namespace Work.OROneRel

namespace WBClean

universe u

theorem weinbaum_at {α : Type u} (r : FreeGroup α) :
    Work.OROneRel.WeinbaumAt r :=
  weinbaum_at_of_cases
    (fun {β : Type u} (r : FreeGroup β) {a : β} ha h => weinbaumAt_of_expSum_eq_zero r ha h)
    (fun {β : Type u} (r : FreeGroup β) h => weinbaumAt_of_expSum_ne_zero r h)
    r

end WBClean

end Work.OROneRel
