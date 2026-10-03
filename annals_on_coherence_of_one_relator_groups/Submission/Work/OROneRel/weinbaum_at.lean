import Mathlib
import Submission.Work.OROneRel.Interface
import Submission.Work.OROneRel.weinbaumDefs
import Submission.Work.OROneRel.weinbaumAt_of_expSum_eq_zero
import Submission.Work.OROneRel.weinbaumAt_of_expSum_ne_zero

/-!
# Weinbaum's theorem

`Work.OROneRel.weinbaum_at` is the unconditional form of Weinbaum's theorem (1972): for a cyclically
reduced relator `r` which is not a proper power, no nontrivial subword `v` of a power of `r` with
`relatorNorm v < relatorNorm r` is trivial in the one-relator group `⟨α | r⟩`.

The definitions and the general reductions live in `Submission.Work.OROneRel.weinbaumDefs`; the two
cases of the final case split are

* `Work.OROneRel.weinbaumAt_of_expSum_eq_zero` (some generator occurring in `r` has exponent sum
  zero -- the Magnus/Moldavanskii case);
* `Work.OROneRel.weinbaumAt_of_expSum_ne_zero` (every generator occurring in `r` has nonzero
  exponent sum -- the abelianisation/`Freiheitssatz`/padding case),

and the assembly `Work.OROneRel.weinbaum_at_of_cases` (also in `weinbaumDefs`) combines them.
-/

namespace Work.OROneRel

universe u

theorem weinbaum_at {α : Type u} (r : FreeGroup α) :
    Work.OROneRel.WeinbaumAt r :=
  weinbaum_at_of_cases
    (fun {β : Type u} (r : FreeGroup β) {a : β} ha h => weinbaumAt_of_expSum_eq_zero r ha h)
    (fun {β : Type u} (r : FreeGroup β) h => weinbaumAt_of_expSum_ne_zero r h)
    r

end Work.OROneRel
