import Mathlib
import Submission.Work.OROneRel.weinbaumDefs
import Submission.Work.OROneRel.MagnusRewrite
import Submission.Work.OROneRel.expSum_mk_eq_ofAdd_ssum

namespace Work.OROneRel

universe u

/-- The additive exponent sum `ssum` (built from `gfun`) and the exponent sum `wordEps` (built from
the explicit `if`-expression) agree: they are the same sum of the same contributions. -/
lemma ssum_eq_wordEps {α : Type u} (t : α) (L : List (α × Bool)) :
    Work.OROneRel.ssum t L = Work.OROneRel.wordEps t L := rfl

/-- **The exponent sum is the count on the reduced word.**  For a generator `z` and an element `w`
of the free group, the exponent sum of `z` in `w` (a homomorphism into `Multiplicative ℤ`) is the
additive exponent sum `wordEps z w.toWord` read off the reduced word of `w`.  This bridges
`Work.OROneRel.expSum` (`FreeGroup.lift`, used in the abelianisation criterion) with
`Work.OROneRel.eps` / `Work.OROneRel.wordEps` (used in the Magnus rewriting).  It should be a short
proof from `FreeGroup.mk_toWord` together with the corresponding identity for `FreeGroup.mk L`
(induction on the list `L`). -/
theorem expSum_ofAdd_wordEps {α : Type u} [DecidableEq α] (z : α) (w : FreeGroup α) :
    Work.OROneRel.expSum z w = Multiplicative.ofAdd (Work.OROneRel.wordEps z w.toWord) := by
  conv_lhs => rw [← FreeGroup.mk_toWord (x := w)]
  rw [Work.OROneRel.expSum_mk_eq_ofAdd_ssum, Work.OROneRel.ssum_eq_wordEps]

end Work.OROneRel
