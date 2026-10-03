import Mathlib
import Submission.Work.ORDivLoc.Basic
import Submission.Work.ORDivLoc.Vocabulary
import Submission.Work.ORDivLoc.Closure.isEpic_starClosureCod
import Submission.Work.ORDivLoc.Closure.star_toUK_complex

namespace Work.ORDivLoc.Closure

/-- **The epic criterion at the `∗`-regular closure, for the complex coefficients.**

For the complex envelope `U(G)` and the coefficient embedding `RingHom.id ℂ`, the structure map
`starClosureCod E (RingHom.id ℂ) H : ℂ[H] →+* V` into the `∗`-regular closure `V` of its image is
epic.

This is the specialisation of `isEpic_starClosureCod_of_star_mem` to `K = ℂ`, `φK = RingHom.id ℂ`:
the hypothesis needed there — the star of every element of the image of `toUK E (RingHom.id ℂ) H`
is a ring expression in that image — is supplied by `star_toUK_complex`, which says that
`toUK E (RingHom.id ℂ) H` is a `∗`-homomorphism, so `star (toUK x) = toUK (star x)` lies in the
image itself. -/
theorem isEpic_starClosureCod_complex {G : Type} [Group G]
    (E : Work.ORVonNeumann.StarRegularEnvelope G) (H : Subgroup G) :
    Work.ORHughesFree.IsEpic (Work.ORDivLoc.starClosureCod E (RingHom.id ℂ) H) :=
  isEpic_starClosureCod_of_star_mem E (RingHom.id ℂ) H (fun x => by
    rw [star_toUK_complex]
    exact Subring.subset_closure ⟨star x, rfl⟩)

end Work.ORDivLoc.Closure
