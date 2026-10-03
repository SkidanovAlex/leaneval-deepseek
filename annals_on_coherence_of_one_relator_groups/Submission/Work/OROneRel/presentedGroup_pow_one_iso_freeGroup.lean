import Mathlib
import Submission.Work.OROneRel.letter_once_iso_freeGroup

/-!
# `⟨β | x⟩ ≃* F(β \ {x})`

The one-relator group presented by the single relation `x ^ 1 = 1` (i.e. the word `of x`) is the
free group on the remaining generators `β \ {x}`.

Maths: writing the relator as the one-letter word `FreeGroup.mk [(x, true)]`, this is the
"generator occurring once" case of the Freiheitssatz, which is instantiated from the general
length-one case `Work.OROneRel.letter_once_iso_freeGroup` with the two outer words empty
(`L₁ = L₂ = []`, `e = true`).  The remaining content is the bookkeeping that
`FreeGroup.mk [(x, true)] = FreeGroup.of x ^ (1 : ℕ)`, so that the singleton presentation
`{of x ^ 1}` is (up to the canonical isomorphism of presentations by equal relator sets) the
one presented by `{FreeGroup.mk [(x, true)]}`.
-/

namespace Work.OROneRel

/-- The presentation by the relator `of x ^ 1` is the presentation by the one-letter word
`mk [(x, true)]`: after `pow_one` the two relators are `of x` and `mk [(x, true)]`, which are
definitionally equal (`mk` on a one-letter word *is* `of`). -/
theorem singleton_pow_one_eq_singleton_of {β : Type*} (x : β) :
    ({FreeGroup.mk [(x, true)]} : Set (FreeGroup β)) =
      ({FreeGroup.of x ^ (1 : ℕ)} : Set (FreeGroup β)) := by
  rw [pow_one]
  rfl

/-- `⟨β | x ^ 1⟩ ≃* F(β \ {x})`: killing the single generator `x` leaves the free group on the
remaining generators. -/
theorem presentedGroup_pow_one_iso_freeGroup {β : Type*} (x : β) :
    Nonempty (PresentedGroup ({FreeGroup.of x ^ (1 : ℕ)} : Set (FreeGroup β)) ≃*
      FreeGroup {a : β // a ≠ x}) := by
  -- The length-one relator `mk [(x, true)]` is a generator occurring exactly once.
  obtain ⟨e⟩ := letter_once_iso_freeGroup (α := β) x true
    ([] : List (β × Bool)) ([] : List (β × Bool))
    (by intro p hp; exact absurd hp (by simp))
  -- Transport the presentation along `{mk [(x, true)]} = {of x ^ 1}`.
  exact ⟨(QuotientGroup.quotientMulEquivOfEq
    (congrArg Subgroup.normalClosure (singleton_pow_one_eq_singleton_of x))).trans e⟩

end Work.OROneRel
