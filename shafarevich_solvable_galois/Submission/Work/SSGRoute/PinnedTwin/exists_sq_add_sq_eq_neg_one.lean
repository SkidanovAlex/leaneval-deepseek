import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PinnedTwin

/-- Over a finite field, every element -- in particular `-1` -- is a sum of two squares.

This is the classical finite-field fact underlying the "two-squares" pigeonhole argument:
the set of squares and its translate by `-1` must intersect because each has more than half
the elements.  It is a direct consequence of `CharP.sq_add_sq`, which in turn is Mathlib's
`ZMod.sq_add_sq` (the Cauchy–Davenport / Chevalley–Warning style input).

The hypothesis `h2 : ringChar κ ≠ 2` is retained for compatibility with the interface the
requesting development expects; the statement in fact holds for every finite field. -/
theorem exists_sq_add_sq_eq_neg_one {κ : Type} [Field κ] [Fintype κ] (h2 : ringChar κ ≠ 2) :
    ∃ u v : κ, u ^ 2 + v ^ 2 = -1 := by
  haveI : NeZero (ringChar κ) := ⟨CharP.ringChar_ne_zero_of_finite κ⟩
  haveI : CharP κ (ringChar κ) := ⟨ringChar.spec κ⟩
  obtain ⟨a, b, hab⟩ := CharP.sq_add_sq κ (ringChar κ) (-1)
  exact ⟨a, b, by simpa using hab⟩

end Work.SSGRoute.PinnedTwin
