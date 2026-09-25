import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Audit.PadicInstance
import Submission.NK.LocalReciprocityLubinTate.Audit.residueCard_padic

/-!
# `p` is an irreducible element of the ring of integers of `ℚ_[p]`

The ring of integers `𝒪[ℚ_[p]] = {x : ℚ_[p] | valuation x ≤ 1}` of the `p`-adic field is the unit
ball `ℤ_[p]`, and `p` is a uniformizer there: a generator of the maximal ideal, hence prime, hence
irreducible (`PadicInt.irreducible_p`).  The identification with the unit ball is
`padicIntegerEquiv`, which is a ring isomorphism whose underlying map is the identity; it carries
`(p : ℤ_[p])` to the element of `𝒪[ℚ_[p]]` whose underlying `p`-adic number is `p`.
-/

open scoped ValuativeRel

namespace NK.LocalReciprocityLubinTate.Audit

/-- **There is an irreducible element of the ring of integers of `ℚ_[p]` equal to `p`.**

Concretely `p` itself: transported along the ring isomorphism `padicIntegerEquiv` identifying the
ring of integers of `ℚ_[p]` with the unit ball `ℤ_[p]`, where `p` generates the maximal ideal and so
is irreducible. -/
theorem exists_irreducible_padic (p : ℕ) [Fact p.Prime] :
    ∃ π : ↥(ValuativeRel.valuation ℚ_[p]).integer, Irreducible π ∧ (π : ℚ_[p]) = (p : ℚ_[p]) := by
  refine ⟨(padicIntegerEquiv p).symm (p : ℤ_[p]), ?_, ?_⟩
  · rw [MulEquiv.irreducible_iff]
    exact PadicInt.irreducible_p
  · rw [show (((padicIntegerEquiv p).symm (p : ℤ_[p])) : ℚ_[p]) = ((p : ℤ_[p]) : ℚ_[p]) from rfl,
      PadicInt.coe_natCast]

end NK.LocalReciprocityLubinTate.Audit
