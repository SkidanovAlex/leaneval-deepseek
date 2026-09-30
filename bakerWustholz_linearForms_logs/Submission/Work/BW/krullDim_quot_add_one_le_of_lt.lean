import Mathlib
import Submission.Work.BW.DefsMult

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

namespace Work.BW

/-- Krull dimension drops by at least one when passing to a strictly larger ideal: if `p < q`
are ideals of a commutative ring and `p` is prime, then `dim (A ⧸ q) + 1 ≤ dim (A ⧸ p)`.

(State it in `namespace Work.BW`; only `Mathlib` is needed.)

Proof sketch: choose `x ∈ q \ p`, so that `x̄ = Ideal.Quotient.mk p x ≠ 0` is a nonzerodivisor on
the domain `A ⧸ p`. The quotient map `f = Ideal.Quotient.factor (le_of_lt h) : A ⧸ p →+* A ⧸ q`
is surjective and kills `x̄`, so
`ringKrullDim_succ_le_of_surjective f hf hx̄ hfx̄ : ringKrullDim (A ⧸ q) + 1 ≤ ringKrullDim (A ⧸ p)`
applies (that is the Krull dimension version of `dim R/r + 1 ≤ dim R` for a nonzerodivisor),
giving exactly the claim. -/
theorem krullDim_quot_add_one_le_of_lt {A : Type*} [CommRing A] {p q : Ideal A}
    (hp : p.IsPrime) (h : p < q) :
    ringKrullDim (A ⧸ q) + 1 ≤ ringKrullDim (A ⧸ p) := by
  -- `A ⧸ p` is a domain, so nonzero elements are nonzerodivisors
  haveI : p.IsPrime := hp
  -- pick `x ∈ q` with `x ∉ p`
  obtain ⟨x, hxq, hxp⟩ := SetLike.exists_of_lt h
  -- the quotient map `A ⧸ p →+* A ⧸ q` is surjective and kills `x̄ = mk p x`
  refine ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor (le_of_lt h))
    (Ideal.Quotient.factor_surjective _) (r := Ideal.Quotient.mk p x) ?_ ?_
  · -- `x̄ ≠ 0` in the domain `A ⧸ p`, hence a nonzerodivisor
    rw [mem_nonZeroDivisors_iff_ne_zero]
    exact fun hx0 => hxp (Ideal.Quotient.eq_zero_iff_mem.mp hx0)
  · -- `x ∈ q` means `f x̄ = 0`
    rw [Ideal.Quotient.factor_mk]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hxq

end Work.BW
