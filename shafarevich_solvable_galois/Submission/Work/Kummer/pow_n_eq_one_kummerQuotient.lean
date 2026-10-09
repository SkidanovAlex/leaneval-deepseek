import Mathlib
import Submission.Work.Kummer.Pairing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v

namespace Work.Kummer

/-- The Kummer quotient `(Kˣ ∩ (Lˣ)^n)/(Kˣ)^n` has exponent dividing `n`: the class of any
`a ∈ Kˣ ∩ (Lˣ)^n` raised to the `n`-th power is trivial, because `a ^ n` is itself an `n`-th
power of an element of `Kˣ`. -/
theorem pow_n_eq_one_kummerQuotient {K : Type u} {L : Type v} [Field K]
    [Field L] [Algebra K L] {n : ℕ} (q : kummerQuotient n K L) : q ^ n = 1 := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective
    ((nthPowerSubgroup n Kˣ).subgroupOf (kummerSubgroup n K L)) q
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact ⟨(a : Kˣ), rfl⟩

end Work.Kummer
