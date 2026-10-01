import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.FieldTheory.FiniteField

/-- For a finite field `K` and `n ≥ 1` with `n ∣ |K| - 1`, the quotient of `Kˣ` by the subgroup
of `n`-th powers has exactly `n` elements. -/
theorem units_quotient_pow_card (K : Type*) [Field K] [Fintype K] (n : ℕ) [NeZero n]
    (h : n ∣ Fintype.card K - 1) :
    Nat.card (Kˣ ⧸ (powMonoidHom n).range) = n := by
  rw [← Subgroup.index_eq_card]
  rw [IsCyclic.index_powMonoidHom_range]
  rw [Nat.card_units, Nat.card_eq_fintype_card]
  exact Nat.gcd_eq_right h

end Commons.FieldTheory.FiniteField