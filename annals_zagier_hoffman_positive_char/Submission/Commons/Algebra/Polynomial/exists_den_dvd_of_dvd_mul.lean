import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.Algebra.Polynomial

/-- **Denominator extraction, retained factor form**: if `a ∣ b * c` then there is a **divisor `d` of
`a`** which clears `b` out of `a` and which is caught by `c`.

Precisely: `∃ d, d ∣ a ∧ a ∣ d * b ∧ d ∣ c`.  The witness is `d := a / gcd a b` (equivalently, any
`d` with `a = gcd a b * d`), and then
* `d ∣ a` is immediate (by construction),
* `a ∣ d * b`, since `d * b = a * (b / gcd a b)` (using `gcd a b ∣ b`), and
* `d ∣ c`, from `a ∣ b * c` ⟹ `d ∣ (b / gcd a b) * c` together with `IsCoprime d (b / gcd a b)`
  (`gcd (g*d) (g*e) = normalize g * gcd d e` shows `gcd d e` is a unit; Bézout via
  `EuclideanDomain.gcd_eq_gcd_ab` gives `IsCoprime d e`; then `IsCoprime.dvd_of_dvd_mul_left`).

⚠ Note `d ∣ a` is *not* implied by the weaker conclusion `∃ d, a ∣ d * b ∧ d ∣ c` (the witness above
satisfies all three, but a general witness of the weaker statement need not divide `a`).  This is the
form needed by a "potential denominator" argument: `d` is the part of `a` not already shared with `b`.
If `/` is awkward, carry `d` explicitly instead:
`a = gcd a b * d → a ∣ b * c → d ∣ a ∧ a ∣ d * b ∧ d ∣ c`. -/
theorem exists_den_dvd_of_dvd_mul {K : Type*} [Field K] {a b c : Polynomial K} (h : a ∣ b * c) :
    ∃ d : Polynomial K, d ∣ a ∧ a ∣ d * b ∧ d ∣ c := by
  -- `Polynomial K` is a `DecompositionMonoid` (it is a UFD / gcd domain), so any divisor of a
  -- product splits: `a = a₁ * a₂` with `a₁ ∣ b` and `a₂ ∣ c`.
  obtain ⟨a₁, a₂, ha₁, ha₂, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul h
  refine ⟨a₂, ⟨a₁, by ring⟩, ?_, ha₂⟩
  -- `a₁ ∣ b` gives `a₁ * a₂ ∣ a₂ * b`.
  obtain ⟨k, rfl⟩ := ha₁
  exact ⟨k, by ring⟩

end Commons.Algebra.Polynomial