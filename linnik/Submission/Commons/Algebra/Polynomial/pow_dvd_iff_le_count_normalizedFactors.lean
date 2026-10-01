import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.Algebra.Polynomial

/-- For a monic irreducible polynomial `P` over a field and a monic polynomial `p`, the power
`P ^ e` divides `p` iff `e` is at most the multiplicity of `P` in the normalized factorisation
of `p`. -/
theorem pow_dvd_iff_le_count_normalizedFactors {F : Type*} [Field F] [DecidableEq F]
    {P p : Polynomial F} (hP : P.Monic) (hPi : Irreducible P) (hp : p.Monic) (e : ℕ) :
    P ^ e ∣ p ↔ e ≤ (UniqueFactorizationMonoid.normalizedFactors p).count P := by
  rw [pow_dvd_iff_le_emultiplicity,
    UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hPi hp.ne_zero,
    hP.normalize_eq_self]
  exact Nat.cast_le

end Commons.Algebra.Polynomial