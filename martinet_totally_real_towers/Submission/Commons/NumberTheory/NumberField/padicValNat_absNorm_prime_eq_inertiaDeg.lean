import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.Algebra.CharZero.Infinite

open scoped NumberField

namespace Commons.NumberTheory.NumberField

theorem padicValNat_absNorm_prime_eq_inertiaDeg
    {K : Type*} [Field K] [NumberField K] {p : ℕ} [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    padicValNat p P.absNorm = P.inertiaDeg ℤ := by
  rw [← Ideal.pow_inertiaDeg (R := 𝓞 K) p P]
  exact padicValNat.prime_pow (P.inertiaDeg ℤ)

end Commons.NumberTheory.NumberField