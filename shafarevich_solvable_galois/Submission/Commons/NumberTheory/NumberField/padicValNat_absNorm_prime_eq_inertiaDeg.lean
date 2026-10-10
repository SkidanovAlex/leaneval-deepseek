import Mathlib.Algebra.CharZero.Infinite
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.Padics.PadicVal.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField

namespace Commons.NumberTheory.NumberField

theorem padicValNat_absNorm_prime_eq_inertiaDeg
    {K : Type*} [Field K] [NumberField K] {p : ℕ} [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    padicValNat p P.absNorm = P.inertiaDeg ℤ := by
  rw [← Ideal.pow_inertiaDeg (R := 𝓞 K) p P]
  exact padicValNat.prime_pow (P.inertiaDeg ℤ)

end Commons.NumberTheory.NumberField