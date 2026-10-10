import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.RamificationInertia.Inertia
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.NumberField

/-- In a number field `K`, a prime ideal `P` of the ring of integers lying over the
rational prime `p` has residue field of cardinality `p ^ f`, where `f = P.inertiaDeg ℤ`
is the inertia degree of `P` over `p`. -/
theorem natCard_quotient_eq_pow_inertiaDeg {K : Type*} [Field K] [NumberField K] (p : ℕ)
    [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    (hP : P ∈ IsDedekindDomain.primesOverFinset (Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 K)) :
    Nat.card ((𝓞 K) ⧸ P) = p ^ P.inertiaDeg ℤ := by
  classical
  let pZ : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  have hp : Nat.Prime p := (inferInstance : Fact (Nat.Prime p)).out
  have hp0 : pZ ≠ ⊥ := by
    dsimp [pZ]
    rw [Ideal.span_singleton_eq_bot]
    exact_mod_cast (Nat.Prime.ne_zero hp)
  have hP' : P ∈ pZ.primesOver (𝓞 K) :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 K)).mp hP
  letI : P.IsPrime := hP'.1
  letI : P.LiesOver pZ := hP'.2
  rw [Ideal.pow_inertiaDeg (R := 𝓞 K) p P]
  rw [Ideal.absNorm_apply]
  rfl

end Commons.NumberTheory.NumberField