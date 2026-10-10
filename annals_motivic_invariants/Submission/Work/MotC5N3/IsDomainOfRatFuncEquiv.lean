import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotC5N3.IsDomainOfRatFuncEquiv`

A residue-field trick: if the fraction ring of the polynomial ring over `A` is `K`-isomorphic to
`RatFunc T` for a field `T`, then `A` is a domain.

This is the "cheap" route to the irreducibility of the AS residual quotient
`A = K[x₀,x₁,x₂] ⧸ √(ZIAS a b g)`: the K6 node `Work.MotC5N3.ASZTwistDiv2` provides the
`K`-algebra isomorphism `FractionRing (Polynomial A) ≅ RatFunc ↥(twistFieldAS D (2 • g))` with the
right-hand side a field, and the two `algebraMap`s `A → A[X] → FractionRing (A[X])` are injective
(`IsFractionRing.injective` for any commutative ring, since the localisation is at the
non-zero-divisors: `s * C a = 0` with `s` a non-zero-divisor forces `C a = 0`).  Hence `A` embeds
into a field and is a domain.
-/

set_option autoImplicit false

namespace Work.MotC5N3

/-- **A commutative ring embedding into a field is a domain.** -/
theorem isDomain_of_injective_into_field {A F : Type*} [CommRing A] [Field F] (f : A →+* F)
    (hf : Function.Injective f) : IsDomain A := by
  have h01 : (0 : A) ≠ 1 := fun h => zero_ne_one (α := F) (by simpa using congrArg f h)
  haveI : Nontrivial A := ⟨0, 1, h01⟩
  haveI : NoZeroDivisors A := by
    refine ⟨fun {a b} hab => ?_⟩
    have hmap : f a * f b = 0 := by rw [← map_mul, hab, map_zero]
    rcases mul_eq_zero.mp hmap with h | h
    · exact Or.inl (hf (by rw [h, map_zero]))
    · exact Or.inr (hf (by rw [h, map_zero]))
  exact IsDomain.mk

/-- **`IsDomain A` from `FractionRing (Polynomial A) ≅ RatFunc T`** (`T` a field). -/
theorem isDomain_of_algEquiv_ratFunc {K : Type*} [Field K] {A : Type*} [CommRing A] [Algebra K A]
    {T : Type*} [Field T] [Algebra K T] (e : FractionRing (Polynomial A) ≃ₐ[K] RatFunc T) :
    IsDomain A := by
  refine isDomain_of_injective_into_field
    ((e : FractionRing (Polynomial A) →+* RatFunc T).comp
      ((algebraMap (Polynomial A) (FractionRing (Polynomial A))).comp Polynomial.C)) ?_
  intro a b hab
  have h1 : (algebraMap (Polynomial A) (FractionRing (Polynomial A))) (Polynomial.C a)
      = (algebraMap (Polynomial A) (FractionRing (Polynomial A))) (Polynomial.C b) :=
    e.injective hab
  exact Polynomial.C_injective
    (IsFractionRing.injective (Polynomial A) (FractionRing (Polynomial A)) h1)

end Work.MotC5N3
