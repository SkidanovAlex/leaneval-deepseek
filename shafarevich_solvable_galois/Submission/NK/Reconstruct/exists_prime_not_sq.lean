import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NK.Reconstruct.quadraticAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A prime which is not a square in a number field

For `A` a finite-dimensional intermediate field `ℚ ⊆ A ⊆ Ω`, we produce a prime `p` having no
square root in `A`.  Equivalently, only finitely many rational primes are squares inside a number
field: square roots of two distinct primes generate the two *distinct* quadratic subfields
`ℚ(√p) ≠ ℚ(√q)`, while a finite extension of `ℚ` has only finitely many intermediate fields
(primitive element theorem).

This is the auxiliary input used by `NK.Reconstruct.exists_aux_imaginary`.
-/

set_option autoImplicit false

namespace NK.Reconstruct

/-- **Distinct primes have distinct square-root fields.**

If `x ^ 2 = p` and `y ^ 2 = q` for primes `p ≠ q`, then `ℚ⟮x⟯ ≠ ℚ⟮y⟯`.  The proof inspects an
element of the quadratic field `ℚ⟮y⟯`: writing `x = a + b * y`, the square `x ^ 2 = p` lies in `ℚ`,
so (by `eq_zero_or_eq_zero_of_sq_mem`) either `a = 0` or `b = 0`, and each alternative would make
`p` or `p * q` a square in `ℚ`, contradicting primality. -/
theorem prime_eq_of_adjoin_sq_eq {A : Type*} [Field A] [Algebra ℚ A]
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) {x y : A}
    (hx : x ^ 2 = (p : A)) (hy : y ^ 2 = (q : A))
    (heq : (IntermediateField.adjoin ℚ ({x} : Set A)) =
      (IntermediateField.adjoin ℚ ({y} : Set A))) :
    p = q := by
  by_contra hpq
  -- `y` is not rational, as `q` is not a square in `ℚ`.
  have hy' : y ^ 2 = algebraMap ℚ A (q : ℚ) := by rw [hy, map_natCast]
  have hy_not : ∀ c : ℚ, algebraMap ℚ A c ≠ y := by
    intro c hc
    have hcq : (q : ℚ) = c ^ 2 := by
      apply (algebraMap ℚ A).injective
      rw [map_pow]
      rw [← hy', ← hc]
    exact not_isSquare_natCast_of_prime hq ⟨c, by rw [hcq]; ring⟩
  -- `x` lies in `ℚ⟮y⟯`, hence `x = a + b * y`.
  have hxmem : x ∈ (IntermediateField.adjoin ℚ ({y} : Set A)) := by
    rw [← heq]
    exact IntermediateField.mem_adjoin_simple_self ℚ x
  have hset := adjoin_sq_eq_set (F := ℚ) (K := A) hy' hy_not
  have hxmem' : x ∈ ({z : A | ∃ a b : ℚ,
      z = algebraMap ℚ A a + algebraMap ℚ A b * y} : Set A) := by
    rw [← hset]; exact hxmem
  obtain ⟨a, b, hab⟩ := hxmem'
  -- whose square is rational
  have hsq : ∃ c : ℚ, (algebraMap ℚ A a + algebraMap ℚ A b * y) ^ 2 = algebraMap ℚ A c :=
    ⟨(p : ℚ), by rw [← hab, hx, map_natCast]⟩
  rcases eq_zero_or_eq_zero_of_sq_mem (F := ℚ) (K := A) (d := (q : ℚ)) (w := y) hy' hy_not hsq
    with ha | hb
  · -- `x = b * y`: then `p * q = (b * q) ^ 2` is a square in `ℚ`.
    rw [ha] at hab
    simp only [map_zero, zero_add] at hab
    have hkey : (p : ℚ) = b ^ 2 * (q : ℚ) := by
      apply (algebraMap ℚ A).injective
      simp only [map_mul, map_pow, map_natCast]
      rw [← hx, hab, mul_pow, hy]
    refine not_isSquare_natCast_mul_prime hp hq hpq ⟨b * (q : ℚ), ?_⟩
    push_cast
    rw [hkey]
    ring
  · -- `x = a`: then `p = a ^ 2` is a square in `ℚ`.
    rw [hb] at hab
    simp only [map_zero, zero_mul, add_zero] at hab
    have hkey : (p : ℚ) = a ^ 2 := by
      apply (algebraMap ℚ A).injective
      simp only [map_pow, map_natCast]
      rw [← hx, hab]
    exact not_isSquare_natCast_of_prime hp ⟨a, by rw [hkey]; ring⟩

/-- **Some prime is not a square in `A`.**  A finite extension of `ℚ` has only finitely many
intermediate fields, but distinct primes give distinct square-root fields in `A`; since there are
infinitely many primes, one of them has no square root in `A`. -/
theorem exists_prime_not_sq {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (A : IntermediateField ℚ Ω) [FiniteDimensional ℚ ↥A] :
    ∃ p : ℕ, p.Prime ∧ ¬ ∃ x : ↥A, x ^ 2 = (p : ↥A) := by
  -- Suppose every prime were a square in `A`.
  by_contra hcon
  push Not at hcon
  -- `A / ℚ` is finite separable: it has only finitely many intermediate fields.
  have hfin : Finite (IntermediateField ℚ ↥A) :=
    Field.finite_intermediateField_of_exists_primitive_element ℚ ↥A
      (Field.exists_primitive_element ℚ ↥A)
  -- Pick a square root of every prime and send `p` to the field it generates.
  choose x hx using hcon
  let φ : {p : ℕ // p.Prime} → IntermediateField ℚ ↥A := fun p =>
    IntermediateField.adjoin ℚ ({x p.1 p.2} : Set ↥A)
  have hφ : Function.Injective φ := by
    rintro ⟨p, hp⟩ ⟨q, hq⟩ heq
    exact Subtype.ext (prime_eq_of_adjoin_sq_eq hp hq (hx p hp) (hx q hq) heq)
  -- An injection from the (infinite) primes into a finite set: impossible.
  have hinf : Infinite {p : ℕ // p.Prime} := Set.infinite_coe_iff.mpr Nat.infinite_setOfPred_prime
  exact hinf.not_finite (Finite.of_injective φ hφ)

end NK.Reconstruct
