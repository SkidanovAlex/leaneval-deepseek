import Mathlib

/-!
# Additivity of the Frobenius map in `Localization.Away f` in characteristic `p`

Let `R` be a commutative ring of prime characteristic `p` and `f : R`.  The localization
`Localization.Away f` need not have characteristic `p` (it may even be the zero ring when
`f` is nilpotent), but it always satisfies `(p : S) = 0`: its prime subring is a quotient
of `𝔽_p`.  That single fact is enough for the Frobenius map `x ↦ x ^ p` to be additive,
hence to distribute over finite sums.
-/

namespace Work.DSM5b

/-- In a commutative semiring in which `p = 0` for a prime `p`, the Frobenius map
`x ↦ x ^ p` is additive. -/
lemma add_pow_prime_of_natCast_eq_zero {S : Type*} [CommSemiring S] {p : ℕ} (hp : p.Prime)
    (h : (p : S) = 0) (x y : S) : (x + y) ^ p = x ^ p + y ^ p := by
  rw [add_pow_prime_eq hp x y]
  simp [h]

/-- The Frobenius ring endomorphism `x ↦ x ^ p` of a commutative semiring in which
`p = 0` for a prime `p`. -/
noncomputable def frobeniusOfNatCastEqZero (S : Type*) [CommSemiring S] (p : ℕ) (hp : p.Prime)
    (h : (p : S) = 0) : S →+* S where
  toFun x := x ^ p
  map_one' := one_pow p
  map_mul' x y := mul_pow x y p
  map_zero' := zero_pow hp.pos.ne'
  map_add' := add_pow_prime_of_natCast_eq_zero hp h

/-- The Frobenius map distributes over finite sums in a commutative semiring in which
`p = 0` for a prime `p`. -/
lemma sum_pow_prime_of_natCast_eq_zero {S : Type*} [CommSemiring S] {p : ℕ} (hp : p.Prime)
    (h : (p : S) = 0) {ι : Type*} (s : Finset ι) (f : ι → S) :
    (∑ i ∈ s, f i) ^ p = ∑ i ∈ s, f i ^ p :=
  map_sum (frobeniusOfNatCastEqZero S p hp h) f s

/-- In the localization away from `f` of a ring of characteristic `p`, the integer `p`
is zero. -/
lemma natCast_eq_zero_away {R : Type*} [CommRing R] {p : ℕ} [CharP R p] (f : R) :
    (p : Localization.Away f) = 0 := by
  rw [← map_natCast (algebraMap R (Localization.Away f)) p, CharP.cast_eq_zero R p, map_zero]

theorem sum_pow_p_away (p : ℕ) [Fact p.Prime] {R : Type*} [CommRing R] [CharP R p] (f : R)
    {α : Type*} (s : Finset α) (u : α → Localization.Away f) :
    (∑ i ∈ s, u i) ^ p = ∑ i ∈ s, (u i) ^ p :=
  sum_pow_prime_of_natCast_eq_zero Fact.out (natCast_eq_zero_away f) s u

end Work.DSM5b
