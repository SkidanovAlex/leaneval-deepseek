import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.CharP.Lemmas

/-!
# Frobenius exponents

Mathlib's `ExpChar R p` (the *exponential characteristic*) only makes sense for `p` a prime:
its only constructors are `ExpChar.zero` (`p = 1`, characteristic zero) and `ExpChar.prime`
(`p` prime, `CharP R p`).  Many constructions of this project, however, need the `q`-th power
Frobenius for `q = p ^ f` (`p = ringChar R`): the base field `F = F_q` of the positive
characteristic MZV theory has `q = |F| = p ^ f`, and the Frobenius twist `x ↦ x ^ q` is the
`f`-fold iterate of the true Frobenius.

This file isolates the exact property of `q` that the twist construction uses: the additivity
of the `q`-th power map.  `FrobPow R q` records it (together with `q ≠ 0`, needed for `0 ^ q = 0`);
it holds for every power of the characteristic (`FrobPow.pow`, `FrobPow.of_charP`) and it is
equivalent to Mathlib's `ExpChar` in the prime case (`FrobPow.ofExpChar`).

## Main results

* `FrobPow` — the class; `FrobPow.ne_zero`, `FrobPow.add_pow` its fields.
* `FrobPow.ofExpChar` — `ExpChar R p` gives `FrobPow R p`.
* ★ `FrobPow.pow` — `FrobPow R q` gives `FrobPow R (q ^ n)`.
* `FrobPow.of_charP` — `CharP R p`, `p` prime, gives `FrobPow R (p ^ f)`.
* `FrobPow.sum_pow`, `FrobPow.sum_pow_finset`.
-/

set_option autoImplicit false

/-- `q` is a *Frobenius exponent* for the commutative semiring `R`: `q ≠ 0` and the `q`-th power
map is additive.  For `R` of positive characteristic `p` this holds for every power of `p`. -/
class FrobPow (R : Type*) [CommSemiring R] (q : ℕ) : Prop where
  /-- `q` is nonzero, so that `0 ^ q = 0`. -/
  ne_zero : q ≠ 0
  /-- The `q`-th power map is additive. -/
  add_pow : ∀ x y : R, (x + y) ^ q = x ^ q + y ^ q

namespace FrobPow

variable {R : Type*} [CommSemiring R]

/-- The classical Frobenius: `ExpChar R p` gives the Frobenius exponent `p`. -/
instance ofExpChar {p : ℕ} [ExpChar R p] : FrobPow R p where
  ne_zero := (expChar_pos R p).ne'
  add_pow := fun x y => by simpa using add_pow_expChar_pow x y p 1

lemma add_pow' {q : ℕ} [FrobPow R q] (x y : R) : (x + y) ^ q = x ^ q + y ^ q :=
  FrobPow.add_pow x y

/-- **Powers of a Frobenius exponent are Frobenius exponents.** -/
lemma pow {q : ℕ} [FrobPow R q] (n : ℕ) : FrobPow R (q ^ n) where
  ne_zero := pow_ne_zero n (FrobPow.ne_zero R (q := q))
  add_pow := by
    intro x y
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ]
        conv_lhs => rw [pow_mul]
        rw [ih, FrobPow.add_pow, pow_mul, pow_mul]

/-- A finite sum of `q ^ n`-th powers. -/
lemma sum_pow {q : ℕ} [FrobPow R q] {ι : Type*} (s : Finset ι) (f : ι → R) (n : ℕ) :
    (∑ i ∈ s, f i) ^ (q ^ n) = ∑ i ∈ s, (f i) ^ (q ^ n) := by
  classical
  haveI := FrobPow.pow (R := R) (q := q) n
  induction s using Finset.induction with
  | empty => exact zero_pow (pow_ne_zero n (FrobPow.ne_zero R (q := q)))
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, FrobPow.add_pow, ih]

/-- A finite sum of `q`-th powers. -/
lemma sum_pow_finset {q : ℕ} [FrobPow R q] {ι : Type*} (s : Finset ι) (f : ι → R) :
    (∑ i ∈ s, f i) ^ q = ∑ i ∈ s, (f i) ^ q := by
  classical
  induction s using Finset.induction with
  | empty => exact zero_pow (FrobPow.ne_zero R (q := q))
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, FrobPow.add_pow, ih]

/-- `CharP R p` with `p` prime gives the Frobenius exponent `p ^ f`. -/
lemma of_charP {p : ℕ} [Fact p.Prime] [CharP R p] (f : ℕ) : FrobPow R (p ^ f) := by
  have : ExpChar R p := expChar_prime R p
  exact FrobPow.ofExpChar.pow f

end FrobPow
