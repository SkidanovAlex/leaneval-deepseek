import Mathlib

-- `haveI` is exactly what is wanted for the (Prop-valued) `IsReduced`/`CharP` instances below.
set_option linter.style.haveILetI false

/-!
# Injectivity of Frobenius on a localisation away from an element

Let `R` be a commutative ring of characteristic a prime `p` which is *perfect* (Frobenius
`x ↦ x ^ p` is bijective).  Then for every `f : R` the `p`-th power map is injective on the
localisation `R[1/f] = Localization.Away f`.

The mathematical content is small but the two ingredients are both worth recording:

* a perfect ring of characteristic a prime is **reduced** (`isReduced_of_charP_perfectRing`):
  if `z ^ n = 0`, then `z ^ (p ^ n) = 0` as well, i.e. `(frobenius R p)^[n] z = 0`; since
  `frobenius R p` is bijective, so is its `n`-th iterate, whence `z = 0`.
  (This is *not* derivable from `Mathlib`'s `PerfectRing` alone: Mathlib's
  `PerfectRing.ofSurjective` goes in the other direction and assumes reducedness.)
* in a **reduced** commutative ring `A` with `(p : A) = 0` for a prime `p`, the `p`-th power map
  is injective (`eq_of_pow_eq_pow_of_natCast_prime_eq_zero`): the vanishing of `p` in `A` makes
  Freshman's dream `(u + v) ^ p = u ^ p + v ^ p` hold, so `x ^ p = y ^ p` forces
  `(x - y) ^ p = 0`, and `x - y` is nilpotent.

`Localization.Away f` is reduced because `R` is (Mathlib's
`isReduced_localizationPreserves`), and `(p : R[1/f]) = 0` because it is a quotient of `R`
(this does **not** follow from a `CharP` instance: the localisation can be trivial, e.g. for
`f = 0`, and the trivial ring has no prime characteristic, so only `(p : ·) = 0` is available —
which is all the argument needs).
-/

namespace Work.DSM5b

/-- A perfect ring of characteristic a prime `p` is reduced. -/
theorem isReduced_of_charP_perfectRing (p : ℕ) [Fact p.Prime] {R : Type*} [CommRing R]
    [CharP R p] [PerfectRing R p] : IsReduced R := by
  refine ⟨fun z hz => ?_⟩
  obtain ⟨n, hn⟩ := hz
  have hpow : z ^ (p ^ n) = 0 :=
    pow_eq_zero_of_le (le_of_lt (Nat.lt_pow_self (Fact.out : p.Prime).one_lt)) hn
  have h1 : (frobenius R p)^[n] z = 0 := by rw [iterate_frobenius, hpow]
  have h2 : (frobenius R p)^[n] (0 : R) = 0 := Function.iterate_fixed (map_zero _) n
  exact (injective_frobenius R p).iterate n (h1.trans h2.symm)

/-- In a reduced commutative ring `A` in which `(p : A) = 0` for a prime `p`, the `p`-th power
map is injective.  (Only `(p : A) = 0` is assumed, not `CharP A p`: this is the form needed for
localisations, which may be trivial.) -/
theorem eq_of_pow_eq_pow_of_natCast_prime_eq_zero {A : Type*} [CommRing A] [IsReduced A]
    {p : ℕ} (hp : p.Prime) (hp0 : (p : A) = 0) {x y : A} (h : x ^ p = y ^ p) : x = y := by
  -- Freshman's dream, from `(p : A) = 0`
  have hadd : ∀ u v : A, (u + v) ^ p = u ^ p + v ^ p := by
    intro u v
    obtain ⟨c, hc⟩ := (Commute.all u v).exists_add_pow_prime_pow_eq hp 1
    rw [pow_one] at hc
    rw [hc, hp0]
    ring
  have hxy : x ^ p = (x - y) ^ p + y ^ p := by rw [← hadd (x - y) y, sub_add_cancel]
  have hz : (x - y) ^ p = 0 := by
    refine add_right_cancel (a := (x - y) ^ p) (b := y ^ p) (c := 0) ?_
    simpa using hxy.symm.trans h
  exact sub_eq_zero.mp (IsReduced.eq_zero (x - y) ⟨p, hz⟩)

theorem frobenius_injective_away (p : ℕ) [Fact p.Prime] {R : Type*} [CommRing R] [CharP R p]
    [PerfectRing R p] (f : R) {x y : Localization.Away f} (h : x ^ p = y ^ p) : x = y := by
  haveI : IsReduced R := isReduced_of_charP_perfectRing p
  haveI : IsReduced (Localization.Away f) := inferInstance
  have hp : p.Prime := Fact.out
  have hpR : (p : R) = 0 := CharP.cast_eq_zero R p
  have hp0 : (p : Localization.Away f) = 0 := by
    rw [← map_natCast (algebraMap R (Localization.Away f)) p, hpR, map_zero]
  exact eq_of_pow_eq_pow_of_natCast_prime_eq_zero hp hp0 h

end Work.DSM5b
