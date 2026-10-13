import Mathlib

/-!
# The alternating Frobenius identity in characteristic `p`

In a commutative ring `R` of characteristic `p` (with `p` a prime, so that `(p : R) = 0`),
the `p ^ k`-th power of a signed sum `∑ (-1)^i • c_i` equals the signed sum of the
`p ^ k`-th powers: the Frobenius map `x ↦ x ^ p` is additive, and `(-1 : R) ^ (p ^ k) = -1`
so the signs are compatible.

This is the combinatorial lemmas underlying the alternating idempotent used in the
direct-summand argument.
-/

namespace Work.DSEQP

universe u v

/-- In a ring, integer scalar multiplication by `(-1) ^ i` is multiplication by
`(-1 : R) ^ i`. -/
theorem zsmul_neg_one_pow_eq {R : Type u} [CommRing R] (i : ℕ) (x : R) :
    (-1 : ℤ) ^ i • x = (-1 : R) ^ i * x := by
  rw [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]

/-- In a commutative ring with `(p : R) = 0` and `p` prime, `(-1 : R) ^ (p ^ k) = -1`. -/
theorem neg_one_pow_prime_pow {R : Type u} [CommRing R] (p : ℕ) (hp : p.Prime)
    (hpz : (p : R) = 0) (k : ℕ) :
    (-1 : R) ^ p ^ k = -1 := by
  rcases hp.eq_two_or_odd with h | h
  · subst h
    -- in characteristic `2` we have `-1 = 1`
    have hneg : (-1 : R) = 1 := by
      have h2 : (1 : R) + 1 = 0 := by rw [one_add_one_eq_two]; exact hpz
      rw [neg_eq_iff_add_eq_zero]; exact h2
    simp [hneg]
  · -- if `p` is odd then so is `p ^ k`
    have hodd : Odd p := Nat.odd_iff.mpr h
    exact Odd.neg_one_pow hodd.pow

/-- The two-term form of the Frobenius map in characteristic `p`: `(x + y) ^ p ^ k =
x ^ p ^ k + y ^ p ^ k`. -/
theorem add_pow_prime_pow_of_char {R : Type u} [CommSemiring R] (p : ℕ) (hp : p.Prime)
    (hpz : (p : R) = 0) (x y : R) (k : ℕ) :
    (x + y) ^ p ^ k = x ^ p ^ k + y ^ p ^ k := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp x y k
  simp [hr, hpz]

/-- The Frobenius map commutes with finite sums: `(∑ i, f i) ^ p ^ k = ∑ i, (f i) ^ p ^ k`. -/
theorem sum_pow_prime_pow_of_char {R : Type u} [CommSemiring R] (p : ℕ) (hp : p.Prime)
    (hpz : (p : R) = 0) {ι : Type v} (s : Finset ι) (f : ι → R) (k : ℕ) :
    (s.sum f) ^ p ^ k = s.sum (fun i => (f i) ^ p ^ k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact zero_pow (pow_ne_zero k hp.ne_zero)
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      rw [add_pow_prime_pow_of_char p hp hpz]
      rw [ih]

/-- Since `(-1 : R) ^ (p ^ k) = -1`, the sign `(-1 : R) ^ i` is fixed by taking the
`p ^ k`-th power. -/
theorem neg_one_pow_pow_pow {R : Type u} [CommRing R] (p : ℕ) (hp : p.Prime)
    (hpz : (p : R) = 0) (i k : ℕ) :
    ((-1 : R) ^ i) ^ p ^ k = (-1 : R) ^ i := by
  rw [← pow_mul, Nat.mul_comm i (p ^ k), pow_mul, neg_one_pow_prime_pow p hp hpz k]

theorem alt_sum_pow {R : Type u} [CommRing R] (p : ℕ) [Fact p.Prime] (hp : (p : R) = 0) (n : ℕ)
    (c : Fin n → R) (k : ℕ) :
    (Finset.univ.sum fun i : Fin n => (-1 : ℤ) ^ (i : ℕ) • c i) ^ p ^ k =
      Finset.univ.sum fun i : Fin n => (-1 : ℤ) ^ (i : ℕ) • (c i) ^ p ^ k := by
  have hp' : p.Prime := Fact.out
  -- convert the integer scalar multiplications into multiplications in `R`
  have hL : (Finset.univ.sum fun i : Fin n => (-1 : ℤ) ^ (i : ℕ) • c i)
      = Finset.univ.sum fun i : Fin n => (-1 : R) ^ (i : ℕ) * c i := by
    apply Finset.sum_congr rfl
    intro i _
    exact zsmul_neg_one_pow_eq (i : ℕ) (c i)
  have hR : (Finset.univ.sum fun i : Fin n => (-1 : ℤ) ^ (i : ℕ) • (c i) ^ p ^ k)
      = Finset.univ.sum fun i : Fin n => (-1 : R) ^ (i : ℕ) * (c i) ^ p ^ k := by
    apply Finset.sum_congr rfl
    intro i _
    exact zsmul_neg_one_pow_eq (i : ℕ) ((c i) ^ p ^ k)
  rw [hL, hR]
  -- push the Frobenius through the finite sum
  rw [sum_pow_prime_pow_of_char p hp' hp Finset.univ
        (fun i : Fin n => (-1 : R) ^ (i : ℕ) * c i) k]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_pow, neg_one_pow_pow_pow p hp' hp (i : ℕ) k]

end Work.DSEQP
