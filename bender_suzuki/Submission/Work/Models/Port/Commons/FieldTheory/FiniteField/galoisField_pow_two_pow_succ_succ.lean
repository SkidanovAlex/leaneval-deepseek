import Mathlib.FieldTheory.Finite.GaloisField

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Powers in a Galois field

For a finite field `K` with `q = #K` elements one has `x ^ q = x` for every `x : K`
(`FiniteField.pow_card`).  Specialising to `K = GaloisField p n`, whose cardinality is
`p ^ n`, gives `x ^ (p ^ n) = x`.

As a consequence, in `GaloisField 2 (2 * n + 1)` the `(n + 1)`-fold squaring map composed
with itself is the ordinary squaring map, i.e.

`(x ^ 2 ^ (n + 1)) ^ 2 ^ (n + 1) = x ^ 2`,

because `2 ^ (n + 1) * 2 ^ (n + 1) = 2 ^ (2 * n + 1) * 2` and `x ^ 2 ^ (2 * n + 1) = x`.
-/

namespace Commons.FieldTheory.FiniteField

set_option linter.style.haveILetI false

/-- Frobenius-type identity in a Galois field: every element of `GaloisField p n`
(`n ≠ 0`) is fixed by the `n`-fold Frobenius `x ↦ x ^ (p ^ n)`. -/
theorem galoisField_pow_card_pow_self {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : n ≠ 0)
    (x : GaloisField p n) : x ^ p ^ n = x := by
  haveI : Fintype (GaloisField p n) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField p n) = p ^ n := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card]
    exact hn
  rw [← hcard]
  exact FiniteField.pow_card x

theorem galoisField_pow_two_pow_succ_succ (n : ℕ) (x : GaloisField 2 (2 * n + 1)) :
    (x ^ 2 ^ (n + 1)) ^ 2 ^ (n + 1) = x ^ 2 := by
  have hx : x ^ (2 ^ (2 * n + 1)) = x :=
    galoisField_pow_card_pow_self (p := 2) (2 * n + 1) (by omega) x
  have hpow : 2 ^ (n + 1) * 2 ^ (n + 1) = 2 ^ (2 * n + 1) * 2 := by
    rw [← pow_add, ← pow_succ]
    congr 1
    omega
  rw [← pow_mul, hpow, pow_mul, hx]

end Commons.FieldTheory.FiniteField