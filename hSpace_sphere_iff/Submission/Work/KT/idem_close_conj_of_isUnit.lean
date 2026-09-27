import Mathlib

namespace Work.KT

/-- Two idempotents `p` and `q` in a ring `A` are conjugate by a unit as soon as
`1 + (2 * p - 1) * (q - p)` is a unit.

Concretely, the unit `u = 1 + (2 * p - 1) * (q - p)` satisfies `u * q = p * u`.
The proof is a direct computation: writing `a = 2 * p - 1` we have `a * p = p`,
`p * a = p` and `1 + a = 2 * p` (as `p` is idempotent), and then both `u * q` and
`p * u` reduce to `p * q` (using `q * q = q`). -/
theorem idem_close_conj_of_isUnit {A : Type*} [Ring A] {p q : A} (hp : p * p = p)
    (hq : q * q = q) (hu : IsUnit (1 + (2 * p - 1) * (q - p))) :
    ∃ u : Aˣ, (u : A) * q = p * (u : A) := by
  refine ⟨hu.unit, ?_⟩
  rw [hu.unit_spec]
  set a : A := 2 * p - 1 with ha
  have h1 : a * p = p := by
    rw [ha, sub_mul, one_mul, mul_assoc, hp, two_mul, add_sub_cancel_left]
  have h2 : p * a = p := by
    rw [ha, mul_sub, mul_one, two_mul, mul_add, hp, add_sub_cancel_left]
  have h3 : 1 + a = 2 * p := by
    rw [ha]; abel
  have hadd : q + a * q = (1 + a) * q := by
    rw [add_mul, one_mul]
  have hu_eq : 1 + a * (q - p) = 1 + a * q - p := by
    rw [mul_sub, h1]; abel
  have hL : (1 + a * q - p) * q = p * q := by
    rw [sub_mul, add_mul, one_mul, mul_assoc, hq, hadd, h3, mul_assoc, two_mul, add_sub_cancel_left]
  have hR : p * (1 + a * q - p) = p * q := by
    rw [mul_sub, mul_add, mul_one, ← mul_assoc, h2, hp]; abel
  rw [hu_eq, hL, hR]

end Work.KT
