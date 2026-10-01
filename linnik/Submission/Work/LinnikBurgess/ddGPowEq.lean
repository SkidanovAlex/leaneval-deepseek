import Mathlib
import Submission.Work.LinnikAreas.LocalCorr.pow_one_add_pow_prime_modEq

namespace Work.LinnikBurgess

/-- **The `p`-th-power lift of `1 + p^j`.**  For an odd prime `p`, `e ≥ 2` and `1 ≤ j ≤ e - 1`,
the `p^(e-j-1)`-th power of `1 + p^j` is congruent modulo `p^e` to `1 + p^(e-1) u` with `p ∤ u`.

This is the LTE congruence `(1+p^j)^(p^(e-j-1)) ≡ 1 + p^(e-1) (mod p^e)` of
`Work.LinnikAreas.LocalCorr.pow_one_add_pow_prime_modEq`; in fact `u = 1` already works. -/
theorem ddGPowEq {p e j : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hj : 1 ≤ j) (hje : j ≤ e - 1) :
    ∃ u : ℕ, ¬ p ∣ u ∧ (((1 + p ^ j : ℕ) : ZMod (p ^ e)) ^ (p ^ (e - j - 1))
      = ((1 + p ^ (e - 1) * u : ℕ) : ZMod (p ^ e))) := by
  have hp : p.Prime := Fact.out
  refine ⟨1, hp.not_dvd_one, ?_⟩
  simp only [mul_one]
  -- Reinterpret the base `1 + p^j` as the cast of the integer `1 + p^j`.
  have hbase : ((1 + p ^ j : ℕ) : ZMod (p ^ e)) = (1 + ((p ^ j : ℕ) : ZMod (p ^ e))) := by
    push_cast; ring
  have hcast_eq : (1 + ((p ^ j : ℕ) : ZMod (p ^ e)))
      = ((((1 + (p : ℤ) ^ j)) : ℤ) : ZMod (p ^ e)) := by
    push_cast; ring
  -- LTE: `(1 + p^j)^(p^(e-j-1)) ≡ 1 + p^(e-1)  (mod p^e)`.
  have h := Work.LinnikAreas.LocalCorr.pow_one_add_pow_prime_modEq p hp hj hp2 (e - j - 1)
  have h1 : j + (e - j - 1) = e - 1 := by omega
  rw [h1, show e - 1 + 1 = e from by omega] at h
  have hcast : ((((1 + (p : ℤ) ^ j) ^ (p ^ (e - j - 1))) : ℤ) : ZMod (p ^ e))
      = (((1 + (p : ℤ) ^ (e - 1)) : ℤ) : ZMod (p ^ e)) :=
    (ZMod.intCast_eq_intCast_iff _ _ _).mpr h
  rw [hbase, hcast_eq, ← Int.cast_pow, hcast]
  push_cast; ring

end Work.LinnikBurgess
