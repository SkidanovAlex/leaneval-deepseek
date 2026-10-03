import Mathlib.NumberTheory.LegendreSymbol.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.Diophantine

/-- If `p ≡ 3 (mod 4)` is prime and `p ∣ a ^ 2 + b ^ 2`, then `p` divides both
`a` and `b`. -/
lemma prime_three_mod_four_dvd_sq_add_sq {p a b : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3)
    (h : p ∣ a ^ 2 + b ^ 2) : p ∣ a ∧ p ∣ b := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- Reduce the divisibility to an equality in `ZMod p`.
  have hz : (a : ZMod p) ^ 2 + (b : ZMod p) ^ 2 = 0 := by
    have h0 : ((a ^ 2 + b ^ 2 : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff (a ^ 2 + b ^ 2) p).mpr h
    simpa using h0
  -- If `b` were not divisible by `p`, then `a` would be a root of `x ^ 2 + b ^ 2`.
  have hpb : p ∣ b := by
    by_contra hb
    have hb_ne : (b : ZMod p) ≠ 0 := fun hb0 =>
      hb ((ZMod.natCast_eq_zero_iff b p).mp hb0)
    have hxy : (a : ZMod p) ^ 2 = -((b : ZMod p) ^ 2) := eq_neg_of_add_eq_zero_left hz
    exact (ZMod.mod_four_ne_three_of_sq_eq_neg_sq' hb_ne hxy) hp4
  refine ⟨?_, hpb⟩
  have hb2 : p ∣ b ^ 2 := by
    rw [pow_two]
    exact dvd_mul_of_dvd_left hpb b
  have hpa2 : p ∣ a ^ 2 := by
    simpa [Nat.add_sub_cancel] using Nat.dvd_sub h hb2
  exact hp.dvd_of_dvd_pow hpa2

end Commons.NumberTheory.Diophantine