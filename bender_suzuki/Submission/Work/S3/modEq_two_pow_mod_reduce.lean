import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.S3

/-- Since `2 ^ p ≡ 1 [MOD 2 ^ p - 1]`, the powers of `2` are periodic modulo `2 ^ p - 1`
with period dividing `p`; hence `2 ^ i` is congruent to `2 ^ (i % p)`. -/
theorem modEq_two_pow_mod_reduce {p ℓ i : ℕ} (hp : p.Prime)
    (h : ℓ ≡ 2 ^ i [MOD 2 ^ p - 1]) : ∃ j < p, ℓ ≡ 2 ^ j [MOD 2 ^ p - 1] := by
  refine ⟨i % p, Nat.mod_lt _ hp.pos, ?_⟩
  -- `2 ^ p = (2 ^ p - 1) + 1`, so `2 ^ p ≡ 1 [MOD 2 ^ p - 1]`.
  have h2p : 2 ^ p ≡ 1 [MOD 2 ^ p - 1] := Nat.modEq_sub (Nat.one_le_two_pow)
  -- Decompose the exponent: `2 ^ i = (2 ^ p) ^ (i / p) * 2 ^ (i % p)`.
  have hdecomp : 2 ^ i = (2 ^ p) ^ (i / p) * 2 ^ (i % p) := by
    conv_lhs => rw [← Nat.div_add_mod i p]
    rw [pow_add, pow_mul]
  -- Hence `2 ^ i ≡ 2 ^ (i % p)`.
  have hpow : 2 ^ i ≡ 2 ^ (i % p) [MOD 2 ^ p - 1] := by
    rw [hdecomp]
    have hh := (h2p.pow (i / p)).mul (Nat.ModEq.refl (2 ^ (i % p)))
    simpa using hh
  exact h.trans hpow

end Work.S3
