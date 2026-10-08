import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.Prove.Step10Wrap

/-- Fermat's little theorem, in the form used below: for a prime `p` and the residue `2` in `ZMod p`,
`2 ^ p = 2`.  Consequently `2 ^ p ≡ 2 (mod p)` and hence `2 ^ p - 1 ≡ 1 (mod p)`, so `p` does not
divide `2 ^ p - 1` and appears with exponent `0` in its prime factorization. -/
theorem twoPowSubOne_factorization {p : ℕ} (hp : p.Prime) : (2 ^ p - 1).factorization p = 0 := by
  apply Nat.factorization_eq_zero_of_not_dvd
  intro hdvd
  have : Fact p.Prime := ⟨hp⟩
  have h1 : 1 ≤ 2 ^ p := Nat.one_le_two_pow
  -- cast the divisibility to an identity in `ZMod p`
  have hcast : ((2 ^ p - 1 : ℕ) : ZMod p) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]; exact hdvd
  have h2 : ((2 : ZMod p) ^ p - 1) = 0 := by
    simpa only [Nat.cast_sub h1, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using hcast
  -- Fermat's little theorem: `2 ^ p = 2` in `ZMod p`, so `2 - 1 = 0`, i.e. `1 = 0`
  rw [ZMod.pow_card] at h2
  have h3 : (1 : ZMod p) = 0 := by
    have h23 : (2 : ZMod p) - 1 = 1 := by ring
    rwa [h23] at h2
  -- but `1 ≠ 0` in `ZMod p` because `p ≥ 2`
  have hp1 : p = 1 := ZMod.one_eq_zero_iff.mp h3
  have hp2 : 2 ≤ p := hp.two_le
  omega

end Work.ThmF.Prove.Step10Wrap
