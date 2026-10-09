import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalCFT.Units

/-- Every `ℓ ≥ 2` admits a decomposition `ℓ = p ^ e * m` with `p` prime, `e ≥ 1`,
`p ^ e` coprime to `m`, and `m` a proper divisor of `ℓ` whenever `m ≥ 2`.
(As usual `m` may be `1`.)  The decomposition is obtained by taking any prime
divisor `p` of `ℓ` and letting `p ^ e` be the exact power of `p` dividing `ℓ`. -/
theorem exists_prime_pow_mul_coprime {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    ∃ p e m : ℕ, p.Prime ∧ 1 ≤ e ∧ ℓ = p ^ e * m ∧ (p ^ e).Coprime m ∧ (2 ≤ m → m < ℓ) := by
  have hℓ0 : ℓ ≠ 0 := by omega
  have hℓ1 : ℓ ≠ 1 := by omega
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hℓ1
  obtain ⟨e, m, hm, heq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hℓ0 p hp.ne_one
  have h1e : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with he | he
    · rw [he, pow_zero, one_mul] at heq
      exact absurd (heq ▸ hpdvd) hm
    · exact he
  refine ⟨p, e, m, hp, h1e, heq, (hp.coprime_iff_not_dvd.mpr hm).pow_left e, fun _ => ?_⟩
  have hpe : 1 < p ^ e := by
    calc 1 < p := by have := hp.two_le; omega
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos h1e
  rw [heq]
  exact lt_mul_of_one_lt_left (by omega) hpe

end NK.LocalCFT.Units
