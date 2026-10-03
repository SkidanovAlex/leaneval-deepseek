import Mathlib

namespace Work.A3.Weil

/-- Multiplication by an integer `a` coprime to `q` is injective on the nonzero residues
`1, …, q-1` modulo `q`: if `(a * r₁) % q = (a * r₂) % q` with `r₁, r₂ ∈ [1, q-1]` then
`r₁ = r₂`.

`a` is invertible modulo `q` (Bezout: `IsCoprime a q` means `u * a + v * q = 1` for some
`u, v`), and the two representatives `r₁, r₂` lie in a complete residue system
`[1, q-1] ⊆ [0, q)`, so a congruence `r₁ ≡ r₂ [ZMOD q]` forces equality. -/
theorem emod_mul_injOn {q : ℤ} (hq : 1 ≤ q) {a : ℤ} (ha : IsCoprime a q)
    {r₁ r₂ : ℤ} (h₁ : r₁ ∈ Finset.Icc (1 : ℤ) (q - 1)) (h₂ : r₂ ∈ Finset.Icc (1 : ℤ) (q - 1))
    (heq : (a * r₁) % q = (a * r₂) % q) : r₁ = r₂ := by
  rw [Finset.mem_Icc] at h₁ h₂
  obtain ⟨h1l, h1u⟩ := h₁
  obtain ⟨h2l, h2u⟩ := h₂
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  -- the hypothesis `heq` is exactly the congruence `a * r₁ ≡ a * r₂ [ZMOD q]`
  have hmod : a * r₁ ≡ a * r₂ [ZMOD q] := heq
  -- `a` is coprime to `q`, so `gcd q a = 1` and the modulus can be cancelled
  have hg : q.gcd a = 1 := by
    rw [Int.gcd_comm]
    exact Int.isCoprime_iff_gcd_eq_one.mp ha
  have hA : r₁ ≡ r₂ [ZMOD q] := by
    have h := Int.ModEq.cancel_left_div_gcd hqpos hmod
    simpa [hg] using h
  -- two representatives in `[1, q-1]` that are congruent mod `q` differ by a multiple of `q`
  -- of absolute value `< q`, hence are equal
  have hlt : |r₂ - r₁| < q := by
    rw [abs_lt]
    constructor <;> linarith
  have hzero := Int.eq_zero_of_abs_lt_dvd hA.dvd hlt
  linarith

end Work.A3.Weil
