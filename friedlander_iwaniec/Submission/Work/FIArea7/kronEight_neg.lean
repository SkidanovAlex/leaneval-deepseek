/-
# `Submission.Work.FIArea7.kronEight_neg` — the "opposite sign" 2-adic identity

`kronEight.lean` proves the `mod 4` correction factor for *FI* Lemma 17.1 in the case
`u₁ ≡ u₂ (mod 4)`:  for `g, u₁, u₂` odd and `s₁, s₂` even with `s₁ ≡ s₂ (mod 4)`,

  `χ₂(g²u₁u₂ + s₁s₂)·χ₂(g²u₁² + s₁²) = χ₂(u₁u₂)`,   `χ₂ = kronTwo = ZMod.χ₈ = (2|·)`.

The present file is the companion identity for the *other* residue class
`u₁ + u₂ ≡ 0 (mod 4)` (i.e. `u₂ ≡ -u₁ (mod 4)`, which the `Δ < 0` branch of the
reciprocity argument produces), where the cross term appears with the *opposite sign*:

  `χ₂(g²u₁u₂ − s₁s₂)·χ₂(g²u₁² + s₁²) = χ₂(u₁u₂)`.

Since `χ₂` is a multiplicative function of the argument modulo `8`, this reduces to the
`ℤ/8ℤ`-statement `kronEight_neg_key`.  The latter is *equivalent* to the positive key
`kronEight_key` under `U₂ ↦ −U₂`: the substitution flips `(U₁U₂ + S₁S₂)` into `−(U₁U₂ − S₁S₂)`
and `U₁U₂` into `−U₁U₂`, so the two sides differ by an overall sign, while the hypothesis
`2(U₁ − U₂) = 0` of the positive key becomes exactly `2(U₁ + U₂) = 0`.  This is why the
negative case needs no new finite computation.
-/
import Mathlib
import Submission.Work.FIArea7.KronTwoAux
import Submission.Work.FIArea7.kronEight

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea7

/-- Congruence `a + b ≡ 0 (mod 4)` of two integers becomes `2(a + b) = 0` in `ℤ/8ℤ`. -/
lemma kronEight_two_mul_add_of_modEq {a b : ℤ} (h : a + b ≡ 0 [ZMOD 4]) :
    (2 : ZMod 8) * ((a : ZMod 8) + (b : ZMod 8)) = 0 := by
  have hh : (4 : ℤ) ∣ a + b := by
    have hd := Int.modEq_iff_dvd.mp h
    obtain ⟨c, hc⟩ := hd
    exact ⟨-c, by omega⟩
  obtain ⟨c, hc⟩ := hh
  have h2 : ((2 * (a + b) : ℤ) : ZMod 8) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨c, by omega⟩
  simpa using h2

/-- **The finite core of the negative identity**, in the ring `ℤ/8ℤ`: for odd `U₁,U₂`
(`Uᵢ² = 1`), even `S₁,S₂` (`4 Sᵢ = 0`) and `U₁ + U₂ ≡ 0 (mod 4)`, `S₁ ≡ S₂ (mod 4)` — i.e.
`2(U₁ + U₂) = 0`, `2(S₁ − S₂) = 0` — the product `(U₁U₂ − S₁S₂)(U₁² + S₁²)` equals `U₁U₂`.

Obtained from the positive core `kronEight_key` by `U₂ ↦ −U₂`. -/
lemma kronEight_neg_key : ∀ U1 U2 S1 S2 : ZMod 8,
    U1 ^ 2 = 1 → U2 ^ 2 = 1 → 4 * S1 = 0 → 4 * S2 = 0 →
    2 * (U1 + U2) = 0 → 2 * (S1 - S2) = 0 →
    (U1 * U2 - S1 * S2) * (U1 ^ 2 + S1 ^ 2) = U1 * U2 := by
  intro U1 U2 S1 S2 hU1 hU2 hS1 hS2 hA hS
  have hkey := kronEight_key U1 (-U2) S1 S2 hU1 (by rw [neg_sq]; exact hU2) hS1 hS2
    (by rw [sub_neg_eq_add]; exact hA) hS
  linear_combination -hkey

/-- **The 2-adic correction in the negative-`Δ` residue class.**  With `g` odd, `u₁,u₂` odd
satisfying `u₁ + u₂ ≡ 0 (mod 4)`, `s₁,s₂` even satisfying `s₁ ≡ s₂ (mod 4)`, and
`A' = g²u₁u₂ − s₁s₂`, `B = g²u₁² + s₁²` (both odd), one has `χ₂(A')·χ₂(B) = χ₂(u₁u₂)`,
equivalently `A'·B ≡ u₁u₂ (mod 8)`.  This is the companion of `kronEight` in the case the
reciprocity argument of *FI* Lemma 17.1 reaches with the sign `Δ < 0`. -/
theorem kronEight_neg {g u1 u2 : ℕ} {s1 s2 : ℤ}
    (hg : Odd g) (hu1 : Odd u1) (hu2 : Odd u2) (hs1 : Even s1) (hs2 : Even s2)
    (h4 : (u1 : ℤ) + (u2 : ℤ) ≡ 0 [ZMOD 4]) (hs4 : s1 ≡ s2 [ZMOD 4]) :
    Work.FIArea7.kronTwo ((g : ℤ) ^ 2 * (u1 : ℤ) * (u2 : ℤ) - s1 * s2)
        * Work.FIArea7.kronTwo ((g : ℤ) ^ 2 * (u1 : ℤ) ^ 2 + s1 ^ 2)
      = Work.FIArea7.kronTwo ((u1 : ℤ) * (u2 : ℤ)) := by
  -- `χ₂` is multiplicative, so it suffices to compare the arguments modulo `8`,
  rw [← Work.FIArea7.kronTwo_mul]
  apply Work.FIArea7.kronTwo_eq_of_modEq
  -- which is the `ℤ/8ℤ`-statement `kronEight_neg_key`, after feeding in parity and `mod 4`.
  apply (ZMod.intCast_eq_intCast_iff _ _ 8).mp
  push_cast
  rw [kronEight_odd_sq hg]
  simp only [one_mul]
  exact kronEight_neg_key _ _ _ _ (kronEight_odd_sq hu1) (kronEight_odd_sq hu2)
    (kronEight_four_mul_of_even hs1) (kronEight_four_mul_of_even hs2)
    (kronEight_two_mul_add_of_modEq h4) (kronEight_two_mul_sub_of_modEq hs4)

end Work.FIArea7
