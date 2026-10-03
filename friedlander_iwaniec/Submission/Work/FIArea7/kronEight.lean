import Mathlib
import Submission.Work.FIArea7.KronTwoAux
import Submission.Work.FIArea7.KronTwo

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea7

/-! ## Auxiliary arithmetic in `ℤ/8ℤ`

Everything below is used to transfer the hypotheses of `kronEight` — parity of `g, uᵢ` and the
congruences `mod 4` — into the ring `ZMod 8`, where the final 8-adic identity is a finite
computation (`decide`). -/

/-- The finite core of the identity, in the ring `ℤ/8ℤ`: for odd `U₁,U₂` (i.e. `Uᵢ² = 1`),
even `S₁,S₂` (i.e. `4 Sᵢ = 0`), `U₁ ≡ U₂` and `S₁ ≡ S₂` modulo `4` (i.e. `2 (U₁-U₂) = 0`,
`2 (S₁-S₂) = 0`), the product `(U₁U₂ + S₁S₂)(U₁² + S₁²)` equals `U₁U₂`. -/
lemma kronEight_key : ∀ U1 U2 S1 S2 : ZMod 8,
    U1 ^ 2 = 1 → U2 ^ 2 = 1 → 4 * S1 = 0 → 4 * S2 = 0 →
    2 * (U1 - U2) = 0 → 2 * (S1 - S2) = 0 →
    (U1 * U2 + S1 * S2) * (U1 ^ 2 + S1 ^ 2) = U1 * U2 := by
  decide

/-- `4 y (y+1) = 0` in `ℤ/8ℤ`, the source of `x² = 1` for odd `x`. -/
lemma kronEight_four_mul_mul_succ : ∀ y : ZMod 8, (4 : ZMod 8) * y * (y + 1) = 0 := by
  decide

/-- The square of an odd natural number is `1` in `ℤ/8ℤ`. -/
lemma kronEight_odd_sq {n : ℕ} (hn : Odd n) : (n : ZMod 8) ^ 2 = 1 := by
  obtain ⟨k, hk⟩ := hn
  subst hk
  push_cast
  have h : (4 : ZMod 8) * (k : ZMod 8) * ((k : ZMod 8) + 1) = 0 :=
    kronEight_four_mul_mul_succ _
  linear_combination h

/-- An even integer is killed by the multiplication-by-`4` of `ℤ/8ℤ`. -/
lemma kronEight_four_mul_of_even {s : ℤ} (hs : Even s) : (4 : ZMod 8) * (s : ZMod 8) = 0 := by
  have h2 : ((4 * s : ℤ) : ZMod 8) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    obtain ⟨k, hk⟩ := hs
    exact ⟨k, by rw [hk]; ring⟩
  simpa using h2

/-- Congruence modulo `4` of two integers becomes `2 (a - b) = 0` in `ℤ/8ℤ`. -/
lemma kronEight_two_mul_sub_of_modEq {a b : ℤ} (h : a ≡ b [ZMOD 4]) :
    (2 : ZMod 8) * ((a : ZMod 8) - (b : ZMod 8)) = 0 := by
  have h2 : ((2 * (a - b) : ℤ) : ZMod 8) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    obtain ⟨c, hc⟩ := h.dvd
    exact ⟨-c, by omega⟩
  simpa using h2

/-- **The 2-adic correction is an 8-adic identity.**  With `g` odd, `u₁,u₂` odd satisfying
`u₁ ≡ u₂ (mod 4)`, `s₁,s₂` even satisfying `s₁ ≡ s₂ (mod 4)`, and `A = g²u₁u₂ + s₁s₂`,
`B = g²u₁² + s₁²` (both odd), one has `χ₂(A)·χ₂(B) = χ₂(u₁u₂)`, equivalently `A·B ≡ u₁u₂ (mod 8)`.
This is exactly the correction factor by which the `mod 4` form of *FI* Lemma 17.1 differs from
the `mod 8` form (`Work.FIArea7.kronTwo = ZMod.χ₈ = (2|·)`, which depends only on the residue
mod 8). -/
theorem kronEight {g u1 u2 : ℕ} {s1 s2 : ℤ}
    (hg : Odd g) (hu1 : Odd u1) (hu2 : Odd u2) (hs1 : Even s1) (hs2 : Even s2)
    (h4 : (u1 : ℤ) ≡ (u2 : ℤ) [ZMOD 4]) (hs4 : s1 ≡ s2 [ZMOD 4]) :
    Work.FIArea7.kronTwo ((g : ℤ) ^ 2 * (u1 : ℤ) * (u2 : ℤ) + s1 * s2)
        * Work.FIArea7.kronTwo ((g : ℤ) ^ 2 * (u1 : ℤ) ^ 2 + s1 ^ 2)
      = Work.FIArea7.kronTwo ((u1 : ℤ) * (u2 : ℤ)) := by
  -- `χ₂` is multiplicative, so it suffices to compare the two arguments modulo `8`,
  rw [← Work.FIArea7.kronTwo_mul]
  apply Work.FIArea7.kronTwo_eq_of_modEq
  -- which is the `ℤ/8ℤ`-statement `kronEight_key`, after feeding in the parity and `mod 4` data.
  apply (ZMod.intCast_eq_intCast_iff _ _ 8).mp
  push_cast
  rw [kronEight_odd_sq hg]
  simp only [one_mul]
  exact kronEight_key _ _ _ _ (kronEight_odd_sq hu1) (kronEight_odd_sq hu2)
    (kronEight_four_mul_of_even hs1) (kronEight_four_mul_of_even hs2)
    (kronEight_two_mul_sub_of_modEq h4) (kronEight_two_mul_sub_of_modEq hs4)

end Work.FIArea7
