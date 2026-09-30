import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.adi_const

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

/-- Core real-variable inequality behind `lhs_pow_bound`.

If `0 < ε`, `1 ≤ X`, `X ^ (ε²/2) ≤ P₁ ≤ X ^ ε` and `X ^ (ε²/2) ≤ P₂`, then for all
exponents `a`, `K`,
`((2 P₁)^a · X/(P₁ P₂))^K ≤ 2^(aK) · X^((εa + 1 - ε²) K)`.

The two factors are bounded separately: `(2 P₁)^a ≤ 2^a X^(εa)` using `P₁ ≤ X^ε`, and
`X/(P₁ P₂) ≤ X^(1-ε²)` using `P₂ ≥ X^(ε²/2)` (both `P₁, P₂` are at least `X^(ε²/2)`). -/
private lemma core (a K : ℕ) (ε X P₁ P₂ : ℝ) (hε : 0 < ε) (hX : 1 ≤ X)
    (hP1lo : X ^ (ε ^ 2 / 2) ≤ P₁) (hP1hi : P₁ ≤ X ^ ε)
    (hP2lo : X ^ (ε ^ 2 / 2) ≤ P₂) :
    ((2 * P₁) ^ a * (X / (P₁ * P₂))) ^ K
      ≤ (2 : ℝ) ^ (a * K) * X ^ ((ε * a + 1 - ε ^ 2) * K) := by
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hXnn : 0 ≤ X := le_of_lt hXpos
  have ht : 0 ≤ ε ^ 2 / 2 := by positivity
  have hXt : 1 ≤ X ^ (ε ^ 2 / 2) := Real.one_le_rpow hX ht
  have hXtpos : 0 < X ^ (ε ^ 2 / 2) := Real.rpow_pos_of_pos hXpos _
  have hP1nn : 0 ≤ P₁ := le_trans (le_of_lt hXtpos) hP1lo
  have hP2nn : 0 ≤ P₂ := le_trans (le_of_lt hXtpos) hP2lo
  -- First factor: `(2 P₁)^a ≤ 2^a · X^(εa)`.
  have hF1 : (2 * P₁) ^ a ≤ 2 ^ a * X ^ (ε * a) := by
    have h1 : 2 * P₁ ≤ 2 * X ^ ε := by linarith
    have h2 : (2 * X ^ ε) ^ a = 2 ^ a * X ^ (ε * a) := by
      rw [mul_pow, ← Real.rpow_natCast (X ^ ε) a, ← Real.rpow_mul hXnn ε (a : ℝ)]
    exact (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 * P₁) h1 a).trans (le_of_eq h2)
  -- Second factor: `X/(P₁ P₂) ≤ X^(1-ε²)`.
  have hF2 : X / (P₁ * P₂) ≤ X ^ (1 - ε ^ 2) := by
    have hprod : X ^ (ε ^ 2 / 2) * X ^ (ε ^ 2 / 2) ≤ P₁ * P₂ :=
      mul_le_mul hP1lo hP2lo (le_of_lt hXtpos) hP1nn
    have hsq : X ^ (ε ^ 2 / 2) * X ^ (ε ^ 2 / 2) = X ^ (ε ^ 2) := by
      rw [← Real.rpow_add hXpos]
      ring_nf
    have hsqpos : 0 < X ^ (ε ^ 2) := Real.rpow_pos_of_pos hXpos _
    have hle : X ^ (ε ^ 2) ≤ P₁ * P₂ := by rw [← hsq]; exact hprod
    have hinv : (P₁ * P₂)⁻¹ ≤ (X ^ (ε ^ 2))⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hsqpos hle
    calc X / (P₁ * P₂) = X * (P₁ * P₂)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ X * (X ^ (ε ^ 2))⁻¹ := mul_le_mul_of_nonneg_left hinv hXnn
      _ = X ^ (1 - ε ^ 2) := by
          rw [Real.rpow_sub hXpos 1 (ε ^ 2), Real.rpow_one, div_eq_mul_inv]
  -- Combine.
  have hAB : (2 * P₁) ^ a * (X / (P₁ * P₂)) ≤ 2 ^ a * X ^ (ε * a + 1 - ε ^ 2) := by
    have h := mul_le_mul hF1 hF2 (by positivity : 0 ≤ X / (P₁ * P₂))
      (by positivity : 0 ≤ 2 ^ a * X ^ (ε * a))
    have hBeq : 2 ^ a * X ^ (ε * a) * X ^ (1 - ε ^ 2) = 2 ^ a * X ^ (ε * a + 1 - ε ^ 2) := by
      rw [mul_assoc, ← Real.rpow_add hXpos (ε * a) (1 - ε ^ 2),
        show ε * a + (1 - ε ^ 2) = ε * a + 1 - ε ^ 2 by ring]
    exact h.trans (le_of_eq hBeq)
  have hAnn : 0 ≤ (2 * P₁) ^ a * (X / (P₁ * P₂)) := by positivity
  have hstep := pow_le_pow_left₀ hAnn hAB K
  refine hstep.trans (le_of_eq ?_)
  rw [mul_pow, ← pow_mul (2 : ℝ) a K, ← Real.rpow_natCast (X ^ (ε * a + 1 - ε ^ 2)) K,
    ← Real.rpow_mul hXnn (ε * a + 1 - ε ^ 2) (K : ℝ)]

theorem lhs_pow_bound (k ℓ : ℕ) (ε X P₁ P₂ : ℝ) (hε : 0 < ε) (hX : 1 ≤ X)
    (hP1lo : X ^ (ε ^ 2 / 2) ≤ P₁) (hP1hi : P₁ ≤ X ^ ε)
    (hP2lo : X ^ (ε ^ 2 / 2) ≤ P₂) :
    ((2 * P₁) ^ (2 * ℓ + 2) * (X / (P₁ * P₂))) ^ (max (Work.BMF.Kc k) 1)
      ≤ (2 : ℝ) ^ ((2 * ℓ + 2) * max (Work.BMF.Kc k) 1)
        * X ^ ((ε * (2 * ℓ + 2 : ℕ) + 1 - ε ^ 2) * (max (Work.BMF.Kc k) 1 : ℝ)) := by
  have h := core (2 * ℓ + 2) (max (Work.BMF.Kc k) 1) ε X P₁ P₂ hε hX hP1lo hP1hi hP2lo
  rw [Nat.cast_max] at h
  simpa using h

end Work.N8
