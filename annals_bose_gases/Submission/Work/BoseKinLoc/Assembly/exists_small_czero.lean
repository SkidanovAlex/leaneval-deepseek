import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseKinLoc.Assembly

/-- There is a positive constant `c₀` (depending only on `β` and `C`) that is simultaneously
small against `1/4`, `β²/4`, and the `C`-dependent cubic and quintic thresholds needed to
absorb the auxiliary error terms: `8 C c₀³ ≤ 1/4`, `128 c₀³ ≤ 7β`, `(1600/9) C c₀⁵ ≤ 7`
and `48 c₀² ≤ 7`.

The witness is the explicit minimum `min (β²/4) (1/(1600 C + 1))`. -/
theorem exists_small_czero (β C : ℝ) (hβ : 0 < β) (hβ1 : β < 1) (hC : 0 < C) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ c₀ ≤ 1 / 4 ∧ c₀ ≤ β ^ 2 / 4 ∧ 8 * C * c₀ ^ 3 ≤ 1 / 4
      ∧ 128 * c₀ ^ 3 ≤ 7 * β ∧ (1600 / 9) * C * c₀ ^ 5 ≤ 7 ∧ 48 * c₀ ^ 2 ≤ 7 := by
  set c₀ : ℝ := min (β ^ 2 / 4) (1 / (1600 * C + 1)) with hc₀def
  have hβ2pos : 0 < β ^ 2 / 4 := by positivity
  have hDinv : 0 < 1 / (1600 * C + 1) := by positivity
  have hc₀pos : 0 < c₀ := by rw [hc₀def]; exact lt_min hβ2pos hDinv
  have hle_β : c₀ ≤ β ^ 2 / 4 := by rw [hc₀def]; exact min_le_left _ _
  have hle_D : c₀ ≤ 1 / (1600 * C + 1) := by rw [hc₀def]; exact min_le_right _ _
  refine ⟨c₀, hc₀pos, ?_, hle_β, ?_, ?_, ?_, ?_⟩
  · -- `c₀ ≤ 1/4`
    have h : β ^ 2 / 4 ≤ 1 / 4 := by
      have h2 : β ^ 2 ≤ 1 := pow_le_one₀ (le_of_lt hβ) (le_of_lt hβ1)
      linarith
    linarith
  · -- `8 * C * c₀ ^ 3 ≤ 1/4`
    have hc₀3 : c₀ ^ 3 ≤ (1 / (1600 * C + 1)) ^ 3 :=
      pow_le_pow_left₀ (le_of_lt hc₀pos) hle_D 3
    have h1 : 8 * C * c₀ ^ 3 ≤ 8 * C * (1 / (1600 * C + 1)) ^ 3 := by nlinarith [hc₀3, hC]
    have h2 : 8 * C * (1 / (1600 * C + 1)) ^ 3 ≤ 1 / 4 := by
      have hpos : (0:ℝ) < (1600 * C + 1) ^ 3 := by positivity
      have hkey : 32 * C ≤ (1600 * C + 1) ^ 3 := by
        have h3 : (1600 * C + 1) ≤ (1600 * C + 1) ^ 3 :=
          le_self_pow₀ (by linarith) (by norm_num)
        nlinarith [h3, hC]
      rw [one_div, inv_pow]
      change 8 * C / (1600 * C + 1) ^ 3 ≤ 1 / 4
      rw [div_le_iff₀ hpos]
      nlinarith [hkey]
    linarith
  · -- `128 * c₀ ^ 3 ≤ 7 * β`
    have hc₀3 : c₀ ^ 3 ≤ (β ^ 2 / 4) ^ 3 :=
      pow_le_pow_left₀ (le_of_lt hc₀pos) hle_β 3
    have hcube : c₀ ^ 3 ≤ β ^ 6 / 64 := by
      have heq : (β ^ 2 / 4) ^ 3 = β ^ 6 / 64 := by ring
      linarith [hc₀3, heq]
    have hβ6 : β ^ 6 ≤ β := by
      have h5 : β ^ 5 ≤ 1 := pow_le_one₀ (le_of_lt hβ) (le_of_lt hβ1)
      calc β ^ 6 = β * β ^ 5 := by ring
        _ ≤ β * 1 := mul_le_mul_of_nonneg_left h5 (le_of_lt hβ)
        _ = β := by ring
    nlinarith [hcube, hβ6, hβ]
  · -- `(1600/9) * C * c₀ ^ 5 ≤ 7`
    have hc₀5 : c₀ ^ 5 ≤ (1 / (1600 * C + 1)) ^ 5 :=
      pow_le_pow_left₀ (le_of_lt hc₀pos) hle_D 5
    have h1 : (1600 / 9) * C * c₀ ^ 5 ≤ (1600 / 9) * C * (1 / (1600 * C + 1)) ^ 5 := by
      nlinarith [hc₀5, hC]
    have h2 : (1600 / 9) * C * (1 / (1600 * C + 1)) ^ 5 ≤ 7 := by
      have hpos : (0:ℝ) < (1600 * C + 1) ^ 5 := by positivity
      have hkey : 1600 * C ≤ 63 * (1600 * C + 1) ^ 5 := by
        have h3 : (1600 * C + 1) ≤ (1600 * C + 1) ^ 5 :=
          le_self_pow₀ (by linarith) (by norm_num)
        nlinarith [h3, hC]
      have heq : (1600 / 9) * C * (1 / (1600 * C + 1)) ^ 5
          = (1600 * C) / (9 * (1600 * C + 1) ^ 5) := by
        rw [one_div, inv_pow]
        field_simp
      rw [heq]
      change 1600 * C / (9 * (1600 * C + 1) ^ 5) ≤ 7
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hkey]
    linarith
  · -- `48 * c₀ ^ 2 ≤ 7`
    have hc₀2 : c₀ ^ 2 ≤ (β ^ 2 / 4) ^ 2 :=
      pow_le_pow_left₀ (le_of_lt hc₀pos) hle_β 2
    have hsq : c₀ ^ 2 ≤ β ^ 4 / 16 := by
      have heq : (β ^ 2 / 4) ^ 2 = β ^ 4 / 16 := by ring
      linarith [hc₀2, heq]
    have hβ4 : β ^ 4 ≤ 1 := pow_le_one₀ (le_of_lt hβ) (le_of_lt hβ1)
    nlinarith [hsq, hβ4]

end Work.BoseKinLoc.Assembly
