import Mathlib

namespace Work.TMC16Core.Assembly

/-- For `j : ℤ` with `|j| ≤ qn` and any integer `ℓ`, the distance from `j` to the
multiple `ℓ * qn` of `qn` is at least `min |j| (qn - |j|)`, i.e. the distance from
`j` to the nearest multiple of `qn` (which is `0`, `qn` or `-qn`).
Equivalently: `min j.natAbs (qn - j.natAbs) ≤ |j - ℓ * qn|`. -/
theorem res_dist_le {qn : ℕ} {j : ℤ} (hj : j.natAbs ≤ qn) (ℓ : ℤ) :
    ((min j.natAbs (qn - j.natAbs) : ℕ) : ℤ) ≤ |j - ℓ * (qn : ℤ)| := by
  rw [Nat.cast_min]
  have ha : (j.natAbs : ℤ) = |j| := Int.natCast_natAbs j
  have hle : |j| ≤ (qn : ℤ) := by
    have := Int.ofNat_le.mpr hj
    simpa [ha] using this
  have hb : ((qn - j.natAbs : ℕ) : ℤ) = (qn : ℤ) - |j| := by
    rw [Nat.cast_sub hj, ha]
  rw [ha, hb]
  by_cases hℓ : ℓ = 0
  · -- The nearest multiple is `0`.
    rw [hℓ, zero_mul, sub_zero]
    exact min_le_left _ _
  · -- For `ℓ ≠ 0` the distance is at least `qn - |j|`.
    have h1 : (qn : ℤ) - |j| ≤ |j - ℓ * (qn : ℤ)| := by
      have hq : (0 : ℤ) ≤ (qn : ℤ) := Int.natCast_nonneg qn
      rcases lt_or_gt_of_ne hℓ with hneg | hpos
      · -- `ℓ < 0`: `ℓ * qn ≤ -qn`, so `j - ℓ*qn ≥ j + qn ≥ qn - |j| ≥ 0`.
        have hℓ1 : ℓ ≤ -1 := by omega
        have hmul : ℓ * (qn : ℤ) ≤ -(qn : ℤ) := by
          have := mul_le_mul_of_nonneg_right hℓ1 hq
          simpa using this
        have hnonneg : 0 ≤ j - ℓ * (qn : ℤ) := by
          have h2 : -|j| ≤ j := neg_abs_le j
          linarith
        rw [abs_of_nonneg hnonneg]
        have h2 : -|j| ≤ j := neg_abs_le j
        linarith
      · -- `ℓ > 0`: `ℓ * qn ≥ qn`, so `j - ℓ*qn ≤ qn - |j| ≤ 0`.
        have hℓ1 : (1 : ℤ) ≤ ℓ := by omega
        have hmul : (qn : ℤ) ≤ ℓ * (qn : ℤ) := by
          have := mul_le_mul_of_nonneg_right hℓ1 hq
          simpa using this
        have hnonpos : j - ℓ * (qn : ℤ) ≤ 0 := by
          have h2 : j ≤ |j| := le_abs_self j
          linarith
        rw [abs_of_nonpos hnonpos]
        have h2 : j ≤ |j| := le_abs_self j
        linarith
    exact le_trans (min_le_right _ _) h1

end Work.TMC16Core.Assembly
