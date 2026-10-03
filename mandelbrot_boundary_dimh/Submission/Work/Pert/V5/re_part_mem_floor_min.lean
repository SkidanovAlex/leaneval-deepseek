import Mathlib

namespace Work.Pert.V5

/-- The real part of `p + t • v` (with `t ∈ [0, ℓ]`, `‖v‖ = 1`, `ℓ ≤ 1/2`) lies in the
interval `[⌊min p.re (p.re + ℓ * v.re)⌋, ⌊min p.re (p.re + ℓ * v.re)⌋ + 3/2]`.

The interval `[p.re, p.re + ℓ * v.re]` has length `ℓ * |v.re| ≤ ℓ ≤ 1/2`, and `p.re + t * v.re`
is a convex combination of its endpoints, hence lies in it; finally `m < ⌊m⌋ + 1` gives the
`3/2 = 1/2 + 1` slack. -/
theorem re_part_mem_floor_min {p v : ℂ} {ℓ t : ℝ} (hℓ : 0 ≤ ℓ) (hshort : ℓ ≤ 1 / 2)
    (hv : ‖v‖ = 1) (ht : t ∈ Set.Icc (0:ℝ) ℓ) :
    ((⌊min p.re (p.re + ℓ * v.re)⌋ : ℤ) : ℝ) ≤ (p + (t : ℂ) • v).re ∧
      (p + (t : ℂ) • v).re ≤ ((⌊min p.re (p.re + ℓ * v.re)⌋ : ℤ) : ℝ) + 3 / 2 := by
  obtain ⟨ht0, htℓ⟩ := ht
  have hre : (p + (t : ℂ) • v).re = p.re + t * v.re := by
    simp [Complex.add_re]
  have hvre_abs : |v.re| ≤ 1 := by
    have h := Complex.abs_re_le_norm v
    rwa [hv] at h
  have hvre_le : v.re ≤ 1 := (abs_le.mp hvre_abs).2
  have hvre_ge : -1 ≤ v.re := (abs_le.mp hvre_abs).1
  rw [hre]
  by_cases hℓ0 : ℓ = 0
  · -- degenerate case `ℓ = 0`, where `t = 0`
    subst hℓ0
    have ht_eq : t = 0 := le_antisymm htℓ ht0
    subst ht_eq
    simp only [zero_mul, add_zero, min_self]
    constructor
    · exact Int.floor_le p.re
    · have h := Int.lt_floor_add_one p.re; linarith
  · rcases le_total 0 v.re with hvpos | hvnonpos
    · -- `v.re ≥ 0`: the interval is `[p.re, p.re + ℓ * v.re]`, and `min` is `p.re`
      have hmin : min p.re (p.re + ℓ * v.re) = p.re :=
        min_eq_left (by have h := mul_nonneg hℓ hvpos; linarith)
      rw [hmin]
      have htvre0 : 0 ≤ t * v.re := mul_nonneg ht0 hvpos
      have htvre_le : t * v.re ≤ ℓ * v.re := mul_le_mul_of_nonneg_right htℓ hvpos
      have hδle : ℓ * v.re ≤ 1 / 2 := by
        have h1 : ℓ * v.re ≤ ℓ * 1 := mul_le_mul_of_nonneg_left hvre_le hℓ
        linarith
      constructor
      · have h1 : (⌊p.re⌋ : ℝ) ≤ p.re := Int.floor_le _
        linarith
      · have h1 : p.re < (⌊p.re⌋ : ℝ) + 1 := Int.lt_floor_add_one _
        linarith
    · -- `v.re ≤ 0`: the interval is `[p.re + ℓ * v.re, p.re]`, and `min` is `p.re + ℓ * v.re`
      have hmin : min p.re (p.re + ℓ * v.re) = p.re + ℓ * v.re :=
        min_eq_right (by have h := mul_nonpos_of_nonneg_of_nonpos hℓ hvnonpos; linarith)
      rw [hmin]
      have htvre_le0 : t * v.re ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0 hvnonpos
      have htvre_ge : ℓ * v.re ≤ t * v.re := mul_le_mul_of_nonpos_right htℓ hvnonpos
      have hδge : -(1/2 : ℝ) ≤ ℓ * v.re := by
        have h1 : ℓ * (-1) ≤ ℓ * v.re := mul_le_mul_of_nonneg_left hvre_ge hℓ
        linarith
      constructor
      · have h1 : (⌊p.re + ℓ * v.re⌋ : ℝ) ≤ p.re + ℓ * v.re := Int.floor_le _
        linarith
      · have h1 : p.re + ℓ * v.re < (⌊p.re + ℓ * v.re⌋ : ℝ) + 1 := Int.lt_floor_add_one _
        linarith

end Work.Pert.V5
