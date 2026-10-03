import Mathlib
import Submission.Work.Peluse.ladderA_defs

namespace Work.Peluse.LadderA

/-! ## Two integer-arithmetic helpers

The shift bound below is an instance of the elementary fact that the Euclidean (i.e. floor)
division of `ℤ` by a positive integer is superadditive, together with the triangle inequality
`|a - b| ≤ |a| + |b|`. -/

/-- Superadditivity of Euclidean division of `ℤ` by a positive integer:
`a / c + b / c ≤ (a + b) / c` for `0 < c`. -/
theorem int_ediv_add_ediv_le {a b c : ℤ} (hc : 0 < c) : a / c + b / c ≤ (a + b) / c := by
  rw [Int.le_ediv_iff_mul_le hc]
  have h1 := Int.ediv_mul_le a (ne_of_gt hc)
  have h2 := Int.ediv_mul_le b (ne_of_gt hc)
  have h3 : (a / c + b / c) * c = a / c * c + b / c * c := by ring
  rw [h3]; linarith

/-- The triangle inequality in the difference form `|a - b| ≤ |a| + |b|`. -/
theorem abs_sub_le_abs_add_abs (a b : ℤ) : |a - b| ≤ |a| + |b| := by
  rw [sub_eq_add_neg, ← abs_neg b]
  exact abs_add_le a (-b)

/-- **The symmetric shift bound.**  If the vector `d` is bounded by `C·N/M₁` in sup norm and the
product `M₁·M₂` fits in the window `N/c` (with `M₂ ≥ 1`, `M₂ ≤ M₁`, `0 < c`), then shifting `d` by
either of the two symmetric shifts `c·M₂` and `c` keeps it within the (slightly enlarged) bound
`(C+1)·N/M₁`.

Mathematically the point is that both shifts are bounded by `(N:ℤ)/(M₁:ℤ)`:
`c·M₂ ≤ (N:ℤ)/(M₁:ℤ)` follows from `c·M₁·M₂ ≤ N` (the integral form of `hscale`) and
`c ≤ (N:ℤ)/(M₁:ℤ)` from `c·M₁ ≤ c·M₁·M₂ ≤ N`; the enlarged ceiling comes from the superadditivity
of Euclidean division, `⌊C·N/M₁⌋ + ⌊N/M₁⌋ ≤ ⌊(C+1)·N/M₁⌋`. -/
theorem symmShiftBound {s : ℕ} {C : ℕ} {c : ℤ} (hc : 0 < c) {N M₁ M₂ : ℕ}
    (hM₂ : 1 ≤ M₂) (hM₁ : M₂ ≤ M₁) (hscale : (M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ) / (c : ℝ))
    (d : Fin s → ℤ) (hd : ∀ i : Fin s, |d i| ≤ (C : ℤ) * (N : ℤ) / (M₁ : ℤ)) :
    (∀ i : Fin s, |d i - c * (M₂ : ℤ)| ≤ ((C + 1 : ℕ) : ℤ) * (N : ℤ) / (M₁ : ℤ)) ∧
    (∀ i : Fin s, |d i - c| ≤ ((C + 1 : ℕ) : ℤ) * (N : ℤ) / (M₁ : ℤ)) := by
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  -- `1 ≤ M₂ ≤ M₁` gives `M₁ > 0`, so that `(N : ℤ) / (M₁ : ℤ)` is honest floor division.
  have hM1pos : (0 : ℤ) < (M₁ : ℤ) := by
    have : (1 : ℤ) ≤ (M₁ : ℤ) := by exact_mod_cast (le_trans hM₂ hM₁)
    linarith
  have hcM₁_nonneg : 0 ≤ c * (M₁ : ℤ) := mul_nonneg (le_of_lt hc) (Int.natCast_nonneg M₁)
  -- Integral form of the scale hypothesis: `c·M₁·M₂ ≤ N`.
  have hscaleZ : c * (M₁ : ℤ) * (M₂ : ℤ) ≤ (N : ℤ) := by
    have hdiv : (c : ℝ) * ((N : ℝ) / (c : ℝ)) = (N : ℝ) := by field_simp
    have h1 : (c : ℝ) * ((M₁ : ℝ) * (M₂ : ℝ)) ≤ (N : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hscale (le_of_lt hcR)
      rw [hdiv] at h
      exact h
    have hL : ((c * (M₁ : ℤ) * (M₂ : ℤ) : ℤ) : ℝ) = (c : ℝ) * ((M₁ : ℝ) * (M₂ : ℝ)) := by
      push_cast
      ring
    have h3 : ((c * (M₁ : ℤ) * (M₂ : ℤ) : ℤ) : ℝ) ≤ (N : ℝ) := by rw [hL]; exact h1
    exact_mod_cast h3
  -- Both shifts are bounded by `(N : ℤ) / (M₁ : ℤ)`.
  have hcm₂ : c * (M₂ : ℤ) ≤ (N : ℤ) / (M₁ : ℤ) := by
    apply (Int.le_ediv_iff_mul_le hM1pos).mpr
    calc (c * (M₂ : ℤ)) * (M₁ : ℤ) = c * (M₁ : ℤ) * (M₂ : ℤ) := by ring
      _ ≤ (N : ℤ) := hscaleZ
  have hc_le : c ≤ (N : ℤ) / (M₁ : ℤ) := by
    apply (Int.le_ediv_iff_mul_le hM1pos).mpr
    calc c * (M₁ : ℤ) = c * (M₁ : ℤ) * 1 := by ring
      _ ≤ c * (M₁ : ℤ) * (M₂ : ℤ) := by
            apply mul_le_mul_of_nonneg_left _ hcM₁_nonneg
            exact_mod_cast hM₂
      _ ≤ (N : ℤ) := hscaleZ
  -- The enlarged ceiling absorbs the shift.
  have hsuper : (C : ℤ) * (N : ℤ) / (M₁ : ℤ) + (N : ℤ) / (M₁ : ℤ)
      ≤ ((C + 1 : ℕ) : ℤ) * (N : ℤ) / (M₁ : ℤ) := by
    have hcast : ((C : ℤ) * (N : ℤ) + (N : ℤ)) = ((C + 1 : ℕ) : ℤ) * (N : ℤ) := by
      push_cast; ring
    have h := int_ediv_add_ediv_le (a := (C : ℤ) * (N : ℤ)) (b := (N : ℤ)) hM1pos
    rw [hcast] at h
    exact h
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have h1 := hd i
    have h3 : |d i - c * (M₂ : ℤ)| ≤ |d i| + c * (M₂ : ℤ) := by
      have hcnn : 0 ≤ c * (M₂ : ℤ) := mul_nonneg (le_of_lt hc) (Int.natCast_nonneg M₂)
      calc |d i - c * (M₂ : ℤ)| ≤ |d i| + |c * (M₂ : ℤ)| := abs_sub_le_abs_add_abs _ _
        _ = |d i| + c * (M₂ : ℤ) := by rw [abs_of_nonneg hcnn]
    linarith [h3, h1, hcm₂, hsuper]
  · have h1 := hd i
    have h3 : |d i - c| ≤ |d i| + c := by
      calc |d i - c| ≤ |d i| + |c| := abs_sub_le_abs_add_abs _ _
        _ = |d i| + c := by rw [abs_of_pos hc]
    linarith [h3, h1, hc_le, hsuper]

end Work.Peluse.LadderA
