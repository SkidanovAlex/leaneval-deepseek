import Mathlib

namespace Work.WilC4

/-- If a positive lower bound `m` and an upper bound `M` are both attained by `x ^ d`
for arbitrarily large `x`, then the exponent must vanish.

Indeed, for `d > 0` the map `x ↦ x ^ d` is unbounded above, while for `d < 0` it
tends to `0`, so it eventually drops below the positive bound `m`. -/
theorem rpow_bounded_exponent_zero {d m M : ℝ} (hm : 0 < m) (hbdd : ∀ R : ℝ, ∃ x : ℝ, R ≤ x ∧ m ≤ x ^ d ∧ x ^ d ≤ M) : d = 0 := by
  by_contra hd
  rcases lt_or_gt_of_ne hd with hdneg | hdpos
  · -- Case `d < 0`: `x ↦ x ^ d` is eventually smaller than `m`.
    set x0 : ℝ := (m / 2) ^ (1 / d) with hx0def
    have hm2 : 0 < m / 2 := by linarith
    have hx0pos : 0 < x0 := by rw [hx0def]; exact Real.rpow_pos_of_pos hm2 _
    have hx0d : x0 ^ d = m / 2 := by
      rw [hx0def, ← Real.rpow_mul (le_of_lt hm2) (1 / d) d]
      have hone : 1 / d * d = 1 := by field_simp
      rw [hone, Real.rpow_one]
    obtain ⟨x, hxR, hmxle, -⟩ := hbdd x0
    have hle : x ^ d ≤ x0 ^ d := Real.rpow_le_rpow_of_nonpos hx0pos hxR (le_of_lt hdneg)
    rw [hx0d] at hle
    linarith
  · -- Case `0 < d`: `x ↦ x ^ d` is eventually larger than the upper bound `M`.
    set A : ℝ := |M| + 2 with hAdef
    have hApos : 0 < A := by rw [hAdef]; positivity
    have hMA : M < A := by rw [hAdef]; have := le_abs_self M; linarith
    set x0 : ℝ := A ^ (1 / d) with hx0def
    have hx0pos : 0 < x0 := by rw [hx0def]; exact Real.rpow_pos_of_pos hApos _
    have hx0d : x0 ^ d = A := by
      rw [hx0def, ← Real.rpow_mul (le_of_lt hApos) (1 / d) d]
      have hone : 1 / d * d = 1 := by field_simp
      rw [hone, Real.rpow_one]
    obtain ⟨x, hxR, -, hxM⟩ := hbdd x0
    have hle : x0 ^ d ≤ x ^ d := Real.rpow_le_rpow (le_of_lt hx0pos) hxR (le_of_lt hdpos)
    rw [hx0d] at hle
    linarith

end Work.WilC4
