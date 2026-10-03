import Mathlib

namespace Work.FIArea4.Vflip.Vfd

theorem Hpow_le_xpow (d x H ε : ℝ) (hd : 1 ≤ d) (hH : 1 ≤ H) (hε : 0 < ε)
    (hHx : H ^ 3 = x / d) (hxd : x ≤ d * d) : H ^ (3 * ε) ≤ x ^ (ε / 2) := by
  have hd0 : 0 < d := by linarith
  have hdne : d ≠ 0 := ne_of_gt hd0
  have hH0 : 0 ≤ H := by linarith
  -- Express x in terms of d and H.
  have hx : x = d * H ^ 3 := by
    rw [hHx]
    field_simp
  -- From x ≤ d^2 and x = d * H^3, deduce H^3 ≤ d.
  have hH3le : H ^ 3 ≤ d := by
    have h : d * H ^ 3 ≤ d * d := by rwa [hx] at hxd
    exact le_of_mul_le_mul_left h hd0
  -- Hence H^6 = (H^3)^2 ≤ d * H^3 = x.
  have hH6 : H ^ 6 ≤ x := by
    have h : H ^ 3 * H ^ 3 ≤ d * H ^ 3 :=
      mul_le_mul_of_nonneg_right hH3le (pow_nonneg hH0 3)
    calc H ^ 6 = H ^ 3 * H ^ 3 := by ring
      _ ≤ d * H ^ 3 := h
      _ = x := hx.symm
  -- Raise to the power ε/2 (positive), and rewrite the left side.
  have hH6r : H ^ (6 : ℝ) ≤ x := by simpa using hH6
  have h1 : (H ^ (6 : ℝ)) ^ (ε / 2) ≤ x ^ (ε / 2) :=
    Real.rpow_le_rpow (by positivity) hH6r (by positivity)
  have h6eq : (6 : ℝ) * (ε / 2) = 3 * ε := by ring
  have h2 : H ^ (3 * ε) = (H ^ (6 : ℝ)) ^ (ε / 2) := by
    rw [← h6eq]
    exact Real.rpow_mul hH0 6 (ε / 2)
  rwa [h2]

end Work.FIArea4.Vflip.Vfd
