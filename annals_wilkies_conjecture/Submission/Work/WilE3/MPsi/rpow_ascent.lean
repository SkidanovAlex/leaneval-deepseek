import Mathlib

namespace Work.WilE3.MPsi

/-- `A < Φ ^ (1 - θ)` with `0 < A`, `0 ≤ Φ`, `θ < 1` forces `A ^ (1 / (1 - θ)) ≤ Φ`: raise both
sides to the positive power `1 - θ`, using `(A ^ (1/(1-θ))) ^ (1-θ) = A`. -/
theorem rpow_ascent {A θ Φ : ℝ} (hA : 0 < A) (hΦ : 0 ≤ Φ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (h : A < Φ ^ (1 - θ)) : A ^ (1 / (1 - θ)) ≤ Φ := by
  have hq : 0 < 1 - θ := by linarith
  have hqne : (1 - θ) ≠ 0 := ne_of_gt hq
  -- `Φ ^ (1 - θ) > A > 0`, so `Φ` cannot vanish, hence `Φ > 0`.
  have hΦpos : 0 < Φ := by
    by_contra hc
    have hzero : Φ = 0 := le_antisymm (not_lt.mp hc) hΦ
    rw [hzero, Real.zero_rpow hqne] at h
    linarith
  -- `(A ^ (1/(1-θ))) ^ (1-θ) = A`, since `1/(1-θ) * (1-θ) = 1`.
  have key : (A ^ (1 / (1 - θ))) ^ (1 - θ) = A := by
    rw [← Real.rpow_mul hA.le]
    have hmul : 1 / (1 - θ) * (1 - θ) = 1 := div_mul_cancel₀ 1 hqne
    rw [hmul, Real.rpow_one]
  -- compare `(1-θ)`-th powers: `(A ^ (1/(1-θ)))^(1-θ) = A < Φ^(1-θ)`.
  have hlt : A ^ (1 / (1 - θ)) < Φ := by
    refine (Real.rpow_lt_rpow_iff (Real.rpow_nonneg hA.le _) hΦ hq).mp ?_
    rw [key]
    exact h
  exact le_of_lt hlt

end Work.WilE3.MPsi
