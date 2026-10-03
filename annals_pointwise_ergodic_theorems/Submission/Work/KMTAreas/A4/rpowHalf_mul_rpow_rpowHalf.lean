import Mathlib

namespace Work.KMTAreas.A4

/-- Bookkeeping of half-powers: for `X, δ, Nd ≥ 0` and conjugate exponents `p, q ≥ 1`,
`(X δ^{1/2} Nd^{1/p})^{1/2} (X Nd^{1/q})^{1/2} = X δ^{1/4} Nd^{1/2}`.
Indeed both sides equal `X δ^{1/4} Nd^{(1/p+1/q)/2}`. -/
theorem rpowHalf_mul_rpow_rpowHalf {X δ Nd p q : ℝ} (hX : 0 ≤ X) (hδ : 0 ≤ δ) (hNd : 0 ≤ Nd) (hp : 0 < p) (hq : 0 < q) (hpq : 1 / p + 1 / q = 1) : (X * δ ^ (1 / 2 : ℝ) * Nd ^ (1 / p)) ^ (1 / 2 : ℝ) * (X * Nd ^ (1 / q)) ^ (1 / 2 : ℝ) = X * δ ^ (1 / 4 : ℝ) * Nd ^ (1 / 2 : ℝ) := by
  have _hp := hp
  have _hq := hq
  have hδ2 : 0 ≤ δ ^ (1 / 2 : ℝ) := Real.rpow_nonneg hδ _
  have hNd1 : 0 ≤ Nd ^ (1 / p) := Real.rpow_nonneg hNd _
  have hNd2 : 0 ≤ Nd ^ (1 / q) := Real.rpow_nonneg hNd _
  have h1 : 0 ≤ X * δ ^ (1 / 2 : ℝ) := mul_nonneg hX hδ2
  -- `(X^{1/2})^2 = X` for `X ≥ 0`
  have hXsq : (X ^ (1 / 2 : ℝ)) ^ 2 = X := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sq_sqrt hX
  have hpqi : p⁻¹ + q⁻¹ = 1 := by
    simpa [one_div] using hpq
  have hexp : p⁻¹ * (1 / 2 : ℝ) + q⁻¹ * (1 / 2 : ℝ) = 1 / 2 := by
    rw [← add_mul, hpqi, one_mul]
  -- `Nd^{(1/p)/2} * Nd^{(1/q)/2} = Nd^{1/2}` for `Nd ≥ 0`
  have hNdc : Nd ^ (p⁻¹ * (1 / 2 : ℝ)) * Nd ^ (q⁻¹ * (1 / 2 : ℝ)) = Nd ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add' (x := Nd) (y := p⁻¹ * (1 / 2 : ℝ)) (z := q⁻¹ * (1 / 2 : ℝ)) hNd
      (by rw [hexp]; norm_num), hexp]
  -- split all the half-powers of products
  rw [Real.mul_rpow h1 hNd1, Real.mul_rpow hX hδ2, Real.mul_rpow hX hNd2]
  -- push the outer `1/2` inside the inner powers
  rw [← Real.rpow_mul hδ (1 / 2) (1 / 2), ← Real.rpow_mul hNd (1 / p) (1 / 2),
    ← Real.rpow_mul hNd (1 / q) (1 / 2)]
  rw [show (1 / 2 : ℝ) * (1 / 2) = 1 / 4 by norm_num]
  ring_nf
  rw [hXsq, mul_assoc, hNdc]
  ring

end Work.KMTAreas.A4
