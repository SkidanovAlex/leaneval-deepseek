import Mathlib

namespace Work.KMTAreas.A4Z

/-- `rpow` bookkeeping for the `ℓ^p` major-arc bound of Area A4Z.

With `δ ∈ (0,1]`, `Nd > 0`, `CL > 0`, `p > 1` and the exponent hypothesis
`1/2 ≤ (1 + K₁)/p - K₁` one has

`(δ Nd)^{1/p} · ((4CL+2) δ^{-K₁})^{1-1/p} ≤ (4CL+3) δ^{1/2} Nd^{1/p}`.

Proof: write `e = 1 - 1/p ∈ (0,1)`.  Expanding the products gives
`δ^{1/p - K₁ e} · (4CL+2)^e · Nd^{1/p}`.  The exponent hypothesis is exactly
`1/2 ≤ 1/p - K₁ e = (1+K₁)/p - K₁`, so `δ^{1/p - K₁ e} ≤ δ^{1/2}` because
`δ ≤ 1`; and `(4CL+2)^e ≤ 4CL+2 ≤ 4CL+3` because the base is `> 1` and the
exponent is `≤ 1`. -/
theorem rpow_prod_le {δ Nd CL K₁ p : ℝ} (hδ : 0 < δ) (hNd : 0 < Nd) (hCL : 0 < CL)
    (hp : 1 < p) (hexp : 1 / 2 ≤ (1 + K₁) / p - K₁) (hδ1 : δ ≤ 1) :
    (δ * Nd) ^ (1 / p) * ((4 * CL + 2) * δ ^ (-K₁)) ^ (1 - 1 / p)
      ≤ (4 * CL + 3) * δ ^ (1 / 2 : ℝ) * Nd ^ (1 / p) := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hpne : p ≠ 0 := ne_of_gt hp0
  have he1 : 1 - 1 / p ≤ 1 := by
    have : (0 : ℝ) < 1 / p := by positivity
    linarith
  have h1lt : (1 : ℝ) < 4 * CL + 2 := by linarith
  have h1 : (δ * Nd) ^ (1 / p) = δ ^ (1 / p) * Nd ^ (1 / p) := Real.mul_rpow hδ.le hNd.le
  have h2 : ((4 * CL + 2) * δ ^ (-K₁)) ^ (1 - 1 / p)
      = (4 * CL + 2) ^ (1 - 1 / p) * δ ^ (-K₁ * (1 - 1 / p)) := by
    rw [Real.mul_rpow (by linarith) (Real.rpow_nonneg hδ.le _), ← Real.rpow_mul hδ.le]
  have h3 : δ ^ (1 / p) * δ ^ (-K₁ * (1 - 1 / p)) = δ ^ ((1 + K₁) / p - K₁) := by
    rw [← Real.rpow_add hδ]
    congr 1
    field_simp
    ring
  have hbase : (4 * CL + 2) ^ (1 - 1 / p) ≤ 4 * CL + 3 := by
    calc (4 * CL + 2) ^ (1 - 1 / p) ≤ (4 * CL + 2) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1lt.le he1
      _ = 4 * CL + 2 := Real.rpow_one _
      _ ≤ 4 * CL + 3 := by linarith
  have hδmono : δ ^ ((1 + K₁) / p - K₁) ≤ δ ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hexp
  have hgoal : (δ * Nd) ^ (1 / p) * ((4 * CL + 2) * δ ^ (-K₁)) ^ (1 - 1 / p)
      = (4 * CL + 2) ^ (1 - 1 / p) * δ ^ ((1 + K₁) / p - K₁) * Nd ^ (1 / p) := by
    rw [h1, h2,
      show δ ^ (1 / p) * Nd ^ (1 / p)
            * ((4 * CL + 2) ^ (1 - 1 / p) * δ ^ (-K₁ * (1 - 1 / p)))
          = (4 * CL + 2) ^ (1 - 1 / p)
            * (δ ^ (1 / p) * δ ^ (-K₁ * (1 - 1 / p))) * Nd ^ (1 / p) by ring,
      h3]
  rw [hgoal]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hbase hδmono (Real.rpow_nonneg hδ.le _) (by linarith))
    (Real.rpow_nonneg hNd.le _)

end Work.KMTAreas.A4Z
