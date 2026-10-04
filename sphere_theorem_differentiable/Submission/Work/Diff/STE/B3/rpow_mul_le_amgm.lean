import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

/-- Weighted AM-GM in the exponents that occur in the sharp Gagliardo–Nirenberg estimate: for
nonnegative `u, v`, natural numbers `a, b ≥ 1` with `a + b = k` (`k ≥ 1`),
`(u * v) ^ (2m/k) ≤ (a/k) * u ^ (2m/a) + (b/k) * v ^ (2m/b)`. -/
theorem rpow_mul_le_amgm {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    {m k a b : ℕ} (hk : 1 ≤ k) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a + b = k) :
    (u * v) ^ ((2 * (m : ℝ)) / (k : ℝ))
      ≤ ((a : ℝ) / (k : ℝ)) * u ^ ((2 * (m : ℝ)) / (a : ℝ))
        + ((b : ℝ) / (k : ℝ)) * v ^ ((2 * (m : ℝ)) / (b : ℝ)) := by
  -- The weights `a/k` and `b/k` are nonnegative and sum to `1` (using `hab` and `hk`).
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hla : 0 ≤ (a : ℝ) / (k : ℝ) := by positivity
  have hmu : 0 ≤ (b : ℝ) / (k : ℝ) := by positivity
  have hsum : (a : ℝ) / (k : ℝ) + (b : ℝ) / (k : ℝ) = 1 := by
    rw [← add_div, ← Nat.cast_add, hab, div_self hk0]
  -- Weighted AM-GM applied to `X := u ^ (2m/a)` and `Y := v ^ (2m/b)`.
  have key :
      (u ^ ((2 * (m : ℝ)) / (a : ℝ))) ^ ((a : ℝ) / (k : ℝ)) *
          (v ^ ((2 * (m : ℝ)) / (b : ℝ))) ^ ((b : ℝ) / (k : ℝ))
        ≤ ((a : ℝ) / (k : ℝ)) * u ^ ((2 * (m : ℝ)) / (a : ℝ))
          + ((b : ℝ) / (k : ℝ)) * v ^ ((2 * (m : ℝ)) / (b : ℝ)) :=
    Real.geom_mean_le_arith_mean2_weighted hla hmu
      (Real.rpow_nonneg hu _) (Real.rpow_nonneg hv _) hsum
  -- The exponent `(2m/a)·(a/k)` collapses to `2m/k` (and likewise with `b`).
  have hX : (u ^ ((2 * (m : ℝ)) / (a : ℝ))) ^ ((a : ℝ) / (k : ℝ))
      = u ^ ((2 * (m : ℝ)) / (k : ℝ)) := by
    rw [← Real.rpow_mul hu]
    congr 1
    field_simp
  have hY : (v ^ ((2 * (m : ℝ)) / (b : ℝ))) ^ ((b : ℝ) / (k : ℝ))
      = v ^ ((2 * (m : ℝ)) / (k : ℝ)) := by
    rw [← Real.rpow_mul hv]
    congr 1
    field_simp
  calc (u * v) ^ ((2 * (m : ℝ)) / (k : ℝ))
      = u ^ ((2 * (m : ℝ)) / (k : ℝ)) * v ^ ((2 * (m : ℝ)) / (k : ℝ)) :=
        Real.mul_rpow hu hv
    _ = (u ^ ((2 * (m : ℝ)) / (a : ℝ))) ^ ((a : ℝ) / (k : ℝ)) *
          (v ^ ((2 * (m : ℝ)) / (b : ℝ))) ^ ((b : ℝ) / (k : ℝ)) := by rw [hX, hY]
    _ ≤ ((a : ℝ) / (k : ℝ)) * u ^ ((2 * (m : ℝ)) / (a : ℝ))
          + ((b : ℝ) / (k : ℝ)) * v ^ ((2 * (m : ℝ)) / (b : ℝ)) := key

end Work.Diff.STE.B3
