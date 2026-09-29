import Mathlib.Algebra.Order.Star.Real

namespace Commons.Analysis.Real

/-- One-variable core of the cube-kernel bound: for `0 ≤ u ≤ 1`,
  `9 * u ^ 2 * (1 - u ^ 3) ^ 2 ≤ (1 + u ^ 2 + u ^ 4) ^ 2`.
  It follows by squaring `3 * u * (1 - u ^ 3) ≤ 1 + u ^ 2 + u ^ 4`, whose
  difference factors as `(2 * u - 1) ^ 2 * (1 + u + u ^ 2)`. -/
private lemma cubeKernel_oneVar {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    9 * u ^ 2 * (1 - u ^ 3) ^ 2 ≤ (1 + u ^ 2 + u ^ 4) ^ 2 := by
  have h1m : 0 ≤ 1 - u ^ 3 := by
    rw [show 1 - u ^ 3 = (1 - u) * (1 + u + u ^ 2) by ring]
    exact mul_nonneg (by linarith) (by positivity)
  have hA : 0 ≤ 3 * u * (1 - u ^ 3) := by
    exact mul_nonneg (mul_nonneg (by norm_num) hu0) h1m
  have hB : 0 ≤ 1 + u ^ 2 + u ^ 4 := by positivity
  have hmain : 3 * u * (1 - u ^ 3) ≤ 1 + u ^ 2 + u ^ 4 := by
    calc
      3 * u * (1 - u ^ 3) = (1 + u ^ 2 + u ^ 4) - (2 * u - 1) ^ 2 * (1 + u + u ^ 2) := by ring
      _ ≤ 1 + u ^ 2 + u ^ 4 := by
        have hy : 0 ≤ (2 * u - 1) ^ 2 * (1 + u + u ^ 2) := by
          exact mul_nonneg (sq_nonneg _) (by positivity)
        linarith
  have hsq0 : (3 * u * (1 - u ^ 3)) ^ 2 ≤ (1 + u ^ 2 + u ^ 4) ^ 2 := by
    have habs : |3 * u * (1 - u ^ 3)| ≤ |1 + u ^ 2 + u ^ 4| := by
      rw [abs_of_nonneg hA, abs_of_nonneg hB]
      exact hmain
    exact sq_le_sq.mpr habs
  calc
    9 * u ^ 2 * (1 - u ^ 3) ^ 2 = (3 * u * (1 - u ^ 3)) ^ 2 := by ring
    _ ≤ (1 + u ^ 2 + u ^ 4) ^ 2 := hsq0

/-- For `0 ≤ s, t ≤ 1` we have
  `9 * s * t * (1 - s^3) * (1 - t^3) ≤ (1 + s*t + s^2*t^2)^2`,
  i.e. the kernel `9 s t (1-s³)(1-t³) / (1 + s t + s² t²)²` is bounded by `1`
  on the unit square (sharp at `s = t = 1/2`). -/
lemma cubeKernel_le {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    9 * s * t * (1 - s ^ 3) * (1 - t ^ 3) ≤ (1 + s * t + s ^ 2 * t ^ 2) ^ 2 := by
  let u : ℝ := Real.sqrt (s * t)
  have hu0 : 0 ≤ u := by simp [u]
  have hst0 : 0 ≤ s * t := mul_nonneg hs0 ht0
  have hu_sq : u ^ 2 = s * t := by simpa [u] using Real.sq_sqrt hst0
  have hst_le : s * t ≤ 1 := by
    calc
      s * t ≤ s * 1 := mul_le_mul_of_nonneg_left ht1 hs0
      _ = s := by ring
      _ ≤ 1 := hs1
  have hu_le1 : u ≤ 1 := by
    calc
      u = Real.sqrt (s * t) := by simp [u]
      _ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hst_le
      _ = 1 := Real.sqrt_one
  have hu6 : u ^ 6 = s ^ 3 * t ^ 3 := by
    calc
      u ^ 6 = (u ^ 2) ^ 3 := by ring
      _ = (s * t) ^ 3 := by rw [hu_sq]
      _ = s ^ 3 * t ^ 3 := by ring
  have hu4 : u ^ 4 = s ^ 2 * t ^ 2 := by
    calc
      u ^ 4 = (u ^ 2) ^ 2 := by ring
      _ = (s * t) ^ 2 := by rw [hu_sq]
      _ = s ^ 2 * t ^ 2 := by ring
  -- geometric-mean step: `s^3 + t^3 ≥ 2 * u^3` (AM-GM, u^2 = s*t)
  have hsq : (2 * u ^ 3) ^ 2 ≤ (s ^ 3 + t ^ 3) ^ 2 := by
    calc
      (2 * u ^ 3) ^ 2 = 4 * u ^ 6 := by ring
      _ = 4 * (s ^ 3 * t ^ 3) := by rw [hu6]
      _ = (s ^ 3 + t ^ 3) ^ 2 - (s ^ 3 - t ^ 3) ^ 2 := by ring
      _ ≤ (s ^ 3 + t ^ 3) ^ 2 := by
        have : 0 ≤ (s ^ 3 - t ^ 3) ^ 2 := sq_nonneg _
        linarith
  have hb0 : 0 ≤ s ^ 3 + t ^ 3 := by positivity
  have hfin : 2 * u ^ 3 ≤ s ^ 3 + t ^ 3 := le_of_sq_le_sq hsq hb0
  -- pinching step: `(1 - s^3)(1 - t^3) ≤ (1 - u^3)^2`
  have hpinch : (1 - s ^ 3) * (1 - t ^ 3) ≤ (1 - u ^ 3) ^ 2 := by
    calc
      (1 - s ^ 3) * (1 - t ^ 3) = 1 - (s ^ 3 + t ^ 3) + s ^ 3 * t ^ 3 := by ring
      _ = 1 - (s ^ 3 + t ^ 3) + u ^ 6 := by rw [← hu6]
      _ ≤ 1 - (s ^ 3 + t ^ 3) + u ^ 6 + ((s ^ 3 + t ^ 3) - 2 * u ^ 3) := by linarith
      _ = 1 - 2 * u ^ 3 + u ^ 6 := by ring
      _ = (1 - u ^ 3) ^ 2 := by ring
  have h9 : 0 ≤ 9 * u ^ 2 := by exact mul_nonneg (by norm_num) (sq_nonneg u)
  have h2 : 9 * u ^ 2 * (1 - s ^ 3) * (1 - t ^ 3) ≤ 9 * u ^ 2 * (1 - u ^ 3) ^ 2 := by
    calc
      9 * u ^ 2 * (1 - s ^ 3) * (1 - t ^ 3) = (9 * u ^ 2) * ((1 - s ^ 3) * (1 - t ^ 3)) := by ring
      _ ≤ (9 * u ^ 2) * (1 - u ^ 3) ^ 2 := mul_le_mul_of_nonneg_left hpinch h9
      _ = 9 * u ^ 2 * (1 - u ^ 3) ^ 2 := by ring
  have h3 : 9 * u ^ 2 * (1 - u ^ 3) ^ 2 ≤ (1 + u ^ 2 + u ^ 4) ^ 2 :=
    cubeKernel_oneVar hu0 hu_le1
  calc
    9 * s * t * (1 - s ^ 3) * (1 - t ^ 3) = (9 * (s * t)) * (1 - s ^ 3) * (1 - t ^ 3) := by ring
    _ = 9 * u ^ 2 * (1 - s ^ 3) * (1 - t ^ 3) := by
      rw [hu_sq.symm]
    _ ≤ 9 * u ^ 2 * (1 - u ^ 3) ^ 2 := h2
    _ ≤ (1 + u ^ 2 + u ^ 4) ^ 2 := h3
    _ = (1 + s * t + s ^ 2 * t ^ 2) ^ 2 := by
      rw [hu_sq, hu4]

end Commons.Analysis.Real