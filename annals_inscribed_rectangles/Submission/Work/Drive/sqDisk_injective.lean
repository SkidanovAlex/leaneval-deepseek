import Mathlib
import Submission.Work.Drive.squareDisk

/-!
# Injectivity of the square-to-disk map on the unit square

`Work.Drive.sqDisk` is the classical square-to-disk map

> `sqDisk y = (a·√(1 − b²/2), b·√(1 − a²/2))`,  `a = 2 y 0 − 1`,  `b = 2 y 1 − 1`,

written with the smooth cut-off weight `sqWeight` (`Submission/Work/Drive/squareDisk.lean`).  On the
unit square `[0,1]²` this file proves that it is injective: the cubical presentation of the disk used
by the parity bookkeeping of the chain route identifies (at most) the two points of the boundary that
are interchanged by the antipodal involution, and no others.

The mathematical content is the elementary observation that the map `(u,v) ↦ (u(1−v/2), v(1−u/2))`
on `[0,1]²` is injective: subtracting the two coordinates recovers `u − v`, and adding them recovers
`1 − (1−u)(1−v)`, which determines `(1−u)+(1−v) ≥ 0` from the square of that quantity.
-/

namespace Work.Drive

/-- **Injectivity of the model map.**  If `0 ≤ u,v,u',v' ≤ 1` are such that
`u(1−v/2) = u'(1−v'/2)` and `v(1−u/2) = v'(1−u'/2)`, then `u = u'` and `v = v'`.

(The hypotheses used are only the upper bounds `u,v,u',v' ≤ 1`.) -/
lemma sq_weight_inj_aux {u v u' v' : ℝ}
    (hu : u ≤ 1) (hv : v ≤ 1) (hu' : u' ≤ 1) (hv' : v' ≤ 1)
    (hX : u * (1 - v / 2) = u' * (1 - v' / 2))
    (hY : v * (1 - u / 2) = v' * (1 - u' / 2)) :
    u = u' ∧ v = v' := by
  -- the difference of the two equations is `u - v = u' - v'`
  have hP : u - v = u' - v' := by linarith
  -- the sum of the two equations is `u + v - uv = u' + v' - u'v'`, i.e. `(1-u)(1-v) = (1-u')(1-v')`
  have hQ : u + v - u * v = u' + v' - u' * v' := by linarith
  have hdiff : (1 - u) - (1 - v) = (1 - u') - (1 - v') := by linarith
  have hprod : (1 - u) * (1 - v) = (1 - u') * (1 - v') := by nlinarith [hQ]
  -- hence `((1-u)+(1-v))² = ((1-u')+(1-v'))²`, and both sums are non-negative
  have hsum : (1 - u) + (1 - v) = (1 - u') + (1 - v') := by
    have hsq : ((1 - u) + (1 - v)) ^ 2 = ((1 - u') + (1 - v')) ^ 2 := by
      nlinarith [hdiff, hprod]
    have h1 : 0 ≤ (1 - u) + (1 - v) := by linarith
    have h2 : 0 ≤ (1 - u') + (1 - v') := by linarith
    have := (sq_eq_sq_iff_abs_eq_abs _ _).mp hsq
    rwa [abs_of_nonneg h1, abs_of_nonneg h2] at this
  constructor <;> linarith

/-- **The square-to-disk map is injective on the unit square.** -/
theorem sqDisk_injective (y y' : EuclideanSpace ℝ (Fin 2))
    (hy : y ∈ Submission.Drive.unitBox 1) (hy' : y' ∈ Submission.Drive.unitBox 1)
    (h : Work.Drive.sqDisk y = Work.Drive.sqDisk y') : y = y' := by
  have h0 := abs_two_mul_sub_one_le_one hy 0
  have h1 := abs_two_mul_sub_one_le_one hy 1
  have h0' := abs_two_mul_sub_one_le_one hy' 0
  have h1' := abs_two_mul_sub_one_le_one hy' 1
  -- read off the real and imaginary parts of the equality
  have hre : (2 * y 0 - 1) * sqWeight (2 * y 1 - 1)
      = (2 * y' 0 - 1) * sqWeight (2 * y' 1 - 1) := by
    have := congrArg Complex.re h
    simpa using this
  have him : (2 * y 1 - 1) * sqWeight (2 * y 0 - 1)
      = (2 * y' 1 - 1) * sqWeight (2 * y' 0 - 1) := by
    have := congrArg Complex.im h
    simpa using this
  -- square them and use `sqWeight b ^ 2 = 1 - b^2/2` on `[-1,1]`
  have hX : (2 * y 0 - 1) ^ 2 * (1 - (2 * y 1 - 1) ^ 2 / 2)
      = (2 * y' 0 - 1) ^ 2 * (1 - (2 * y' 1 - 1) ^ 2 / 2) := by
    have := congrArg (fun t : ℝ => t ^ 2) hre
    rw [mul_pow, mul_pow, sqWeight_sq h1, sqWeight_sq h1'] at this
    exact this
  have hY : (2 * y 1 - 1) ^ 2 * (1 - (2 * y 0 - 1) ^ 2 / 2)
      = (2 * y' 1 - 1) ^ 2 * (1 - (2 * y' 0 - 1) ^ 2 / 2) := by
    have := congrArg (fun t : ℝ => t ^ 2) him
    rw [mul_pow, mul_pow, sqWeight_sq h0, sqWeight_sq h0'] at this
    exact this
  have hb0 : (2 * y 0 - 1) ^ 2 ≤ 1 := by
    have := abs_le.mp h0; nlinarith [this.1, this.2]
  have hb1 : (2 * y 1 - 1) ^ 2 ≤ 1 := by
    have := abs_le.mp h1; nlinarith [this.1, this.2]
  have hb0' : (2 * y' 0 - 1) ^ 2 ≤ 1 := by
    have := abs_le.mp h0'; nlinarith [this.1, this.2]
  have hb1' : (2 * y' 1 - 1) ^ 2 ≤ 1 := by
    have := abs_le.mp h1'; nlinarith [this.1, this.2]
  obtain ⟨hA2, hB2⟩ := sq_weight_inj_aux hb0 hb1 hb0' hb1' hX hY
  -- the weight only depends on `b ^ 2`, so the two weights agree
  have hwB : sqWeight (2 * y 1 - 1) = sqWeight (2 * y' 1 - 1) := by
    have hsq : sqWeight (2 * y 1 - 1) ^ 2 = sqWeight (2 * y' 1 - 1) ^ 2 := by
      rw [sqWeight_sq h1, sqWeight_sq h1', hB2]
    have := (sq_eq_sq_iff_abs_eq_abs _ _).mp hsq
    rwa [abs_of_nonneg (sqWeight_nonneg _), abs_of_nonneg (sqWeight_nonneg _)] at this
  have hwA : sqWeight (2 * y 0 - 1) = sqWeight (2 * y' 0 - 1) := by
    have hsq : sqWeight (2 * y 0 - 1) ^ 2 = sqWeight (2 * y' 0 - 1) ^ 2 := by
      rw [sqWeight_sq h0, sqWeight_sq h0', hA2]
    have := (sq_eq_sq_iff_abs_eq_abs _ _).mp hsq
    rwa [abs_of_nonneg (sqWeight_nonneg _), abs_of_nonneg (sqWeight_nonneg _)] at this
  -- cancel the (strictly positive) weights
  have hAeq : 2 * y 0 - 1 = 2 * y' 0 - 1 := by
    rw [← hwB] at hre
    exact mul_right_cancel₀ (ne_of_gt (sqWeight_pos h1)) hre
  have hBeq : 2 * y 1 - 1 = 2 * y' 1 - 1 := by
    rw [← hwA] at him
    exact mul_right_cancel₀ (ne_of_gt (sqWeight_pos h0)) him
  have hAeq' : y 0 = y' 0 := by linarith
  have hBeq' : y 1 = y' 1 := by linarith
  ext1 i
  fin_cases i
  · exact hAeq'
  · exact hBeq'

end Work.Drive
