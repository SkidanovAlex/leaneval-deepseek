import Mathlib
import Submission.Work.A14.defs

namespace Work.A14D

open Complex Metric

/-!
# `Work.A14D.geom_halfball_cover`

Elementary covering statement for the half-balls around `1`: for `δ ≤ 1` the upper (resp. lower)
half of `ball 1 δ` is covered by the unit disc together with the half-plane
`SU = {(1 − Re z)/8 < Im z}` (resp. `SL = {Im z < (Re z − 1)/8}`).

The point is that `SU` and `SL` are convex, `LZ`-regular, and meet the unit disc; when the
continuation of `Hfun` on `SU`/`SL` is glued to the disc solution, exactly the overlap region
`ball 1 δ ∩ ball 0 1` needs the two functions to agree, and outside that overlap the point already
lies in the half-plane.

Concretely, a point `z` of `ball 1 δ` is already in the unit disc as soon as `Re z ∈ (0, 1)` and its
imaginary part obeys the (opposite of the) half-plane inequality with the correct sign:
`(Im z)² ≤ ((1 − Re z)/8)²` forces `Re z ² + Im z ² < 1`.  Since `‖z − 1‖ < δ ≤ 1` gives
`Re z ∈ (0, 2)`, and either the half-plane inequality or its negation holds, the cover follows.
-/

/-- A point of a ball of radius `≤ 1` around `1` has positive real part. -/
private lemma re_pos_of_mem_ball {z : ℂ} {δ : ℝ} (hδ : δ ≤ 1)
    (hz : z ∈ Metric.ball (1 : ℂ) δ) : 0 < z.re := by
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have h : |z.re - 1| ≤ ‖z - 1‖ := by simpa using Complex.abs_re_le_norm (z - 1)
  have hlt : |z.re - 1| < 1 := lt_of_le_of_lt h (lt_of_lt_of_le hz hδ)
  rw [abs_lt] at hlt
  linarith [hlt.1]

/-- If `0 < Re z < 1` and `(Im z)² ≤ ((1 − Re z)/8)²`, then `‖z‖ < 1`.  The second hypothesis is
the (squared) complement of the half-plane condition, with either sign of the imaginary part. -/
private lemma norm_lt_one_of {z : ℂ} (h0 : 0 < z.re) (h1 : z.re < 1)
    (hs : z.im ^ 2 ≤ ((1 - z.re) / 8) ^ 2) : ‖z‖ < 1 := by
  have h2 : z.re ^ 2 + z.im ^ 2 < 1 := by nlinarith
  have h3 : ‖z‖ ^ 2 < 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith
  nlinarith [norm_nonneg z]

/-- A point in `ball 1 δ` (`δ ≤ 1`) with `0 < Im z` that is *not* in `SU` lies in the unit disc. -/
private lemma ball_zero_of_mem_upper {z : ℂ} (hre0 : 0 < z.re) (him : 0 < z.im)
    (hle : z.im ≤ (1 - z.re) / 8) : z ∈ Metric.ball (0 : ℂ) 1 := by
  have hz1 : z.re < 1 := by
    have : (0 : ℝ) < (1 - z.re) / 8 := lt_of_lt_of_le him hle
    linarith
  have hs : z.im ^ 2 ≤ ((1 - z.re) / 8) ^ 2 := by nlinarith
  rw [Metric.mem_ball, dist_zero_right]
  exact norm_lt_one_of hre0 hz1 hs

/-- A point in `ball 1 δ` (`δ ≤ 1`) with `Im z < 0` that is *not* in `SL` lies in the unit disc. -/
private lemma ball_zero_of_mem_lower {z : ℂ} (hre0 : 0 < z.re) (him : z.im < 0)
    (hle : (z.re - 1) / 8 ≤ z.im) : z ∈ Metric.ball (0 : ℂ) 1 := by
  have hz1 : z.re < 1 := by
    have : (0 : ℝ) < (1 - z.re) / 8 := by linarith
    linarith
  have hs : z.im ^ 2 ≤ ((1 - z.re) / 8) ^ 2 := by nlinarith [sq_nonneg (-z.im)]
  rw [Metric.mem_ball, dist_zero_right]
  exact norm_lt_one_of hre0 hz1 hs

theorem geom_halfball_cover {δ : ℝ} (hδ : δ ≤ 1) :
    (Metric.ball (1 : ℂ) δ ∩ {z : ℂ | 0 < z.im} ⊆ Metric.ball (0 : ℂ) 1 ∪ SU) ∧
    (Metric.ball (1 : ℂ) δ ∩ {z : ℂ | z.im < 0} ⊆ Metric.ball (0 : ℂ) 1 ∪ SL) := by
  constructor
  · rintro z ⟨hzball, hzim⟩
    have hre0 := re_pos_of_mem_ball hδ hzball
    by_cases hSU : (1 - z.re) / 8 < z.im
    · exact Or.inr hSU
    · exact Or.inl (ball_zero_of_mem_upper hre0 hzim (not_lt.mp hSU))
  · rintro z ⟨hzball, hzim⟩
    have hre0 := re_pos_of_mem_ball hδ hzball
    by_cases hSL : z.im < (z.re - 1) / 8
    · exact Or.inr hSL
    · exact Or.inl (ball_zero_of_mem_lower hre0 hzim (not_lt.mp hSL))

end Work.A14D
