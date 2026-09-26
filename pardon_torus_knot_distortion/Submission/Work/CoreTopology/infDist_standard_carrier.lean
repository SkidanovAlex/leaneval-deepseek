import Submission.Work.CoreTopology.torusHeight_eq_one_iff

/-!
# The distance to the standard torus

For a point `x ∈ ℝ³` with `r = √(x 0² + x 1²)` the standard torus of revolution
`Σ = standard.carrier` is the surface of revolution of the circle of radius `1` about `(2,0)` in
the `(r, z)`-half-plane.  Hence

`dist (x, Σ) = |√(torusHeight x) - 1|`,

where `torusHeight x = (r - 2)² + x 2²` is the squared distance of `(r, x 2)` to `(2,0)`.

This is the quantitative form of `torusHeight_eq_one_iff`: it turns "off the torus" into a
positive lower bound on `|√(torusHeight ·) - 1|`, which is what the collar argument for pushing
a disc off the standard torus needs.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.CoreTopology

noncomputable section

set_option maxHeartbeats 1000000

/-- The height function is nonnegative. -/
theorem torusHeight_nonneg (x : R3) : 0 ≤ torusHeight x := by
  rw [torusHeight_apply]; positivity

/-- The carrier of the standard torus is nonempty. -/
theorem standard_carrier_nonempty : standard.carrier.Nonempty :=
  ⟨_, ParamTorus.psi_mem_carrier standard 0 0⟩

/-- The coordinates of the standard parametrisation. -/
theorem torusMap_coord_zero (θ φ : ℝ) :
    (Work.Core.torusMap θ φ) 0 = (2 + Real.cos φ) * Real.cos θ := by
  simp [Work.Core.torusMap]

theorem torusMap_coord_one (θ φ : ℝ) :
    (Work.Core.torusMap θ φ) 1 = (2 + Real.cos φ) * Real.sin θ := by
  simp [Work.Core.torusMap]

theorem torusMap_coord_two (θ φ : ℝ) : (Work.Core.torusMap θ φ) 2 = Real.sin φ := by
  simp [Work.Core.torusMap]

/-- **The two-dimensional Cauchy–Schwarz step.** -/
theorem horiz_mul_cos_add_mul_sin_le (x : R3) (θ : ℝ) :
    x 0 * Real.cos θ + x 1 * Real.sin θ ≤ horizRadius x := by
  have h1 : horizRadius x ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
    rw [horizRadius_sq, horizRadiusSq_apply]
  have h2 : 0 ≤ (x 0 * Real.sin θ - x 1 * Real.cos θ) ^ 2 := sq_nonneg _
  have h3 : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  have h4 : (x 0 * Real.cos θ + x 1 * Real.sin θ) ^ 2 ≤ horizRadius x ^ 2 := by
    rw [h1]; nlinarith [h2, h3]
  have h5 : 0 ≤ horizRadius x := Real.sqrt_nonneg _
  nlinarith [h4, h5]

/-- The squared distance from `x` to a point of the torus, split off the azimuthal error. -/
theorem norm_sub_torusMap_sq (x : R3) (θ φ : ℝ) :
    ‖x - Work.Core.torusMap θ φ‖ ^ 2
      = (horizRadius x - (2 + Real.cos φ)) ^ 2 + (x 2 - Real.sin φ) ^ 2
        + 2 * (2 + Real.cos φ)
            * (horizRadius x - (x 0 * Real.cos θ + x 1 * Real.sin θ)) := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp only [PiLp.sub_apply, torusMap_coord_zero, torusMap_coord_one, torusMap_coord_two,
    Real.norm_eq_abs, sq_abs]
  have h1 : horizRadius x ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
    rw [horizRadius_sq, horizRadiusSq_apply]
  have h3 : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  linear_combination -h1 + (2 + Real.cos φ) ^ 2 * h3

/-- The planar fact: a point of the circle of radius `1` about `(2,0)` is at distance at least
`|√((r-2)²+z²) - 1|` from `(r,z)`, by the reverse triangle inequality. -/
theorem circle_dist_le (r z a s : ℝ) (hq : (a - 2) ^ 2 + s ^ 2 = 1) :
    (Real.sqrt ((r - 2) ^ 2 + z ^ 2) - 1) ^ 2 ≤ (r - a) ^ 2 + (z - s) ^ 2 := by
  have hu : Real.sqrt ((r - 2) ^ 2 + z ^ 2) ^ 2 = (r - 2) ^ 2 + z ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hv : (1:ℝ) ^ 2 = (a - 2) ^ 2 + s ^ 2 := by rw [hq]; norm_num
  have hcs : (r - 2) * (a - 2) + z * s ≤ Real.sqrt ((r - 2) ^ 2 + z ^ 2) := by
    have hl : ((r - 2) * (a - 2) + z * s) ^ 2 ≤ ((r - 2) ^ 2 + z ^ 2) * 1 := by
      nlinarith [sq_nonneg ((r - 2) * s - z * (a - 2)), hq]
    have hu' := Real.sq_sqrt (show (0:ℝ) ≤ (r - 2) ^ 2 + z ^ 2 by positivity)
    have hs0 : 0 ≤ Real.sqrt ((r - 2) ^ 2 + z ^ 2) := Real.sqrt_nonneg _
    nlinarith [hl, hu', hs0]
  nlinarith [hcs, hu, hv]

/-- A point of the unit circle of `ℂ` is `(cos θ, sin θ)` for some `θ`. -/
theorem exists_cos_sin_eq {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) :
    ∃ θ : ℝ, Real.cos θ = c ∧ Real.sin θ = s := by
  refine exists_cos_sin_of_normSq_eq_one ⟨c, s⟩ ?_
  rw [Complex.normSq_apply]
  simpa [sq] using h

/-- The horizontal radius squared. -/
theorem horizRadius_sq_coord (x : R3) : horizRadius x ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [horizRadius_sq, horizRadiusSq_apply]

/-- **The lower bound: no torus point is closer than `|√torusHeight - 1|`.** -/
theorem le_infDist_standard_carrier (x : R3) :
    |Real.sqrt (torusHeight x) - 1| ≤ Metric.infDist x standard.carrier := by
  rw [Metric.le_infDist standard_carrier_nonempty]
  intro y hy
  obtain ⟨θ, φ, hφ⟩ := (ParamTorus.mem_carrier_iff standard y).mp hy
  rw [← hφ, standard_psi, dist_eq_norm]
  have hsq := norm_sub_torusMap_sq x θ φ
  have ha : 0 ≤ 2 + Real.cos φ := by linarith [Real.neg_one_le_cos φ]
  have hcs := horiz_mul_cos_add_mul_sin_le x θ
  have h2 : (horizRadius x - (2 + Real.cos φ)) ^ 2 + (x 2 - Real.sin φ) ^ 2
      ≤ ‖x - Work.Core.torusMap θ φ‖ ^ 2 := by
    rw [hsq]; nlinarith [ha, hcs]
  have h3 : (Real.sqrt (torusHeight x) - 1) ^ 2
      ≤ (horizRadius x - (2 + Real.cos φ)) ^ 2 + (x 2 - Real.sin φ) ^ 2 := by
    have hq : ((2 + Real.cos φ) - 2) ^ 2 + Real.sin φ ^ 2 = 1 := by
      have := Real.cos_sq_add_sin_sq φ; nlinarith [this]
    have hcl := circle_dist_le (horizRadius x) (x 2) (2 + Real.cos φ) (Real.sin φ) hq
    simpa only [torusHeight_apply] using hcl
  have h4 : |Real.sqrt (torusHeight x) - 1| ^ 2
      ≤ ‖x - Work.Core.torusMap θ φ‖ ^ 2 := by
    rw [sq_abs]; exact le_trans h3 h2
  have h5 : 0 ≤ ‖x - Work.Core.torusMap θ φ‖ := norm_nonneg _
  nlinarith [h4, h5]

/-- **The distance from a point of `ℝ³` to the standard torus of revolution.**
`dist(x, standard.carrier) = |√(torusHeight x) - 1|`. -/
theorem infDist_standard_carrier (x : R3) :
    Metric.infDist x standard.carrier = |Real.sqrt (torusHeight x) - 1| := by
  refine le_antisymm ?_ (le_infDist_standard_carrier x)
  have h1 : horizRadius x ^ 2 = x 0 ^ 2 + x 1 ^ 2 := horizRadius_sq_coord x
  have ht2 : Real.sqrt (torusHeight x) ^ 2 = torusHeight x := Real.sq_sqrt (torusHeight_nonneg x)
  set r := horizRadius x with hr
  set u := x 2 with hu
  set t := Real.sqrt (torusHeight x) with htt
  have ht20 : t ^ 2 = (r - 2) ^ 2 + u ^ 2 := by
    rw [htt, ht2, torusHeight_apply]
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  set a : ℝ := if t = 0 then 1 else 2 + (r - 2) / t with ha
  set s : ℝ := if t = 0 then 0 else u / t with hs
  have hq : (a - 2) ^ 2 + s ^ 2 = 1 := by
    rcases eq_or_ne t 0 with h0 | h0
    · have h2 : (r - 2) ^ 2 + u ^ 2 = 0 := by rw [← ht20, h0]; norm_num
      have hr2 : r = 2 := by nlinarith [sq_nonneg (r - 2), sq_nonneg u]
      simp only [ha, hs, if_pos h0]
      norm_num
    · simp only [ha, hs, if_neg h0]
      field_simp
      nlinarith [ht20]
  have hp : (r - a) ^ 2 + (u - s) ^ 2 = (t - 1) ^ 2 := by
    rcases eq_or_ne t 0 with h0 | h0
    · have h2 : (r - 2) ^ 2 + u ^ 2 = 0 := by rw [← ht20, h0]; norm_num
      have hr2 : r = 2 := by nlinarith [sq_nonneg (r - 2), sq_nonneg u]
      have hu0 : u = 0 := by nlinarith [sq_nonneg (r - 2), sq_nonneg u]
      simp only [ha, hs, if_pos h0]
      rw [h0, hr2, hu0]
      norm_num
    · simp only [ha, hs, if_neg h0]
      field_simp
      nlinarith [ht20]
  obtain ⟨φ, hcos, hsin⟩ := exists_cos_sin_eq hq
  -- the azimuth: only the scalar identity is needed
  have hθex : ∃ θ : ℝ, x 0 * Real.cos θ + x 1 * Real.sin θ = r := by
    by_cases hr0 : r = 0
    · have hx0 : x 0 = 0 := by
        have hs1 : x 0 ^ 2 = 0 := by nlinarith [h1, hr0, sq_nonneg (x 1)]
        exact sq_eq_zero_iff.mp hs1
      have hx1 : x 1 = 0 := by
        have hs1 : x 1 ^ 2 = 0 := by nlinarith [h1, hr0, sq_nonneg (x 0)]
        exact sq_eq_zero_iff.mp hs1
      exact ⟨0, by simp [hx0, hx1, hr0]⟩
    · have h2 : (x 0 / r) ^ 2 + (x 1 / r) ^ 2 = 1 := by
        field_simp
        nlinarith [h1]
      obtain ⟨θ, hc, hs⟩ := exists_cos_sin_eq h2
      refine ⟨θ, ?_⟩
      rw [hc, hs]
      field_simp
      nlinarith [h1]
  obtain ⟨θ, hθr⟩ := hθex
  rw [Metric.infDist_eq_iInf]
  have hmem : Work.Core.torusMap θ φ ∈ standard.carrier := ⟨(θ, φ), rfl⟩
  refine le_trans (ciInf_le ⟨0, by rintro _ ⟨y, rfl⟩; exact dist_nonneg⟩ ⟨_, hmem⟩) ?_
  rw [dist_eq_norm]
  change ‖x - Work.Core.torusMap θ φ‖ ≤ |t - 1|
  have hcoord0 : (Work.Core.torusMap θ φ) 0 = a * Real.cos θ := by
    rw [torusMap_coord_zero, hcos]; ring
  have hcoord1 : (Work.Core.torusMap θ φ) 1 = a * Real.sin θ := by
    rw [torusMap_coord_one, hcos]; ring
  have hcoord2 : (Work.Core.torusMap θ φ) 2 = s := by rw [torusMap_coord_two, hsin]
  have hnorm2 : ‖x - Work.Core.torusMap θ φ‖ ^ 2 = (t - 1) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    simp only [PiLp.sub_apply, hcoord0, hcoord1, hcoord2, Real.norm_eq_abs, sq_abs]
    have hcq : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
    linear_combination -h1 + a ^ 2 * hcq + (-2 * a) * hθr + hp
  rw [← Real.sqrt_sq_eq_abs (t - 1), ← hnorm2, Real.sqrt_sq (norm_nonneg _)]

end

end Work.CoreTopology
