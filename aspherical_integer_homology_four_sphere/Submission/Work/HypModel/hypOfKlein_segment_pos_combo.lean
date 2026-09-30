import Mathlib
import Submission.Work.HypModel.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.HypModel

/-- The open unit ball (the Klein model) is convex, hence contains every segment joining two of its
points. -/
theorem ball_convex : Convex ℝ (ball : Set E4) := by
  have h : (ball : Set E4) = Metric.ball (0 : E4) 1 := by
    ext x; simp [ball, Metric.ball, dist_eq_norm]
  rw [h]; exact convex_ball 0 1

/-- `ray` is an affine map with respect to the last (`= 1`) coordinate: the ray of a convex
combination is the corresponding combination of rays. -/
theorem ray_convex_combo {y z : E4} {t : ℝ} (ht : (1 - t) + t = 1) :
    (1 - t) • ray y + t • ray z = ray ((1 - t) • y + t • z) := by
  ext i
  fin_cases i <;> simp [ray, ht]

/-- The Klein-lift of a convex combination in the ball is a nonnegative combination of the
Klein-lifts of the endpoints: the segment of the Klein model maps into the cone spanned by the two
lifts.  Explicitly, with `s w = √(1 - ‖w‖²)`, one has
`hypOfKlein w = (s y · (1−t) / s w) • hypOfKlein y + (s z · t / s w) • hypOfKlein z`. -/
theorem hypOfKlein_segment_pos_combo {y z : E4} (hy : y ∈ ball) (hz : z ∈ ball) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧
      hypOfKlein ((1 - t) • y + t • z) = a • hypOfKlein y + b • hypOfKlein z := by
  have hy1 : ‖y‖ < 1 := hy
  have hz1 : ‖z‖ < 1 := hz
  have hw_ball : (1 - t) • y + t • z ∈ ball :=
    (convex_iff_add_mem.mp ball_convex) hy hz (by linarith) ht0 (by ring)
  have hw1 : ‖(1 - t) • y + t • z‖ < 1 := hw_ball
  have hsy : 0 < Real.sqrt (1 - ‖y‖ ^ 2) := by
    apply Real.sqrt_pos_of_pos; nlinarith [norm_nonneg y, hy1]
  have hsz : 0 < Real.sqrt (1 - ‖z‖ ^ 2) := by
    apply Real.sqrt_pos_of_pos; nlinarith [norm_nonneg z, hz1]
  have hsw : 0 < Real.sqrt (1 - ‖(1 - t) • y + t • z‖ ^ 2) := by
    apply Real.sqrt_pos_of_pos; nlinarith [norm_nonneg ((1 - t) • y + t • z), hw1]
  refine ⟨Real.sqrt (1 - ‖y‖ ^ 2) * (1 - t) / Real.sqrt (1 - ‖(1 - t) • y + t • z‖ ^ 2),
          Real.sqrt (1 - ‖z‖ ^ 2) * t / Real.sqrt (1 - ‖(1 - t) • y + t • z‖ ^ 2),
          div_nonneg (mul_nonneg hsy.le (by linarith)) hsw.le,
          div_nonneg (mul_nonneg hsz.le ht0) hsw.le, ?_⟩
  have hray : (1 - t) • ray y + t • ray z = ray ((1 - t) • y + t • z) :=
    ray_convex_combo (by ring)
  simp only [hypOfKlein]
  rw [smul_smul, smul_smul]
  have ha : Real.sqrt (1 - ‖y‖ ^ 2) * (1 - t) / Real.sqrt (1 - ‖(1 - t) • y + t • z‖ ^ 2) *
        (Real.sqrt (1 - ‖y‖ ^ 2))⁻¹
      = (1 - t) / Real.sqrt (1 - ‖(1 - t) • y + t • z‖ ^ 2) := by
    field_simp
  have hb : Real.sqrt (1 - ‖z‖ ^ 2) * t / Real.sqrt (1 - ‖(1 - t) • y + t • z‖ ^ 2) *
        (Real.sqrt (1 - ‖z‖ ^ 2))⁻¹
      = t / Real.sqrt (1 - ‖(1 - t) • y + t • z‖ ^ 2) := by
    field_simp
  rw [ha, hb, ← hray, smul_add, smul_smul, smul_smul]
  rw [show (Real.sqrt (1 - ‖(1 - t) • y + t • z‖ ^ 2))⁻¹ * (1 - t)
        = (1 - t) / Real.sqrt (1 - ‖(1 - t) • y + t • z‖ ^ 2) from by ring,
      show (Real.sqrt (1 - ‖(1 - t) • y + t • z‖ ^ 2))⁻¹ * t
        = t / Real.sqrt (1 - ‖(1 - t) • y + t • z‖ ^ 2) from by ring]

end Work.HypModel
