import Mathlib
import Submission.Work.ParamRays.Bottcher

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ParamRays

open Filter

/-- **A Böttcher coordinate is asymptotic to the identity along an escaping orbit.**

If `φ` is a Böttcher coordinate of `T_c` and `z` escapes, then the orbit of `z` leaves every
compact set, so the third clause of `IsDynBottcher` (`‖φ w - w‖ ≤ ε ‖w‖` for `w` near infinity)
applies to the orbit points.  Hence `|‖φ w‖ - ‖w‖| ≤ ‖φ w - w‖ ≤ ε ‖w‖`, which is exactly the
statement that the ratios `‖φ w‖ / ‖w‖` tend to `1`. -/
theorem IsDynBottcher_norm_div {c : ℂ} {φ : ℂ → ℂ} (h : Work.ParamRays.IsDynBottcher c φ)
    {z : ℂ} (hz : Work.ParamRays.Escaping c z) :
    Filter.Tendsto (fun n : ℕ =>
      ‖φ (Work.ParamRays.orbit c z n)‖ / ‖Work.ParamRays.orbit c z n‖)
      Filter.atTop (nhds 1) := by
  have hz' : Filter.Tendsto (fun n : ℕ => ‖orbit c z n‖) Filter.atTop Filter.atTop := hz
  -- an escaping orbit leaves every compact set
  have hcoc : Filter.Tendsto (fun n : ℕ => orbit c z n) Filter.atTop
      (Filter.cocompact ℂ) :=
    tendsto_cocompact_of_tendsto_dist_comp_atTop 0 (by simpa [dist_zero_right] using hz')
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  -- the asymptotic clause of the Böttcher coordinate, evaluated along the orbit
  have hP : ∀ᶠ w : ℂ in Filter.cocompact ℂ, ‖φ w - w‖ ≤ ε / 2 * ‖w‖ := h.2.2 (ε / 2) hε2
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      ‖φ (orbit c z n) - orbit c z n‖ ≤ ε / 2 * ‖orbit c z n‖ := hcoc.eventually hP
  -- eventually the orbit point is far from the origin, so we may divide by its norm
  have hbig : ∀ᶠ n : ℕ in Filter.atTop, (1 : ℝ) ≤ ‖orbit c z n‖ :=
    hz'.eventually_ge_atTop 1
  filter_upwards [hev, hbig] with n hn hb
  have hbpos : 0 < ‖orbit c z n‖ := lt_of_lt_of_le zero_lt_one hb
  have hdiff : |‖φ (orbit c z n)‖ - ‖orbit c z n‖| ≤ ε / 2 * ‖orbit c z n‖ :=
    le_trans (abs_norm_sub_norm_le _ _) hn
  rw [Real.dist_eq, div_sub_one (ne_of_gt hbpos), abs_div, abs_of_pos hbpos,
    div_lt_iff₀ hbpos]
  nlinarith [hdiff, hbpos, hε]

end Work.ParamRays
