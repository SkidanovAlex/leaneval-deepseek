import Mathlib
import Submission.Work.Drive.EpsForm.WaypointDesign2

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Drive.EpsForm

noncomputable section

/-! ## Elementary bounds used in the proof of `eFunX_tendsto_zero`

The second waypoint `W2c t` is always a point of the unit circle, so both of its coordinates
are bounded by `1` in absolute value; the first piece of the profile is the segment from
`W1 = (-2,0)` to `W2c t`, whose coordinates are therefore `O(s)` uniformly in `t`. -/

/-- The first coordinate of the second waypoint is bounded by `1`. -/
theorem W2c_abs_fst (t : ℝ) : |(W2c t).1| ≤ 1 := by
  by_cases h : inRange t <;> simp [W2c, W5c, h, Real.abs_cos_le_one]

/-- The second coordinate of the second waypoint is bounded by `1`. -/
theorem W2c_abs_snd (t : ℝ) : |(W2c t).2| ≤ 1 := by
  by_cases h : inRange t <;> simp [W2c, W5c, h, Real.abs_sin_le_one]

/-- The first coordinate of the segment from `W1 = (-2,0)` to `Q`, evaluated at level `s`
between `0` and `b`. -/
theorem seg_W1_fst (Q : ℝ × ℝ) (b s : ℝ) :
    (seg W1 Q 0 b s).1 = -2 + 2 * (s / b) + (s / b) * Q.1 := by
  simp only [seg, W1, sub_zero]; ring

/-- The second coordinate of the segment from `W1 = (-2,0)` to `Q`, evaluated at level `s`
between `0` and `b`. -/
theorem seg_W1_snd (Q : ℝ × ℝ) (b s : ℝ) :
    (seg W1 Q 0 b s).2 = (s / b) * Q.2 := by
  simp only [seg, W1, sub_zero]; ring

/-- The Euclidean norm of a vector of `R3` is at most the sum of the absolute values of
its three coordinates. -/
theorem norm_le_sum_abs (v : R3) : ‖v‖ ≤ |v 0| + |v 1| + |v 2| := by
  have hsq : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  have hle : ‖v‖ ^ 2 ≤ (|v 0| + |v 1| + |v 2|) ^ 2 := by
    rw [hsq]
    nlinarith [abs_nonneg (v 0), abs_nonneg (v 1), abs_nonneg (v 2),
      sq_abs (v 0), sq_abs (v 1), sq_abs (v 2)]
  have h2 := sq_le_sq.mp hle
  rwa [abs_of_nonneg (norm_nonneg v), abs_of_nonneg (by positivity)] at h2

/-- **The corrected profile leaves the axis uniformly in the azimuth.**  For small `s` the
point `eFunX t s` is close to the origin, uniformly for `t ∈ [-π,π]`.

Route: for `s ≤ 3/4 ≤ sig1c t` (`sig1c_ge` is in `WaypointDesign2.lean`) the profile is on
the first segment `seg W1 (W2c t) 0 (sig1c t) s`, so both `2 + (profX t s).1` and
`(profX t s).2` are `O(s)`, uniformly in `t`. -/
theorem eFunX_tendsto_zero :
    ∀ ε > 0, ∃ δ > 0, ∀ t ∈ Set.Icc (-Real.pi) Real.pi, ∀ s ∈ Set.Icc (0 : ℝ) 1,
      s < δ → ‖eFunX t s‖ < ε := by
  intro ε hε
  refine ⟨min (3 / 4) (3 * ε / 28), lt_min (by norm_num) (by linarith), ?_⟩
  intro t _ht s hs hsδ
  have hs0 : 0 ≤ s := hs.1
  have hsδ34 : s < 3 / 4 := lt_of_lt_of_le hsδ (min_le_left _ _)
  have hsδε : s < 3 * ε / 28 := lt_of_lt_of_le hsδ (min_le_right _ _)
  have hL_ge : 3 / 4 ≤ sig1c t := sig1c_ge t
  have hL_pos : 0 < sig1c t := lt_of_lt_of_le (by norm_num) hL_ge
  have hsL : s ≤ sig1c t := le_trans hsδ34.le hL_ge
  set L := sig1c t with hLdef
  have hL_ge' : (3 : ℝ) / 4 ≤ L := by rw [hLdef]; exact hL_ge
  have hL_pos' : 0 < L := by rw [hLdef]; exact hL_pos
  have hprofL : profX t s = seg W1 (W2c t) 0 L s := by
    rw [profX_br1 hsL, ← hLdef]
  have hfst : (profX t s).1 = -2 + 2 * (s / L) + (s / L) * (W2c t).1 := by
    rw [hprofL, seg_W1_fst]
  have hsnd : (profX t s).2 = (s / L) * (W2c t).2 := by
    rw [hprofL, seg_W1_snd]
  have hQ1 : |(W2c t).1| ≤ 1 := W2c_abs_fst t
  have hQ2 : |(W2c t).2| ≤ 1 := W2c_abs_snd t
  have hlam0 : 0 ≤ s / L := div_nonneg hs0 hL_pos'.le
  have hlam_le : s / L ≤ 4 * s / 3 := by
    have h1 : s / L ≤ s / (3 / 4) := div_le_div_of_nonneg_left hs0 (by norm_num) hL_ge'
    have h2 : s / (3 / 4) = 4 * s / 3 := by ring
    linarith
  have h2a : 2 + (profX t s).1 = (s / L) * (2 + (W2c t).1) := by
    rw [hfst]; ring
  have h2a_abs : |2 + (profX t s).1| ≤ 3 * (s / L) := by
    rw [h2a, abs_mul, abs_of_nonneg hlam0]
    have hb : |2 + (W2c t).1| ≤ 3 := by
      have h := abs_le.mp hQ1
      rw [abs_le]; exact ⟨by linarith [h.1], by linarith [h.2]⟩
    calc (s / L) * |2 + (W2c t).1| ≤ (s / L) * 3 := mul_le_mul_of_nonneg_left hb hlam0
      _ = 3 * (s / L) := by ring
  have hb_abs : |(profX t s).2| ≤ s / L := by
    rw [hsnd, abs_mul, abs_of_nonneg hlam0]
    calc (s / L) * |(W2c t).2| ≤ (s / L) * 1 := mul_le_mul_of_nonneg_left hQ2 hlam0
      _ = s / L := by ring
  have hnorm : ‖eFunX t s‖ ≤ 2 * |2 + (profX t s).1| + |(profX t s).2| := by
    calc ‖eFunX t s‖ ≤ |eFunX t s 0| + |eFunX t s 1| + |eFunX t s 2| := norm_le_sum_abs _
      _ = |2 + (profX t s).1| * |Real.cos t| + |2 + (profX t s).1| * |Real.sin t|
            + |(profX t s).2| := by
            rw [eFunX_apply_zero, eFunX_apply_one, eFunX_apply_two, abs_mul, abs_mul]
      _ ≤ |2 + (profX t s).1| * 1 + |2 + (profX t s).1| * 1 + |(profX t s).2| := by
            have h1 := Real.abs_cos_le_one t
            have h2 := Real.abs_sin_le_one t
            gcongr
      _ = 2 * |2 + (profX t s).1| + |(profX t s).2| := by ring
  have hfin : ‖eFunX t s‖ ≤ 28 * s / 3 := by
    nlinarith [hnorm, h2a_abs, hb_abs, hlam_le]
  have hlt : 28 * s / 3 < ε := by linarith
  linarith

end

end Work.Drive.EpsForm
