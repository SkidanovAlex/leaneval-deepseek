import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.SmallBoxA0.KinWitnessDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0

open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators ENNReal
open Submission BoseGases
open Work.SmallBoxA0

/-- The scaled bump `kwBump c z = chiBase (c • z)` (defined in
`Submission/Work/SmallBoxA0/KinWitnessDefs.lean`) vanishes outside the box `acube s` as soon as
`0 < s` and `2 / s < c` (which forces `c > 0`).

HINT.  `z ∉ acube s` gives a coordinate `m : Fin 3` with `(z m) ∉ Set.Icc (-s/2) (s/2)`, hence
`|z m| > s / 2`, and `|z m| ≤ ‖z‖` (`Submission.BoseGases.abs_coord_le_norm`), so `‖z‖ > s/2`.
From `2 / s < c` and `0 < s` one gets `1/s < c`, i.e. `1 / (2*c) < s / 2`.  Hence
`‖c • z‖ = c * ‖z‖ > c * (1/(2c)) = 1/2` (`norm_smul`, `Real.norm_of_nonneg`,
`mul_lt_mul_of_pos_left`), and `kwBump c z = chiBase (c • z) = 0` by
`Submission.BoseGases.chiBase_eq_zero_of_norm_gt`. -/
lemma kwBumpZero {s c : ℝ} (hs : 0 < s) (hcs : 2 / s < c) {z : EuclideanSpace ℝ (Fin 3)}
    (hz : z ∉ acube s) : kwBump c z = 0 := by
  -- `c > 0` because `2 / s > 0` and `2 / s < c`.
  have hcpos : 0 < c := lt_trans (div_pos two_pos hs) hcs
  rw [kwBump]
  apply chiBase_eq_zero_of_norm_gt
  -- reduce to the scalar inequality `1 / 2 < c * ‖z‖`
  rw [norm_smul, Real.norm_of_nonneg (le_of_lt hcpos)]
  -- some coordinate leaves the box, hence `|z m| > s / 2`.
  have hzcoord : ∃ m : Fin 3, z m ∉ Set.Icc (-s/2) (s/2) := by
    by_contra h
    apply hz
    rw [mem_acube_iff]
    simpa only [not_exists, not_not] using h
  obtain ⟨m, hm⟩ := hzcoord
  have habs : s / 2 < |z m| := by
    rw [Set.mem_Icc, not_and_or] at hm
    rcases hm with h | h
    · rw [not_le] at h
      rw [abs_of_neg (by linarith)]
      linarith
    · rw [not_le] at h
      rw [abs_of_pos (by linarith)]
      exact h
  -- coordinate bound `|z m| ≤ ‖z‖`.
  have hnorm_gt : s / 2 < ‖z‖ := lt_of_lt_of_le habs (abs_coord_le_norm z m)
  -- `2 < c * s` (from `2 / s < c` and `s > 0`).
  have hcs2 : 2 < c * s := by
    rw [div_lt_iff₀ hs] at hcs
    linarith
  -- hence `1 / (2 * c) < s / 2`.
  have hlt : 1 / (2 * c) < s / 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  -- multiply by `c > 0` and use `c * (1 / (2*c)) = 1/2`.
  have hnorm_bound : 1 / 2 < c * ‖z‖ := by
    have hcc : c * (1 / (2 * c)) = 1 / 2 := by
      field_simp
    rw [← hcc]
    apply mul_lt_mul_of_pos_left _ hcpos
    linarith
  exact hnorm_bound

end Work.SmallBoxA0
