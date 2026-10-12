import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.AprioriCount.conv3_pos_of_norm_lt
import Submission.Work.BoseBoxFock.PCFU.chiW1_integrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.convScale_lower_closedBall`

`Submission.BoseGases.convScale ℓ z = (χ ⋆ χ)(z/ℓ)` is the renormalisation denominator of the
localised two-body kernel `w = χ_ℓ(x)·v(x−y)/(χ⋆χ)_ℓ(x−y)·χ_ℓ(y)`; a *uniform* positive lower
bound on a closed ball is what makes `v/(χ⋆χ)_ℓ` a bounded (hence integrable) numerator there.

The statement proved here: for every `0 < ℓ` and every `r < ℓ` there is `m > 0` with
`m ≤ convScale ℓ z` for all `z` with `‖z‖ ≤ r` (with the ball empty, i.e. the statement vacuous,
when `r < 0`).

## Proof

`convScale ℓ` is continuous (`Submission.BoseGases.convScale_continuous`) and nonnegative
(`Submission.BoseGases.convScale_nonneg`) everywhere, and it is *strictly positive on the open
ball of radius `ℓ`*: `convScale ℓ z = conv3 χ χ ((ℓ⁻¹)•z)` and for `‖w‖ < 1` the two half-balls
`B(0,1/2)` and `B(w,1/2)` overlap — the midpoint `w/2` lies strictly inside both — where `χ > 0`
(that is `Work.AprioriCount.conv3_pos_of_norm_lt`).  For `r ≥ 0` the closed ball `‖z‖ ≤ r` is
compact and nonempty, so `convScale ℓ` attains its minimum there
(`IsCompact.exists_isMinOn`); by the above the minimum is `> 0`.  For `r < 0` the ball is empty
and any `m > 0` works.
-/

namespace Work.BoseBoxFock.PCFU

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- `(χ⋆χ)_ℓ` is strictly positive strictly inside the ball of radius `ℓ`: `‖z‖ < ℓ` forces
`‖(ℓ⁻¹)•z‖ < 1`, where the two half-balls of the convolution overlap. -/
lemma convScale_pos_of_norm_lt {ℓ : ℝ} (hℓ : 0 < ℓ) {z : E3} (hz : ‖z‖ < ℓ) :
    0 < Submission.BoseGases.convScale ℓ z := by
  have hlt : ‖(ℓ⁻¹ : ℝ) • z‖ < 1 := by
    rw [norm_smul, Real.norm_of_nonneg (le_of_lt (inv_pos.mpr hℓ))]
    calc ℓ⁻¹ * ‖z‖ < ℓ⁻¹ * ℓ := mul_lt_mul_of_pos_left hz (inv_pos.mpr hℓ)
      _ = 1 := by field_simp
  have h := Work.AprioriCount.conv3_pos_of_norm_lt hlt
  simpa [Submission.BoseGases.convScale] using h

theorem convScale_lower_closedBall {ℓ r : ℝ} (hℓ : 0 < ℓ) (hr : r < ℓ) :
    ∃ m : ℝ, 0 < m ∧ ∀ z : EuclideanSpace ℝ (Fin 3),
      ‖z‖ ≤ r → m ≤ Submission.BoseGases.convScale ℓ z := by
  rcases le_or_gt 0 r with hr0 | hr0
  · -- `r ≥ 0`: `convScale ℓ` is continuous and positive on the compact closed ball `‖z‖ ≤ r`,
    -- so it attains a strictly positive minimum there
    have hne : (Metric.closedBall (0 : E3) r).Nonempty :=
      ⟨0, by rw [Metric.mem_closedBall, dist_self]; exact hr0⟩
    obtain ⟨z₀, hz₀, hmin⟩ := (isCompact_closedBall (0 : E3) r).exists_isMinOn hne
      (Submission.BoseGases.convScale_continuous ℓ).continuousOn
    have hz₀r : ‖z₀‖ ≤ r := by
      rwa [Metric.mem_closedBall, dist_zero_right] at hz₀
    refine ⟨Submission.BoseGases.convScale ℓ z₀,
      convScale_pos_of_norm_lt hℓ (lt_of_le_of_lt hz₀r hr), ?_⟩
    intro z hz
    exact hmin (by rw [Metric.mem_closedBall, dist_zero_right]; exact hz)
  · -- `r < 0`: the constraint `‖z‖ ≤ r` is unsatisfiable
    refine ⟨1, one_pos, fun z hz => ?_⟩
    have : (0 : ℝ) ≤ r := le_trans (norm_nonneg z) hz
    linarith

end Work.BoseBoxFock.PCFU
