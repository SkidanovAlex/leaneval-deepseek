import Mathlib
import Submission.Work.Motion.schwarz_pick_deriv

/-!
# Schwarz–Pick derivative bound on the unit disc

A holomorphic map of the unit disc into the *closed* unit disc satisfies
`‖deriv f z‖ ≤ 1 / (1 - ‖z‖ ^ 2)` at every point `z` of the disc.

This is the Schwarz–Pick estimate
`‖deriv f z‖ ≤ (1 - ‖f z‖ ^ 2) / (1 - ‖z‖ ^ 2) ≤ 1 / (1 - ‖z‖ ^ 2)`.

The proof reuses the general Schwarz–Pick bound `Work.Motion.schwarz_pick_deriv`
(a holomorphic map of `ball c R` into `ball c M` satisfies
`‖deriv f z‖ ≤ M * R / (R ^ 2 - ‖z - c‖ ^ 2)`), which is stated for an *open* target
ball.  The closed-ball hypothesis is absorbed by applying that bound with the slightly
larger target radius `M = 1 + δ` and letting `δ → 0⁺`; the isolated point of the limit
is handled with `le_of_forall_pos_le_add`.
-/

namespace Work.Dim.Branch

open Metric Set

/-- **Schwarz–Pick derivative bound.** If `f` is holomorphic on the unit disc and maps it
into the closed unit disc, then at every `z` of the disc
`‖deriv f z‖ ≤ 1 / (1 - ‖z‖ ^ 2)`. -/
theorem SchwarzPick (f : ℂ → ℂ) (z : ℂ)
    (hd : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hmap : Set.MapsTo f (Metric.ball 0 1) (Metric.closedBall 0 1))
    (hz : z ∈ Metric.ball 0 1) :
    ‖deriv f z‖ ≤ 1 / (1 - ‖z‖ ^ 2) := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hBpos : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  -- For every `δ > 0` the map `f` takes `ball 0 1` into the *open* ball of radius `1 + δ`,
  -- so the general Schwarz–Pick bound applies with `M = 1 + δ`, `R = 1`.
  have key : ∀ δ : ℝ, 0 < δ → ‖deriv f z‖ ≤ (1 + δ) / (1 - ‖z‖ ^ 2) := by
    intro δ hδpos
    have hMaps : Set.MapsTo f (Metric.ball 0 1) (Metric.ball 0 (1 + δ)) := by
      intro t ht
      rw [mem_ball_zero_iff]
      have ht' := hmap ht
      rw [mem_closedBall_zero_iff] at ht'
      linarith
    have h := Work.Motion.schwarz_pick_deriv (f := f) (c := 0) (R := 1) (M := 1 + δ)
      (by norm_num) hd hMaps hz
    rwa [sub_zero, one_pow, mul_one] at h
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  have hδpos : 0 < ε * (1 - ‖z‖ ^ 2) / 2 := div_pos (mul_pos hε hBpos) (by norm_num)
  have h := key (ε * (1 - ‖z‖ ^ 2) / 2) hδpos
  have hsplit : (1 + ε * (1 - ‖z‖ ^ 2) / 2) / (1 - ‖z‖ ^ 2)
      = 1 / (1 - ‖z‖ ^ 2) + ε / 2 := by
    field_simp
  rw [hsplit] at h
  linarith

end Work.Dim.Branch
