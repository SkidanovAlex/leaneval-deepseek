import Mathlib
import Submission.Work.Repel.koebe_covering_scaled

/-!
# The Koebe one-quarter covering theorem on an *open* disc

`Work.Repel.koebe_covering_scaled` proves the sharp Koebe covering theorem for a holomorphic
injection `f` on a **closed** disc `closedBall c R`:

`ball (f c) (R / 4 * ‖deriv f c‖) ⊆ f '' ball c R`.

For the applications in this workspace only *open-disc* differentiability is available, and
`DifferentiableOn ℂ f (ball c R)` certainly does not imply differentiability on the closed disc.
The two are nevertheless equivalent here, because the covering statement is open-ended: we apply
the closed-disc version with a slightly smaller radius `R' < R` chosen so that the target disc
`ball (f c) (R/4 * ‖deriv f c‖)` is already contained in `ball (f c) (R'/4 * ‖deriv f c‖)`.
Concretely, for `w` with `‖w - f c‖ < R/4 * ‖deriv f c‖` we take

`R' = (max (4 ‖w - f c‖ / ‖deriv f c‖) 0 + R) / 2`,

which satisfies `4 ‖w - f c‖ / ‖deriv f c‖ < R' < R`.  Then `closedBall c R' ⊆ ball c R`
(so `hf` restricts) and `ball c R' ⊆ ball c R` (so does injectivity), and the scaling lemma
applied at radius `R'` puts `w` in `f '' ball c R' ⊆ f '' ball c R`.

The case `deriv f c = 0` is vacuous: the target ball has radius `0` and is empty.
-/

namespace Work.Repel.R3Level1

open Metric

set_option linter.unusedVariables false in
theorem koebe_covering_open {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.ball c R))
    (hinj : Set.InjOn f (Metric.ball c R)) :
    Metric.ball (f c) (R / 4 * ‖deriv f c‖) ⊆ f '' Metric.ball c R := by
  intro w hw
  rw [Metric.mem_ball, dist_eq_norm] at hw
  by_cases hd : deriv f c = 0
  · -- the target disc has radius `0`, hence is empty
    rw [hd, norm_zero, mul_zero] at hw
    exact absurd hw (not_lt.mpr (norm_nonneg _))
  · set A : ℝ := 4 * ‖w - f c‖ / ‖deriv f c‖ with hA
    have hdpos : 0 < ‖deriv f c‖ := norm_pos_iff.mpr hd
    -- `w` is well inside the sharp covering radius, so `A` is strictly below `R`
    have hA_lt : A < R := by
      rw [hA, div_lt_iff₀ hdpos]
      nlinarith [hw]
    have hA_nonneg : 0 ≤ A := by
      rw [hA]; positivity
    -- an intermediate radius strictly between `A` and `R`
    set R' : ℝ := (A + R) / 2 with hR'def
    have hlt : R' < R := by rw [hR'def]; linarith
    have hpos : 0 < R' := by rw [hR'def]; linarith [hR, hA_nonneg]
    have hAlt : A < R' := by rw [hR'def]; linarith
    -- `w` lies in the covering disc of the smaller radius
    have hwf : ‖w - f c‖ < R' / 4 * ‖deriv f c‖ := by
      have h1 : 4 * ‖w - f c‖ < R' * ‖deriv f c‖ := by
        rw [hA, div_lt_iff₀ hdpos] at hAlt
        exact hAlt
      nlinarith
    have hcov := Work.Repel.koebe_covering_scaled (f := f) (c := c) (R := R') hpos
      (hf.mono (Metric.closedBall_subset_ball hlt))
      (hinj.mono (Metric.ball_subset_ball hlt.le))
    have hw' : w ∈ Metric.ball (f c) (R' / 4 * ‖deriv f c‖) := by
      rw [Metric.mem_ball, dist_eq_norm]; exact hwf
    exact (Set.image_mono (Metric.ball_subset_ball hlt.le)) (hcov hw')

end Work.Repel.R3Level1
