import Mathlib
import Submission.Work.FlowerGlue2.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FlowerGlue2

open Filter Set Metric
open scoped Topology

/-!
# `ParabolicBounds` for the germ of the parameter normal form at the parabolic parameter `c₀`

`Work.PARIMPL.ParNormal` records, for every `c` in the parameter ball, the *rotated* uniform
bounds `ParBounds (h c) (h c 0) (h1 c) P.A P.r`: the germ is `h ζ = τ + h₁ ζ + O(ζ²)` on
`‖ζ‖ < P.r`, with `‖h‖ ≤ 2` and `‖h‖ ≥ 1/2` there.  The Fatou–Leau construction of
`Work.FatouCoord` wants the *unrotated* form `ParabolicBounds f h 1 r A A'` with
`f ζ = ζ + ζ² h ζ`, `h 0 = 1`, and a bound `A'` on the derivative of `h` on the chart ball.

At the parabolic parameter `c₀` the rotation has disappeared (`hτ : P.h c₀ 0 = 1`), so the only
genuine content beyond the bookkeeping of `Work.FlowerGlue2.parabolicBounds_of_normalForm` is a
**derivative bound**.  `ParNormal` does not export one; but it does export holomorphy of the germ
on the chart ball (`hdiff`) and the sup-bound `‖h‖ ≤ 2` there, and Cauchy's estimate on the ball
of radius `P.r` gives the derivative bound `‖h'‖ ≤ 2·2/P.r` on the *half* ball.  That is exactly
the pair of parameters `(P.r / 2, 4 / P.r)` of the statement.

## Contents

* `Work.FlowerGlue2.norm_deriv_le_of_mem_ball_half` — Cauchy's estimate at the half radius;
* `Work.FlowerGlue2.parabolicBounds_c0`.
-/

/-- **Cauchy's estimate at the half radius.**  If `f` is holomorphic on `ball 0 R` and bounded
by `M` there, then on `ball 0 (R/2)` its derivative is bounded by `2 M / R`: at a point `z` with
`‖z‖ < R/2` the closed ball of radius `R/2` around `z` is contained in `ball 0 R`, and Cauchy's
estimate on that ball gives `‖f' z‖ ≤ M/(R/2)`. -/
theorem norm_deriv_le_of_mem_ball_half {R M : ℝ} (hR : 0 < R) {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) R))
    (hM : ∀ z ∈ Metric.ball (0 : ℂ) R, ‖f z‖ ≤ M) :
    ∀ z ∈ Metric.ball (0 : ℂ) (R / 2), ‖deriv f z‖ ≤ 2 * M / R := by
  intro z hz
  have hρ : 0 < R / 2 := by linarith
  have hsub : Metric.closedBall z (R / 2) ⊆ Metric.ball (0 : ℂ) R := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    rw [mem_ball_zero_iff]
    have h1 : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by simpa using norm_add_le (w - z) z
    have h2 : ‖z‖ < R / 2 := mem_ball_zero_iff.mp hz
    linarith
  have hdc : DiffContOnCl ℂ f (Metric.ball z (R / 2)) := hd.diffContOnCl_ball hsub
  have hsph : ∀ w ∈ Metric.sphere z (R / 2), ‖f w‖ ≤ M := fun w hw =>
    hM w (hsub (Metric.sphere_subset_closedBall hw))
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (f := f) hρ hdc hsph
  have hm : M / (R / 2) = 2 * M / R := by field_simp
  rwa [hm] at h

/-- **`ParabolicBounds` for the germ of the parameter normal form at the parabolic parameter.**

The germ of `P` at `c₀` is `h ζ = 1 + h₁ c₀ · ζ + O(ζ²)` (the `h 0 = 1` is the hypothesis `hτ`,
and the second order expansion is the closeness field of `ParBounds`), it is bounded by `2`, and
Cauchy's estimate upgrades the latter to the derivative bound `4 / P.r` on the half ball
`‖ζ‖ < P.r / 2`. -/
theorem parabolicBounds_c0 {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : Work.PARIMPL.ParNormal d)
    (hτ : P.h c₀ 0 = 1)
    (hdiff : DifferentiableOn ℂ (P.h c₀) (Metric.ball (0 : ℂ) P.r)) :
    Work.FatouCoord.ParabolicBounds (fun ζ : ℂ => ζ + ζ ^ 2 * P.h c₀ ζ) (P.h c₀) (P.h1 c₀)
      (P.r / 2) P.A (4 / P.r) := by
  have hb := P.bounds c₀ (mem_ball_self P.hρ₀)
  have hle : P.r / 2 ≤ P.r := by linarith [P.hr]
  have hbound : ∀ z : ℂ, ‖z‖ < P.r → ‖P.h c₀ z‖ ≤ 2 := hb.2.2.2.1
  refine ⟨?_, P.hA, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith [P.hr]
  · exact div_nonneg (by norm_num) P.hr.le
  · intro z _
    rfl
  · exact hdiff.mono (Metric.ball_subset_ball hle)
  · intro z hz
    have hzr : ‖z‖ < P.r := mem_ball_zero_iff.mp (Metric.ball_subset_ball hle hz)
    have h := hb.2.2.1 z hzr
    rw [hτ] at h
    exact h
  · intro z hz
    exact hbound z (mem_ball_zero_iff.mp (Metric.ball_subset_ball hle hz))
  · intro z hz
    have h := norm_deriv_le_of_mem_ball_half P.hr hdiff
      (fun w hw => hbound w (mem_ball_zero_iff.mp hw)) z hz
    have hm : 2 * 2 / P.r = 4 / P.r := by ring
    rwa [hm] at h

end Work.FlowerGlue2
