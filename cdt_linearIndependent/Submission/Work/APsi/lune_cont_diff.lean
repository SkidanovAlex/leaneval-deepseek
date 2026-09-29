import Mathlib
import Submission.Work.APsi.lune_branch
import Submission.Work.APsi.defs

/-!
# `Work.APsi.lune_cont_diff`: continuity / holomorphy of the lune map on the unit disc

For `c > 1` the lune map (`Submission.CDTPlan.lune c`, CDT arXiv:2408.15403 eq. `(firstgobble)`)

`lune c z = (z·B - B + √(R z)) / (2C)`,  `B = 1 + c²`, `C = c² - 1`, `R z = B²(1+z)² - 16c²z`,

is continuous on the closed unit disc and holomorphic on the open unit disc.

The only delicate point is the principal square root `w ↦ w ^ (1/2)` along the values `R z`.
On the *closed* unit disc, `R = luneR c` avoids the branch cut `(-∞,0)` except at its two zeros,
which lie on the unit circle (`luneR_slitPlane_of_le_of_ne`, `lune_branch`); at those zeros
`R z = 0` satisfies the weak hypothesis `0 ≤ re w ∨ im w ≠ 0` of
`Complex.continuousAt_cpow_const_of_re_pos`, so continuity holds there too.  On the *open* disc
`R` maps into `slitPlane` (`luneR_slitPlane_of_lt`), so `√R` is holomorphic there
(`DifferentiableOn.cpow_const`).
-/

namespace Work.APsi

open Submission.CDTPlan Complex Metric

noncomputable section

theorem lune_cont_diff (c : ℝ) (hc : 1 < c) :
    ContinuousOn (Submission.CDTPlan.lune c) (Metric.closedBall 0 1) ∧
      DifferentiableOn ℂ (Submission.CDTPlan.lune c) (Metric.ball 0 1) := by
  have hRcont : Continuous (luneR c) := by unfold luneR; fun_prop
  have hRdiff : Differentiable ℂ (luneR c) := by unfold luneR; fun_prop
  have hCne : (2 * luneC c) ≠ 0 := mul_ne_zero two_ne_zero (luneC_ne_zero hc)
  -- Continuity of the principal square root of `luneR c` on the closed unit disc.
  have hsqrt_cont : ContinuousOn (fun z : ℂ => (luneR c z) ^ (1 / 2 : ℂ)) (closedBall 0 1) := by
    intro z hz
    have hzmem : ‖z‖ ≤ 1 := by rwa [mem_closedBall, dist_zero_right] at hz
    -- the weak branch-cut hypothesis holds even at the two zeros of `luneR c`
    have hcond : 0 ≤ (luneR c z).re ∨ (luneR c z).im ≠ 0 := by
      rcases eq_or_ne (luneR c z) 0 with h | h
      · left; rw [h]; simp
      · rcases luneR_slitPlane_of_le_of_ne hc hzmem h with h1 | h2
        · exact Or.inl (le_of_lt h1)
        · exact Or.inr h2
    exact (Complex.continuousAt_cpow_const_of_re_pos hcond
      (by norm_num : 0 < ((1 / 2 : ℂ)).re)).comp_continuousWithinAt
      hRcont.continuousAt.continuousWithinAt
  -- Holomorphy of the principal square root of `luneR c` on the open unit disc.
  have hsqrt_diff : DifferentiableOn ℂ (fun z : ℂ => (luneR c z) ^ (1 / 2 : ℂ)) (ball 0 1) :=
    hRdiff.differentiableOn.cpow_const fun z hz =>
      luneR_slitPlane_of_lt hc (by simpa [mem_ball, dist_zero_right] using hz)
  have hcont : ContinuousOn (fun z : ℂ =>
      (z * luneB c - luneB c + (luneR c z) ^ (1 / 2 : ℂ)) / (2 * luneC c)) (closedBall 0 1) :=
    (ContinuousOn.add ((continuousOn_id.mul continuousOn_const).sub continuousOn_const)
      hsqrt_cont).div continuousOn_const (fun _ _ => hCne)
  have hdiff : DifferentiableOn ℂ (fun z : ℂ =>
      (z * luneB c - luneB c + (luneR c z) ^ (1 / 2 : ℂ)) / (2 * luneC c)) (ball 0 1) :=
    (DifferentiableOn.add ((differentiableOn_id.mul (differentiableOn_const (luneB c))).sub
      (differentiableOn_const (luneB c))) hsqrt_diff).div_const _
  have hfun : lune c = fun z : ℂ =>
      (z * luneB c - luneB c + (luneR c z) ^ (1 / 2 : ℂ)) / (2 * luneC c) :=
    funext (lune_eq c)
  rw [hfun]
  exact ⟨hcont, hdiff⟩

end

end Work.APsi
