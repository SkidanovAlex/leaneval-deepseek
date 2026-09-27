import Mathlib
import Submission.Work.Whitney.exists_sheet_model

/-!
# A smooth cutoff that is also Lipschitz on all of `ℝ^N`

`Work.Whitney.exists_smooth_cutoff` (`exists_sheet_model.lean`) produces a smooth function `χ` equal
to `1` on `closedBall 0 R`, vanishing outside `closedBall 0 R'`, with values in `[0,1]`.  The
*gluing* constructions of this workspace (in particular the germ-extension step of the collar
trivialisation, `NOTES_hasFingerData_S33.md` §6/§7) need in addition a **global Lipschitz bound**
for `χ`, because the interpolated map `y ↦ Ψ₀ y + χ y • W y` is analysed by comparing values at two
points and the term `(χ x - χ y) • W x` has to be controlled.

This file supplies `Work.Whitney.CutPush.exists_lipschitz_smooth_cutoff`.  The bound is obtained from
`ContDiffOn.exists_lipschitzOnWith` on the convex compact set `closedBall 0 R'`, extended off that
ball by hand: for `x` in the ball and `y` outside, the radial point `x' := (R' / ‖x‖) • x` satisfies
`χ x' = 0 = χ y` and `‖x - x'‖ = R' - ‖x‖ ≤ ‖y‖ - ‖x‖ ≤ ‖x - y‖`, so the on-the-ball estimate at
the pair `(x, x')` transfers; the remaining cases are the ball itself and the exterior.
-/

open scoped ContDiff NNReal

namespace Work.Whitney.CutPush

/-- **A smooth cutoff with a global Lipschitz bound.**  For `0 < R < R'` there are a smooth
`χ : ℝ^N → ℝ` and a constant `C ≥ 0` with `0 ≤ χ ≤ 1`, `χ = 1` on `closedBall 0 R`,
`χ = 0` outside `closedBall 0 R'`, and `‖χ x - χ y‖ ≤ C ‖x - y‖` for all `x, y`. -/
theorem exists_lipschitz_smooth_cutoff {N : ℕ} {R R' : ℝ} (hR : 0 < R) (hRR' : R < R') :
    ∃ (χ : EuclideanSpace ℝ (Fin N) → ℝ) (C : ℝ),
      0 ≤ C ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ (∀ u, 0 ≤ χ u ∧ χ u ≤ 1) ∧
      (∀ u, ‖u‖ ≤ R → χ u = 1) ∧ (∀ u, R' ≤ ‖u‖ → χ u = 0) ∧
      (∀ x y : EuclideanSpace ℝ (Fin N), ‖χ x - χ y‖ ≤ C * ‖x - y‖) := by
  obtain ⟨χ, hχ, hb, h1, h0⟩ := exists_smooth_cutoff (n := N) hR hRR'
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hR'pos : 0 < R' := lt_trans hR hRR'
  obtain ⟨L, hL⟩ : ∃ L : ℝ≥0,
      LipschitzOnWith L χ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) R') :=
    (hχ.contDiffOn (s := Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) R')).exists_lipschitzOnWith
      hne (convex_closedBall 0 R') (isCompact_closedBall 0 R')
  have hmem : ∀ x : EuclideanSpace ℝ (Fin N),
      x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) R' ↔ ‖x‖ ≤ R' := by
    intro x
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  -- the estimate for a point of the ball and a point outside it
  have key : ∀ x y : EuclideanSpace ℝ (Fin N), ‖x‖ ≤ R' → R' ≤ ‖y‖ →
      ‖χ x - χ y‖ ≤ max (L : ℝ) (1 / R') * ‖x - y‖ := by
    intro x y hx hy
    have hχy : χ y = 0 := h0 y hy
    rcases eq_or_ne x 0 with hx0 | hx0
    · subst hx0
      have hnorm : 1 ≤ (1 / R') * ‖y‖ := by
        rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hR'pos]
        linarith
      calc ‖χ (0 : EuclideanSpace ℝ (Fin N)) - χ y‖ ≤ 1 := by
            rw [hχy, sub_zero, Real.norm_eq_abs, abs_of_nonneg (hb 0).1]
            exact (hb 0).2
        _ ≤ (1 / R') * ‖y‖ := hnorm
        _ ≤ max (L : ℝ) (1 / R') * ‖y‖ :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
        _ = max (L : ℝ) (1 / R') * ‖(0 : EuclideanSpace ℝ (Fin N)) - y‖ := by
            rw [zero_sub, norm_neg]
    · set x' : EuclideanSpace ℝ (Fin N) := (R' / ‖x‖) • x with hx'def
      have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      have hx'norm : ‖x'‖ = R' := by
        rw [hx'def, norm_smul, Real.norm_eq_abs,
          abs_of_pos (div_pos hR'pos hxn)]
        field_simp
      have hx'mem : x' ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) R' := (hmem x').mpr hx'norm.le
      have hxmem : x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) R' := (hmem x).mpr hx
      have hχx' : χ x' = 0 := h0 x' hx'norm.ge
      have hle1 : 1 ≤ R' / ‖x‖ := (one_le_div hxn).mpr hx
      have hdist : ‖x - x'‖ = R' - ‖x‖ := by
        rw [hx'def, show x - (R' / ‖x‖) • x = (1 - R' / ‖x‖) • x by rw [sub_smul, one_smul]]
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
        field_simp
        ring
      have hybound : R' - ‖x‖ ≤ ‖x - y‖ := by
        have h3 : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
          have h4 := norm_add_le x (y - x)
          rw [show x + (y - x) = y by abel, norm_sub_rev] at h4
          exact h4
        linarith
      calc ‖χ x - χ y‖ = ‖χ x - χ x'‖ := by rw [hχy, hχx']
        _ ≤ (L : ℝ) * ‖x - x'‖ := by
            simpa [Real.dist_eq, dist_eq_norm] using hL.dist_le_mul x hxmem x' hx'mem
        _ ≤ (L : ℝ) * ‖x - y‖ := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            linarith [hdist, hybound]
        _ ≤ max (L : ℝ) (1 / R') * ‖x - y‖ :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  refine ⟨χ, max (L : ℝ) (1 / R'), by positivity, hχ, hb, h1, h0, ?_⟩
  intro x y
  rcases le_total ‖x‖ R' with hx | hx
  · rcases le_total ‖y‖ R' with hy | hy
    · have hxmem : x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) R' := (hmem x).mpr hx
      have hymem : y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) R' := (hmem y).mpr hy
      calc ‖χ x - χ y‖ ≤ (L : ℝ) * ‖x - y‖ := by
            simpa [Real.dist_eq, dist_eq_norm] using hL.dist_le_mul x hxmem y hymem
        _ ≤ max (L : ℝ) (1 / R') * ‖x - y‖ :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    · exact key x y hx hy
  · rcases le_total ‖y‖ R' with hy | hy
    · have h := key y x hy hx
      simpa [norm_sub_rev] using h
    · have hC : 0 ≤ max (L : ℝ) (1 / R') :=
        le_trans (by positivity : (0 : ℝ) ≤ 1 / R') (le_max_right _ _)
      rw [h0 x hx, h0 y hy, sub_zero, norm_zero]
      exact mul_nonneg hC (norm_nonneg _)

end Work.Whitney.CutPush
