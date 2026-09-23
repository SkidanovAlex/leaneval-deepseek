import Submission.JacobiCover

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Bundle ContDiff Set Metric Filter


/-!
# A `C^∞` bump supported in an interval

`exists_contDiff_bump_Ioo`: for `a < t₀ < b` there is a `C^∞` function `χ` with `χ = 1` at `t₀`,
`0 ≤ χ ≤ 1` everywhere and `χ = 0` outside `(a,b)` (a `ContDiffBump`).  This is the cut-off used to
build the perturbation `W` of the shortening argument for `σ ≤ κ` (Roadmap §100.13, item 1): the bump
field `W(t) = χ(t) • (parallel/coordinate constant)` is supported in the piece containing the
conjugate time `t₀` and equals `-∇J(t₀)` there.
-/

namespace Submission.JacobiBump

/-- **A `C^∞` bump supported in an open interval, taking the value `1` at a prescribed interior
point.**  Used for the perturbation `W` of the shortening argument for `σ ≤ κ`. -/
theorem exists_contDiff_bump_Ioo {a b t₀ : ℝ} (ha : a < t₀) (hb : t₀ < b) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ χ t₀ = 1 ∧ (∀ t, 0 ≤ χ t) ∧ (∀ t, χ t ≤ 1) ∧
      (∀ t, t ∉ Ioo a b → χ t = 0) := by
  have h1 : 0 < t₀ - a := by linarith
  have h2 : 0 < b - t₀ := by linarith
  have hε : 0 < min (t₀ - a) (b - t₀) / 4 := by positivity
  set φ : ContDiffBump t₀ :=
    ⟨min (t₀ - a) (b - t₀) / 4, min (t₀ - a) (b - t₀) / 2, hε, by linarith⟩ with hφdef
  refine ⟨φ, ContDiffBump.contDiff φ, ?_, ?_, ?_, ?_⟩
  · refine ContDiffBump.one_of_mem_closedBall φ ?_
    rw [Metric.mem_closedBall, dist_self]
    exact φ.rIn_pos.le
  · exact fun t => ContDiffBump.nonneg φ
  · exact fun t => ContDiffBump.le_one φ
  · intro t ht
    have hmin : 0 < min (t₀ - a) (b - t₀) := lt_min h1 h2
    have hmem : t ∉ Metric.ball t₀ (min (t₀ - a) (b - t₀) / 2) := by
      intro hb'
      rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs, abs_lt] at hb'
      rcases le_or_gt t a with h | h
      · have hm : min (t₀ - a) (b - t₀) ≤ t₀ - a := min_le_left _ _
        linarith [hb'.1, hm]
      · refine ht ⟨h, ?_⟩
        have hm : min (t₀ - a) (b - t₀) ≤ b - t₀ := min_le_right _ _
        linarith [hb'.2, hm]
    by_contra hne
    exact hmem (by rw [← ContDiffBump.support_eq φ]; exact Function.mem_support.mpr hne)

end Submission.JacobiBump
