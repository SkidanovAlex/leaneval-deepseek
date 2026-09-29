import Mathlib
import Submission.Work.C17I.defs
import Submission.Work.C17.stadium_geom
import Submission.Work.C17I.stadium_re_weak
import Submission.Work.C17I.stadium_subset_ball_weak
import Submission.Work.C17I.stadium_ne_half_weak

/-!
# `Work.C17I.stadium_facts` — elementary geometry of the stadium `Sset m n`

`Sset m n = stadiumSet (xsOf m n) ((1 - xsOf m n)/2) (1/20)` is the union of the discs
joining `ball (xsOf m n) ((1-xsOf m n)/2)` to `ball p₀ (1/20)`, `p₀ = 1/4 + i/5`
(`Submission/Work/C17I/defs.lean`).  Here we collect the elementary facts used by
`Work.C17I.pw_continuation`: it is convex and open, contains the two discs, lies in the
half-plane `Re z ≥ 1/5` and in the unit disc, and avoids `0` and `1/2`.

The geometric content is supplied by

* `Work.C17.stadiumSet_eq`, `Work.C17.stadBall_convex`, `Work.C17.stadBall_isOpen`,
  `Work.C17.ball_subset_stadiumSet` (`Submission/Work/C17/stadium_geom.lean`);
* `Work.C17I.stadium_re_weak`, `Work.C17I.stadium_subset_ball_weak`,
  `Work.C17I.stadium_ne_half_weak` (the general forms of the real-part, unit-disc and
  `1/2`-avoidance statements, proved in the sibling files);

the two remaining elementary facts (the `t = 1` slice and `‖p₀‖ ≤ 19/20`) are proved below.
-/

namespace Work.C17I

noncomputable section

/-- `‖p₀‖ = √41/20 ≤ 19/20`, so that `‖p₀‖ + 1/20 ≤ 1`. -/
lemma norm_p0C_le : ‖Work.C17.p0C‖ ≤ 19 / 20 := by
  have h2 : Complex.normSq Work.C17.p0C = (41 : ℝ) / 400 := by
    unfold Work.C17.p0C
    simp [Complex.normSq_apply]
    norm_num
  have h : ‖Work.C17.p0C‖ ^ 2 = (41 : ℝ) / 400 := by
    rw [← Complex.normSq_eq_norm_sq]
    exact h2
  nlinarith [norm_nonneg Work.C17.p0C]

/-- The disc `ball p₀ ρ` of radius `ρ` around `p₀` is the `t = 1` slice of the stadium. -/
lemma ball_p0C_subset_stadiumSet (c δ ρ : ℝ) :
    Metric.ball Work.C17.p0C ρ ⊆ Work.C17.stadiumSet c δ ρ := by
  intro z hz
  refine ⟨1, ⟨zero_le_one, le_refl 1⟩, ?_⟩
  simpa using hz

/-- **Geometry of the stadium `Sset m n`.**  For `0 < x_s = xsOf m n ≤ 1` with
`x_s ≥ 1 - 10⁻⁵`, the stadium joining `ball x_s ((1-x_s)/2)` to `ball p₀ (1/20)` is
convex and open, contains both discs, lies in `{Re z ≥ 1/5}` and in the unit disc, and
avoids `0` and `1/2`. -/
theorem stadium_facts (m n : ℕ) (hx0 : 0 < Work.C17.xsOf m n)
    (hx1 : 1 - 1 / 100000 ≤ Work.C17.xsOf m n) (hx2 : Work.C17.xsOf m n ≤ 1) :
    Convex ℝ (Work.C17I.Sset m n) ∧ IsOpen (Work.C17I.Sset m n) ∧
    Metric.ball ((Work.C17.xsOf m n : ℂ)) ((1 - Work.C17.xsOf m n) / 2) ⊆ Work.C17I.Sset m n ∧
    Metric.ball Work.C17.p0C (1 / 20) ⊆ Work.C17I.Sset m n ∧
    (0 : ℂ) ∉ Work.C17I.Sset m n ∧ Work.C17I.Sset m n ⊆ Metric.ball (0 : ℂ) 1 ∧
    (∀ z ∈ Work.C17I.Sset m n, (1 / 5 : ℝ) ≤ z.re) ∧ (1 / 2 : ℂ) ∉ Work.C17I.Sset m n := by
  have hsub : Work.C17I.Sset m n
      = Work.C17.stadiumSet (Work.C17.xsOf m n) ((1 - Work.C17.xsOf m n) / 2) (1 / 20) := rfl
  have hA : (1 : ℝ) / 5 ≤ Work.C17.xsOf m n - (1 - Work.C17.xsOf m n) / 2 := by
    nlinarith [hx1]
  have hB : (1 : ℝ) / 5 ≤ (1 : ℝ) / 4 - 1 / 20 := by norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- convexity: `stadiumSet` is the `stadBall` of two radii affinely interpolated
    rw [hsub, Work.C17.stadiumSet_eq]
    exact Work.C17.stadBall_convex _ _ _ _
  · -- openness: a union of open discs
    rw [hsub, Work.C17.stadiumSet_eq]
    exact Work.C17.stadBall_isOpen _ _ _ _
  · -- the `t = 0` slice is `ball (xsOf m n) ((1-xsOf m n)/2)`
    rw [hsub]
    exact Work.C17.ball_subset_stadiumSet _ _ _
  · -- the `t = 1` slice is `ball p₀ (1/20)`
    rw [hsub]
    exact ball_p0C_subset_stadiumSet _ _ _
  · -- `0 ∉ Sset` since `Re z ≥ 1/5`
    intro h0
    rw [hsub] at h0
    have hmem := stadium_re_weak hA hB (0 : ℂ) h0
    simp only [Complex.zero_re] at hmem
    norm_num at hmem
  · -- `Sset ⊆ ball 0 1` since `xsOf + (1-xsOf)/2 ≤ 1` and `‖p₀‖ + 1/20 ≤ 1`
    rw [hsub]
    refine stadium_subset_ball_weak (by linarith) ?_ ?_
    · nlinarith [hx2]
    · nlinarith [norm_p0C_le]
  · -- `Re z ≥ 1/5`
    rw [hsub]
    exact stadium_re_weak hA hB
  · -- `1/2 ∉ Sset`
    rw [hsub]
    exact fun h => (stadium_ne_half_weak hx1 le_rfl le_rfl (1 / 2) h) rfl

end

end Work.C17I
