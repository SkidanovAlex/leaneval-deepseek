import Mathlib

/-!
# An even smooth cutoff

Given an open `Ω ⊆ ℝ × ℝ` containing a point `(σ₀, 0)` of the horizontal axis, there is a `C^∞`
function `χ : ℝ × ℝ → ℝ` with values in `[0,1]`, equal to `1` on a neighbourhood of `(σ₀,0)`,
supported in `Ω`, and **even in the second coordinate**:
`χ (q.1, -q.2) = χ q`.

The construction is the product of a one-dimensional bump in the first coordinate around `σ₀` and a
one-dimensional bump in the second coordinate around `0`; the latter is even by
`ContDiffBump.neg`, so the product is even in the second coordinate.
-/

namespace Work.Drive

open scoped Topology

noncomputable section

/-- The standard bump function on `ℝ` with centre `c`, of inner radius `r/2` and outer radius `r`. -/
private def bumpAt (c : ℝ) {r : ℝ} (hr : 0 < r) : ContDiffBump c :=
  ⟨r / 2, r, by linarith, by linarith⟩

theorem exists_even_smooth_cutoff (σ₀ : ℝ) {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (h₀ : (σ₀, 0) ∈ Ω) :
    ∃ χ : ℝ × ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧
      (∀ q, 0 ≤ χ q) ∧ (∀ q, χ q ≤ 1) ∧
      (∀ᶠ q in 𝓝 (σ₀, 0), χ q = 1) ∧
      Function.support χ ⊆ Ω ∧
      (∀ q : ℝ × ℝ, χ (q.1, -q.2) = χ q) := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.1 hΩ (σ₀, 0) h₀
  refine ⟨fun q => bumpAt σ₀ hr q.1 * bumpAt 0 hr q.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- smoothness
    apply ContDiff.mul
    · exact (ContDiffBump.contDiff (bumpAt σ₀ hr)).comp contDiff_fst
    · exact (ContDiffBump.contDiff (bumpAt 0 hr)).comp contDiff_snd
  · -- nonnegativity
    intro q; exact mul_nonneg (ContDiffBump.nonneg _) (ContDiffBump.nonneg _)
  · -- bounded by one
    intro q
    exact mul_le_one₀ (ContDiffBump.le_one _) (ContDiffBump.nonneg _) (ContDiffBump.le_one _)
  · -- equal to one near the centre: on the ball of radius `r/2` both bumps are `1`
    have hball : Metric.ball (σ₀, (0 : ℝ)) (r / 2) ∈ 𝓝 (σ₀, 0) :=
      Metric.ball_mem_nhds _ (by linarith)
    filter_upwards [hball] with q hq
    have hq' : dist q.1 σ₀ < r / 2 := by
      rw [Metric.mem_ball] at hq; rw [Prod.dist_eq] at hq
      exact lt_of_le_of_lt (le_max_left _ _) hq
    have hq'' : dist q.2 (0 : ℝ) < r / 2 := by
      rw [Metric.mem_ball] at hq; rw [Prod.dist_eq] at hq
      exact lt_of_le_of_lt (le_max_right _ _) hq
    have h1 : bumpAt σ₀ hr q.1 = 1 := by
      apply ContDiffBump.one_of_mem_closedBall
      rw [Metric.mem_closedBall]; exact le_of_lt hq'
    have h2 : bumpAt 0 hr q.2 = 1 := by
      apply ContDiffBump.one_of_mem_closedBall
      rw [Metric.mem_closedBall]; exact le_of_lt hq''
    rw [h1, h2, mul_one]
  · -- the support is contained in `Ω`: both factors must be nonzero, so `q` lies in the ball of radius `r`
    intro q hq
    have hq1 : q.1 ∈ Function.support (bumpAt σ₀ hr) := fun h => hq (by simp [h])
    have hq2 : q.2 ∈ Function.support (bumpAt 0 hr) := fun h => hq (by simp [h])
    rw [ContDiffBump.support_eq] at hq1 hq2
    rw [Metric.mem_ball] at hq1 hq2
    apply hsub
    rw [Metric.mem_ball, Prod.dist_eq]
    exact max_lt hq1 hq2
  · -- evenness in the second coordinate
    intro q
    show bumpAt σ₀ hr q.1 * bumpAt 0 hr (-q.2) = bumpAt σ₀ hr q.1 * bumpAt 0 hr q.2
    rw [ContDiffBump.neg (bumpAt 0 hr) q.2]

end

end Work.Drive
