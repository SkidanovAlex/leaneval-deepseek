import Mathlib

namespace Work.TMC13

open Set

/-- An analytic function on an open vertical strip is Lipschitz in the second
variable, uniformly on smaller compact sub-boxes: this is the mean-value
estimate for analytic (hence `C^1`) functions, applied to the compact convex
box `[a', b'] × [0, 1]`. -/
theorem analytic_lipschitz {g : ℝ × ℝ → ℝ} {a b : ℝ}
    (hg : AnalyticOnNhd ℝ g (Set.Ioo a b ×ˢ Set.univ))
    {a' b' : ℝ} (ha : a < a') (hb : b' < b) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ E ∈ Set.Icc a' b', ∀ y ∈ Set.Icc (0:ℝ) 1, ∀ y' ∈ Set.Icc (0:ℝ) 1,
      |g (E, y) - g (E, y')| ≤ K * |y - y'| := by
  -- The compact convex box on which the uniform estimate is taken.
  set s : Set (ℝ × ℝ) := Icc a' b' ×ˢ Icc (0 : ℝ) 1 with hs
  -- It is contained in the open strip of analyticity.
  have hsU : s ⊆ Ioo a b ×ˢ univ := by
    rw [hs]
    exact Set.prod_mono (Icc_subset_Ioo ha hb) (subset_univ _)
  -- Analyticity gives `C^1` (indeed `C^∞`) on the box.
  have hcd : ContDiffOn ℝ 1 g s := by
    intro x hx
    exact (AnalyticAt.contDiffAt (hg x (hsU hx))).contDiffWithinAt
  have hconv : Convex ℝ s := by
    rw [hs]; exact (convex_Icc _ _).prod (convex_Icc _ _)
  have hcomp : IsCompact s := by
    rw [hs]; exact isCompact_Icc.prod isCompact_Icc
  -- A `C^1` function on a compact convex set is Lipschitz on it.
  obtain ⟨K, hK⟩ := hcd.exists_lipschitzOnWith one_ne_zero hconv hcomp
  refine ⟨(K : ℝ), K.coe_nonneg, ?_⟩
  intro E hE y hy y' hy'
  have hp : (E, y) ∈ s := by rw [hs]; exact ⟨hE, hy⟩
  have hp' : (E, y') ∈ s := by rw [hs]; exact ⟨hE, hy'⟩
  have h := hK.dist_le_mul (E, y) hp (E, y') hp'
  -- The product distance in the vertical direction is `|y - y'|`.
  have hd : dist (E, y) (E, y') = |y - y'| := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_self, abs_zero,
      max_eq_right (abs_nonneg _)]
  rw [Real.dist_eq, hd] at h
  exact h

end Work.TMC13
