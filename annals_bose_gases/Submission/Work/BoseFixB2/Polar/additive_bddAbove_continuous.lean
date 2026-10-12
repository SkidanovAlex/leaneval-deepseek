import Mathlib.Analysis.InnerProductSpace.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB2.Polar

/-- An additive function `ℝ → ℝ` which is bounded above on a neighbourhood of `0`
is continuous.  (The point is that additivity makes the one-sided bound two-sided on
a symmetric neighbourhood, so the image of that neighbourhood is bounded, and a
bounded additive homomorphism out of a normed group is continuous.) -/
theorem additive_bddAbove_continuous {R : ℝ → ℝ} (hadd : ∀ s t : ℝ, R (s + t) = R s + R t)
    (hbd : ∃ M ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε → R t ≤ M) : Continuous R := by
  obtain ⟨M, ε, hε, hM⟩ := hbd
  -- package `R` as an additive homomorphism
  let f : ℝ →+ ℝ :=
    { toFun := R
      map_zero' := by
        have h := hadd 0 0
        simp only [zero_add] at h
        linarith
      map_add' := fun a b => hadd a b }
  -- additivity gives antisymmetry: `R (-t) = -R t`
  have hneg : ∀ t : ℝ, R (-t) = -R t := by
    intro t
    have h := hadd t (-t)
    simp only [add_neg_cancel] at h
    have h0 : R 0 = 0 := f.map_zero
    rw [h0] at h
    linarith
  -- the image of a symmetric neighbourhood of `0` is bounded
  have hbounded : Bornology.IsBounded (f '' Metric.ball (0 : ℝ) ε) := by
    rw [Metric.isBounded_iff_subset_ball (0 : ℝ)]
    refine ⟨|M| + 1, ?_⟩
    rintro y ⟨t, ht, rfl⟩
    show dist (R t) 0 < |M| + 1
    have htabs : |t| < ε := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
      exact ht
    rw [Real.dist_eq, sub_zero]
    have h1 : R t ≤ M := hM t htabs
    have h2 : R (-t) ≤ M := hM (-t) (by rw [abs_neg]; exact htabs)
    rw [hneg t] at h2
    rw [abs_lt]
    constructor <;> linarith [neg_abs_le M, le_abs_self M]
  have hcont : Continuous f :=
    f.continuous_of_isBounded_nhds_zero (Metric.ball_mem_nhds (0 : ℝ) hε) hbounded
  exact hcont

end Work.BoseFixB2.Polar
