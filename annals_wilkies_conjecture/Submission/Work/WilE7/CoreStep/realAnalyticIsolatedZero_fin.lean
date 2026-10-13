import Mathlib

namespace Work.WilE7.CoreStep

open Filter Topology

theorem realAnalyticIsolatedZero_fin {k : ℕ} {g : ℝ → (Fin k → ℝ)}
    (hg : AnalyticAt ℝ g 0) :
    (∀ᶠ x in 𝓝 (0 : ℝ), g x = g 0) ∨
      ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, |x| < δ → g x = g 0 → x = 0 := by
  -- Apply the principle of isolated zeros to the analytic function `x ↦ g x - g 0`.
  rcases (hg.sub analyticAt_const).eventually_eq_zero_or_eventually_ne_zero with h | h
  · -- First case: `g - g 0` vanishes in a neighbourhood of `0`, so `g` is eventually constant.
    left
    filter_upwards [h] with x hx
    exact sub_eq_zero.mp hx
  · -- Second case: `g - g 0` does not vanish in a punctured neighbourhood of `0`.
    right
    rw [eventually_nhdsWithin_iff] at h
    rw [Metric.eventually_nhds_iff] at h
    obtain ⟨ε, hε, hε'⟩ := h
    refine ⟨ε, hε, fun x hx hgx => ?_⟩
    by_contra hx0
    exact hε' (by rwa [Real.dist_eq, sub_zero]) (by simpa using hx0)
      (by simp [Pi.sub_apply, hgx])

end Work.WilE7.CoreStep
