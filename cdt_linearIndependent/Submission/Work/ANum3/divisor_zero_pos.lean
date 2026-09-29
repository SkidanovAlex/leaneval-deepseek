import Mathlib

namespace Work.ANum3

open Complex Metric MeromorphicOn

/-- For `f` analytic on a neighbourhood of `closedBall 0 R`, not vanishing at the origin, the
divisor of `f` on `closedBall 0 ρ` is at least `1` at every zero of `f` in that closed ball. -/
theorem divisor_zero_pos {R ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ R) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R)) (hf0 : f 0 ≠ 0)
    {u : ℂ} (hu : u ∈ Metric.closedBall (0 : ℂ) ρ) (hfu : f u = 0) :
    1 ≤ (MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) ρ)) u := by
  -- `0` lies in the closed ball of radius `R`, where `f` does not vanish, so the order of `f`
  -- at `0` is `0`, in particular not `⊤`.
  have hmem0R : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) R := by
    rw [Metric.mem_closedBall, dist_self]; linarith
  have hord0 : analyticOrderAt f 0 = 0 :=
    (hf 0 hmem0R).analyticOrderAt_eq_zero.mpr hf0
  have hmem0ρ : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) ρ := by
    rw [Metric.mem_closedBall, dist_self]; linarith
  -- `f` is analytic on the closed ball of radius `ρ ⊆ R`, which is preconnected, hence the order
  -- of `f` is finite everywhere there.
  have hfmono : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) ρ) :=
    hf.mono (Metric.closedBall_subset_closedBall hρR)
  have hfin : analyticOrderAt f u ≠ ⊤ :=
    AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected hfmono Metric.isPreconnected_closedBall
      hmem0ρ hu (by rw [hord0]; exact ENat.zero_ne_top)
  -- Rewrite the divisor as the (natural number) order of vanishing at `u`.
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hfmono hu, ← Nat.cast_analyticOrderNatAt hfin]
  rw [ENat.map_natCast, WithTop.untop₀_coe]
  -- `f u = 0` forces the order of vanishing at `u` to be at least `1`.
  have h1 : 1 ≤ analyticOrderNatAt f u := by
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    have h2 : analyticOrderAt f u = 0 := by
      rw [← Nat.cast_analyticOrderNatAt hfin, h0]; simp
    exact ((hfmono u hu).analyticOrderAt_eq_zero).mp h2 hfu
  exact_mod_cast h1

end Work.ANum3
