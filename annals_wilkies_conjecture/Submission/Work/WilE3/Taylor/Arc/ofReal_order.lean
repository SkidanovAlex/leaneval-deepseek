import Mathlib
import Submission.Work.WilE3.Taylor.Arc.complexify_order
import Submission.Work.WilE3.Taylor.Arc.order_restrict

namespace Work.WilE3.Taylor.Arc

open Filter
open scoped Topology

/-- Complexifying a real analytic germ at `0` does not change its order of vanishing: the germ
`t ↦ (g t : ℂ)` and the germ `g` vanish to exactly the same order at `0`.

The proof is a two step reduction, both steps available as lemmas in the library.
First (`complexify_order`) `g` extends to a function `F` holomorphic on a complex disk around `0`,
agreeing with `g` on the real axis and with the same order of vanishing at `0`.  Second
(`order_restrict`) restricting a holomorphic germ to the real line does not change its order of
vanishing.  Composing the two equalities and replacing `F` by `g` through the local agreement of
the two germs (`analyticOrderAt_congr`) gives the claim. -/
theorem ofReal_order {g : ℝ → ℝ} (hg : AnalyticAt ℝ g 0) :
    analyticOrderAt (fun t : ℝ => ((g t : ℝ) : ℂ)) 0 = analyticOrderAt g 0 := by
  -- Complexify the real germ: a holomorphic `F` on a disk, agreeing with `g` on the reals,
  -- with the same order of vanishing at `0`.
  obtain ⟨F, ρ, hρ, hFan, hFeq, hFord⟩ := complexify_order g hg
  have hF0 : AnalyticAt ℂ F 0 := hFan 0 (by rw [Metric.mem_ball, dist_self]; exact hρ)
  -- Restricting the holomorphic germ `F` to the real line preserves the order.
  have hres := order_restrict F hF0
  -- The real restriction of `F` agrees with `t ↦ (g t : ℂ)` near `0`.
  have hev : (fun x : ℝ => F ((x : ℝ) : ℂ)) =ᶠ[𝓝 (0 : ℝ)] (fun t : ℝ => ((g t : ℝ) : ℂ)) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hρ] with t ht
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at ht
    exact hFeq t ht
  rw [← hFord, ← hres]
  exact (analyticOrderAt_congr hev).symm

end Work.WilE3.Taylor.Arc
