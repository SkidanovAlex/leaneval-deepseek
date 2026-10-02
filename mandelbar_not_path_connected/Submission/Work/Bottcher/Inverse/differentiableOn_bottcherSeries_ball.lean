/-
# Differentiability of the Böttcher series on a far ball

The Böttcher series of the tricorn at parameter `c` is

`bottcherSeries c z = Σ_n 4^{-(n+1)} log (normFactor c ((pMap c)^[n] z))`,

a series of holomorphic functions of `z`.  This file shows that it is
differentiable on any ball on which the `p_c`-orbit of every point stays far
from the origin, in the precise sense `2 + ‖c‖ ≤ ‖z‖`: on such a region the
`n`-th term is holomorphic with derivative `btDeriv c n y` and every derivative
is dominated by the summable geometric majorant
`uSeq c n = (8 ‖c‖ + 8) (1/4)^n`, so the Weierstrass theorem for series of
holomorphic functions (`hasDerivAt_tsum_of_isPreconnected`) applies.

This is the local holomorphy statement used to build the *inverse* Böttcher
coordinate away from the critical value.
-/
import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.Core.analyticAt_bottcher

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Function Metric
open scoped Topology ComplexConjugate

namespace Work.Bottcher.Inverse

/-- The Böttcher series is differentiable on any ball `Metric.ball u r` on which
every point satisfies `2 + ‖c‖ ≤ ‖y‖`.

The terms `bottcherTerm c n` are holomorphic on that ball (their derivatives
being `Work.Bottcher.Core.btDeriv c n`), and the derivatives are uniformly
dominated by the summable sequence `Work.Bottcher.Core.uSeq c`, so the
Weierstrass theorem `hasDerivAt_tsum_of_isPreconnected` yields the conclusion. -/
theorem differentiableOn_bottcherSeries_ball (c u : ℂ) {r : ℝ} (hr : 0 < r)
    (h : ∀ y ∈ Metric.ball u r, 2 + ‖c‖ ≤ ‖y‖) :
    DifferentiableOn ℂ (Work.Bottcher.bottcherSeries c) (Metric.ball u r) := by
  have hu_mem : u ∈ Metric.ball u r := Metric.mem_ball_self hr
  have h1u : 1 + ‖c‖ ≤ ‖u‖ := by have := h u hu_mem; linarith [norm_nonneg c]
  -- The geometric majorant of the derivatives is summable.
  have hsum_u : Summable (Work.Bottcher.Core.uSeq c) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) < 1)).mul_left (8 * ‖c‖ + 8)
  -- The series converges at the centre of the ball.
  have hg0 : Summable fun n => Work.Bottcher.bottcherTerm c n u := by
    refine Summable.of_norm_bounded (g := fun n => (15 / 8) * (1 / 4) ^ n) ?_ ?_
    · exact (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
        (by norm_num : (1 / 4 : ℝ) < 1)).mul_left (15 / 8)
    · intro n
      exact Work.Bottcher.Core.norm_term_le c u h1u n
  -- Every term is holomorphic on the ball, with derivative `btDeriv c n y`.
  have hderiv : ∀ n y, y ∈ Metric.ball u r →
      HasDerivAt (fun z => Work.Bottcher.bottcherTerm c n z)
        (Work.Bottcher.Core.btDeriv c n y) y :=
    fun n y hy => Work.Bottcher.Core.hasDerivAt_bottcherTerm c y n (fun k => by
      have h2 := Work.Bottcher.Core.pMap_norm_iterate_ge c y (h y hy) k
      linarith [norm_nonneg c])
  -- ... and the derivatives are uniformly bounded by `uSeq c`.
  have hbound : ∀ n y, y ∈ Metric.ball u r →
      ‖Work.Bottcher.Core.btDeriv c n y‖ ≤ Work.Bottcher.Core.uSeq c n :=
    fun n y hy => Work.Bottcher.Core.norm_btDeriv_le c y (h y hy) n
  intro y hy
  have hd : HasDerivAt (Work.Bottcher.bottcherSeries c)
      (∑' n, Work.Bottcher.Core.btDeriv c n y) y :=
    hasDerivAt_tsum_of_isPreconnected hsum_u Metric.isOpen_ball
      (convex_ball u r).isPreconnected hderiv hbound hu_mem hg0 hy
  exact hd.differentiableAt.differentiableWithinAt

end Work.Bottcher.Inverse
