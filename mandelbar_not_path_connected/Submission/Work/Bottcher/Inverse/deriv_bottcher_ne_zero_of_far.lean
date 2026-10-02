import Mathlib
import Submission.Work.Bottcher.Contraction.norm_bottcherSeries_sub_le
import Submission.Work.Bottcher.Core.analyticAt_bottcher

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The derivative of the Böttcher coordinate is nonzero far out

The Böttcher coordinate of the tricorn (product formula) is

`bottcher c z = z * exp (bottcherSeries c z)`,

so its derivative is `exp (B_c z) * (1 + z * B_c'(z))`.  The exponential never vanishes, and on
the far region `64 (1 + ‖c‖) ≤ ‖z‖` the second factor is a unit: the derivative bound
`Work.Bottcher.Contraction.norm_tsum_btDeriv_le` gives
`‖B_c'(z)‖ ≤ 64 (1 + ‖c‖) / ‖z‖³`, hence `‖z * B_c'(z)‖ ≤ 1 / ‖z‖ ≤ 1 / 64 < 1`, so
`1 + z * B_c'(z) ≠ 0`.
-/

namespace Work.Bottcher.Inverse

open scoped Topology

theorem deriv_bottcher_ne_zero_of_far (c : ℂ) {z : ℂ}
    (hz : 64 * (1 + ‖c‖) ≤ ‖z‖) : deriv (Work.Bottcher.bottcher c) z ≠ 0 := by
  have hc : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  have hzpos : 0 < ‖z‖ := by
    have : (0 : ℝ) ≤ 1 + ‖c‖ := by linarith
    nlinarith
  have hz64 : (64 : ℝ) ≤ ‖z‖ := by
    have : (1 : ℝ) ≤ 1 + ‖c‖ := by linarith
    nlinarith
  have hfar : 4 * (1 + ‖c‖) ≤ ‖z‖ := by nlinarith
  set S' : ℂ := ∑' n : ℕ, Work.Bottcher.Core.btDeriv c n z with hS'def
  have hser : HasDerivAt (Work.Bottcher.bottcherSeries c) S' z :=
    Work.Bottcher.Contraction.hasDerivAt_bottcherSeries c z hfar
  have hexp : HasDerivAt (fun w : ℂ => Complex.exp (Work.Bottcher.bottcherSeries c w))
      (Complex.exp (Work.Bottcher.bottcherSeries c z) * S') z := hser.cexp
  have hderiv : deriv (Work.Bottcher.bottcher c) z
      = Complex.exp (Work.Bottcher.bottcherSeries c z) * (1 + z * S') := by
    have hmul : HasDerivAt (fun w : ℂ => w * Complex.exp (Work.Bottcher.bottcherSeries c w))
        (1 * Complex.exp (Work.Bottcher.bottcherSeries c z)
          + z * (Complex.exp (Work.Bottcher.bottcherSeries c z) * S')) z :=
      (hasDerivAt_id z).mul hexp
    have hsame : (fun w : ℂ => w * Complex.exp (Work.Bottcher.bottcherSeries c w))
        = Work.Bottcher.bottcher c := rfl
    rw [hsame] at hmul
    rw [hmul.deriv]
    ring
  rw [hderiv]
  refine mul_ne_zero (Complex.exp_ne_zero _) ?_
  have hS'bound : ‖S'‖ ≤ 64 * (1 + ‖c‖) / ‖z‖ ^ 3 :=
    Work.Bottcher.Contraction.norm_tsum_btDeriv_le c z hfar
  have hbound : ‖z * S'‖ ≤ 1 / 64 := by
    rw [norm_mul]
    calc ‖z‖ * ‖S'‖ ≤ ‖z‖ * (64 * (1 + ‖c‖) / ‖z‖ ^ 3) :=
          mul_le_mul_of_nonneg_left hS'bound (norm_nonneg z)
      _ = 64 * (1 + ‖c‖) / ‖z‖ ^ 2 := by
          field_simp
      _ ≤ 1 / 64 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  intro h
  have h1 : z * S' = -1 := by linear_combination h
  have h2 : ‖z * S'‖ = 1 := by rw [h1, norm_neg, norm_one]
  linarith [hbound, h2]

end Work.Bottcher.Inverse
