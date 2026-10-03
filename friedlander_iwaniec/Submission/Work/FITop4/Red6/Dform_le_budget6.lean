/-
# `Work.FITop4.Red6.Dform_le_budget6` — the (5.18) form against the (5.20) budget

Round-4's `Comp.Dform_le_budget` at the corrected (round-6) objects: the main term `D₀` is the
(9.11) sum on the *count* kernel `G0 = Cnt/|Δ|` with the (7.10) normalisation `f̂(0) = Fhat6`
(`Defs6`), `T(β)` is the (10.5) sum on the same kernel, and the three cuts (10.15)–(10.17) carry
the ratio symbol `(z₂/z₁|d)`.  The chain is identical to round 4's:

* `Dform ≤ Dstar + T/8`                       — (5.22), `AreaBounds6`'s first conjunct;
* `Dstar ≤ D₀.re + T/8`                       — (9.10), `AreaBounds6`'s second;
* `D₀.re ≤ Fhat6·N^{-1/2}·T(β).re + T/8`      — (10.10), `AreaBounds6`'s third;
* `‖T(β)‖ ≤ (cU+cV+cW)(N²(log N)^{-σ} + P^{-1}N²log N)` — Proposition 10.2
  (`Red6.prop102_of_UVW6`, fed by the (10.14) partition `Red6.Tbeta_partition` and
  `AreaBounds6`'s last three conjuncts);
* `Fhat6 ≤ 4√M` (7.7) and the fourth `NumHyp` conjunct close the main term.

Hence `Dform ≤ (1 + cU + cV + cW)·Tbudget`.
-/
import Mathlib
import Submission.Work.FITop4.Defs6
import Submission.Work.FITop4.Areas6
import Submission.Work.FITop4.Red6.Tbeta_partition

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.FITop4.Red6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- (7.7): the discrete mean value `f̂(0) = Σ_u f(u)u^{-1/2}` of a majorant is non-negative. -/
private lemma fhat6_nonneg (Pa : Work.FITop.Params) (f : ℤ → ℝ)
    (h : Work.FITop3.IsMajorant Pa (f)) :
    0 ≤ Work.FITop3.Fhat Pa f := by
  show 0 ≤ Work.FITop3.Fhat Pa (f)
  rw [Work.FITop3.Fhat]
  exact Finset.sum_nonneg fun u _ => div_nonneg (h.1 u) (Real.sqrt_nonneg _)

/-- `N^{-1/2}·N² = N^{3/2}` for `N > 0`. -/
private lemma rpow_neg_half_mul_sq (N : ℝ) (hN : 0 < N) :
    N ^ (-(1 : ℝ) / 2) * N ^ 2 = N ^ ((3 : ℝ) / 2) := by
  rw [show N ^ 2 = N ^ (((2 : ℕ)) : ℝ) by rw [Real.rpow_natCast], ← Real.rpow_add hN,
    show -(1 : ℝ) / 2 + ((2 : ℕ) : ℝ) = (3 : ℝ) / 2 by norm_num]

end

end Work.FITop4.Red6

