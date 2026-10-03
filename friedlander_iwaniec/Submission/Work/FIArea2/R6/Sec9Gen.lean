/-
# *FI* (9.1) for a general round-6 majorant and a general derivative constant

This module assembles the generalised §9 chain:

* `Work.FIArea2.R6.lemma_7_1_gen` — Lemma 7.1 for a majorant supported in `[A,B]` with
  `M/64 ≤ A`, `B ≤ 64 M`, `|F^{(j)}| ≤ Cder·M^{-j}`;
* `Work.FIArea2.R6.sec9_frequency_summable_gen`, `..._sum_bound_gen` — the `h ≠ (0,0)` tail bound;
* `Work.FIArea2.Ccount_smooth_eq_poisson` — the Poisson expansion (6.9), which needs only `C⁴`,
  compact support and `Δ ≠ 0`.

The result is *FI* (9.1) in the form `sec9_error_gen`, and the existential form
`sec9_error_of_pair_H_gen_aux` consumed by
`Work.FIArea2.R6.sec9_error_of_pair_H_gen`.
-/
import Mathlib
import Submission.Work.FIArea2.R6.Sec9GenCore
import Submission.Work.FIArea2.R6.Fint_gen
import Submission.Work.FIArea2.R6.vol_regG_le
import Submission.Work.FIArea2.R6.deriv4_pointwise_gen

set_option autoImplicit false

namespace Work.FIArea2.R6

open MeasureTheory
open scoped BigOperators
open scoped Topology

noncomputable section

/-- Non-negativity of the right-hand side of the generalised (9.1). -/
lemma sec9_gen_rhs_nonneg (Pa : Work.FITop.Params) (Cder : ℝ) (z1 z2 : GaussianInt)
    (hCder : 0 ≤ Cder) (hγ0 : 0 ≤ Work.FIArea2.gamOf z1 z2)
    (hγ1 : Work.FIArea2.gamOf z1 z2 < 1) :
    0 ≤ 4 * 10 ^ 13 * Cder * (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4))
      * ((((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) ^ 3)
          / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) * Real.sqrt Pa.M
          * Real.log (2 + 1 / (1 - (Work.FIArea2.gamOf z1 z2) ^ 2))
          * Work.FIArea2.Haver Pa z1 z2) := by
  have hHaver : 0 ≤ Work.FIArea2.Haver Pa z1 z2 := by
    rw [← HaverG_gamOf Pa z1 z2]
    exact HaverG_nonneg Pa _ z1 z2
  have h1γ : 0 < 1 - (Work.FIArea2.gamOf z1 z2) ^ 2 := by nlinarith
  have hlog : 0 ≤ Real.log (2 + 1 / (1 - (Work.FIArea2.gamOf z1 z2) ^ 2)) := by
    apply Real.log_nonneg
    have h1 : 0 < 1 / (1 - (Work.FIArea2.gamOf z1 z2) ^ 2) := by positivity
    linarith
  have hY : 0 ≤ (((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) ^ 3)
      / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) * Real.sqrt Pa.M
      * Real.log (2 + 1 / (1 - (Work.FIArea2.gamOf z1 z2) ^ 2))
      * Work.FIArea2.Haver Pa z1 z2 := by
    refine mul_nonneg (mul_nonneg (mul_nonneg ?_ (Real.sqrt_nonneg _)) hlog) hHaver
    exact div_nonneg (by positivity) (Nat.cast_nonneg _)
  have hX : 0 ≤ (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4)) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hA4 : (0 : ℝ) ≤ 4 * 10 ^ 13 := by norm_num
  exact mul_nonneg (mul_nonneg (mul_nonneg hA4 hCder) hX) hY

end

end Work.FIArea2.R6
