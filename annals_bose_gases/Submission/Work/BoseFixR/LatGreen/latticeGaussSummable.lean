import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixR.LatGreen.LGFormDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.LatGreen.latticeGaussSummable`

The shifted lattice Gaussian sum `Σ_{n ∈ ℤ³} exp(−c‖u − n‖²)` is summable for every centre
`u : ℝ³` and every `c > 0`.

This is the "shift the centre" companion of
`Work.BoseFixR.LatGreen.summable_exp_neg_norm_latVec_sq` (which is the case `u = 0`), and it is
what lets Tonelli/Fubini manipulations of the periodised heat kernel `heatPeriod` be justified
for a general `u ∈ ℝ³` and not only on a fundamental domain.

The proof is the elementary two-sided bound

`‖n‖² ≤ 2‖u‖² + 2‖u − n‖²`   (`(n − u) + u = n`, `‖a + b‖ ≤ ‖a‖ + ‖b‖`, `(a+b)² ≤ 2a² + 2b²`),

which turns the summand into a constant times `exp(−(c/2)‖n‖²)`, a summable majorant by the
`u = 0` case.
-/

namespace Work.BoseFixR.LatGreen

/-- **The elementary shift bound**: for every `u : ℝ³` and lattice point `n`,
`‖n‖² ≤ 2‖u‖² + 2‖u − n‖²`.
(Write `n = (n − u) + u` and use `‖a + b‖² ≤ 2a² + 2b²`.) -/
private lemma norm_latVec_sq_le_two_mul (u : EuclideanSpace ℝ (Fin 3)) (n : Fin 3 → ℤ) :
    ‖latVec n‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖u - latVec n‖ ^ 2 := by
  have h1 : ‖latVec n‖ ≤ ‖latVec n - u‖ + ‖u‖ := by
    have h := norm_add_le (latVec n - u) u
    rwa [sub_add_cancel] at h
  have h3 : ‖latVec n‖ ^ 2 ≤ (‖latVec n - u‖ + ‖u‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h4 : (‖latVec n - u‖ + ‖u‖) ^ 2 ≤ 2 * (‖latVec n - u‖ ^ 2 + ‖u‖ ^ 2) := by
    nlinarith [sq_nonneg (‖latVec n - u‖ - ‖u‖)]
  have h5 : ‖latVec n - u‖ = ‖u - latVec n‖ := norm_sub_rev (latVec n) u
  rw [h5] at h3 h4
  linarith

theorem latticeGaussSummable (u : EuclideanSpace ℝ (Fin 3)) {c : ℝ} (hc : 0 < c) :
    Summable (fun n : Fin 3 → ℤ => Real.exp (-c * ‖u - latVec n‖ ^ 2)) := by
  have hbase : Summable (fun n : Fin 3 → ℤ => Real.exp (-(c / 2) * ‖latVec n‖ ^ 2)) :=
    summable_exp_neg_norm_latVec_sq (by linarith)
  have hg : Summable (fun n : Fin 3 → ℤ =>
      Real.exp (c * ‖u‖ ^ 2) * Real.exp (-(c / 2) * ‖latVec n‖ ^ 2)) :=
    hbase.mul_left _
  refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_) hg
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hb := norm_latVec_sq_le_two_mul u n
  nlinarith [hb, hc]

end Work.BoseFixR.LatGreen
