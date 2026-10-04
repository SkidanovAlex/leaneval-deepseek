import Mathlib
import Submission.Work.Diff.C.cosSqrt_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Properties of the entire function `cosSqrt s = cos (√s)`

`cosSqrt s = ∑' n, (-1)^n s^n / (2n)!` is the entire function whose value at `s ≥ 0` is
`Real.cos (Real.sqrt s)` (equivalently `cosSqrt (x^2) = Real.cos x`).  It is analytic on all
of `ℝ`, hence in particular smooth at `0`, where `s ↦ Real.cos (Real.sqrt s)` is only
one-sided smooth.

The proof is via the API for scalar power series `∑ cᵢ • xⁱ`
(`FormalMultilinearSeries.ofScalars`): the coefficients `(-1)^n/(2n)!` give a series of
infinite radius of convergence (dominated by `Real.cosh (√r)`), hence an analytic — and so
`C^∞` — function, whose derivative at `0` is the coefficient of `x¹`.
-/

namespace Work.Diff.C

open scoped BigOperators ContDiff NNReal

/-- The scalar coefficients `(-1)^n/(2n)!` of the series defining `cosSqrt`. -/
noncomputable def cosCoef : ℕ → ℝ := fun n => (-1) ^ n / ((Nat.factorial (2 * n) : ℕ) : ℝ)

private lemma norm_cosCoef (n : ℕ) :
    ‖cosCoef n‖ = (((Nat.factorial (2 * n) : ℕ) : ℝ))⁻¹ := by
  rw [cosCoef, Real.norm_eq_abs, abs_div, abs_pow]
  simp

private lemma summable_norm_cosCoef (r : ℝ≥0) :
    Summable fun n => ‖cosCoef n‖ * (r : ℝ) ^ n := by
  -- `(√r)^(2n) = r^n`, so this is `Real.hasSum_cosh (√r)`.
  have h := (Real.hasSum_cosh (Real.sqrt (r : ℝ))).summable
  refine h.congr (fun n => ?_)
  have hsq : (Real.sqrt (r : ℝ)) ^ (2 * n) = (r : ℝ) ^ n := by
    rw [pow_mul, Real.sq_sqrt (r : ℝ≥0).coe_nonneg]
  rw [hsq, norm_cosCoef, div_eq_mul_inv, mul_comm]

/-- The scalar power series `∑ (-1)^n x^n/(2n)!` has infinite radius of convergence. -/
private lemma radius_cosCoef :
    (FormalMultilinearSeries.ofScalars ℝ cosCoef).radius = ⊤ :=
  FormalMultilinearSeries.radius_eq_top_of_summable_norm _ (fun r => by
    simpa only [FormalMultilinearSeries.ofScalars_norm] using summable_norm_cosCoef r)

/-- `cosSqrt` is the sum of the scalar power series with coefficients `cosCoef`. -/
private lemma cosSqrt_eq_ofScalars_sum :
    cosSqrt = (FormalMultilinearSeries.ofScalars ℝ cosCoef).sum := by
  funext s
  rw [FormalMultilinearSeries.sum]
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, cosSqrt]
  refine tsum_congr fun n => ?_
  rw [cosCoef, div_mul_eq_mul_div]

/-- Currying a `1`-multilinear map on `ℝ`. -/
private lemma curry_fin1_apply (f : ℝ[×1]→L[ℝ]ℝ) (z : ℝ) :
    (continuousMultilinearCurryFin1 ℝ ℝ ℝ f) z = f (fun _ => z) := by
  rw [continuousMultilinearCurryFin1_apply]
  congr 1

/-- The derivative of the scalar power series at `0` is its linear coefficient `-1/2`. -/
private lemma hasDerivAt_ofScalars_sum :
    HasDerivAt (FormalMultilinearSeries.ofScalars ℝ cosCoef).sum (-(1 / 2)) 0 := by
  have hfp : HasFPowerSeriesOnBall (FormalMultilinearSeries.ofScalars ℝ cosCoef).sum
      (FormalMultilinearSeries.ofScalars ℝ cosCoef) 0
      (FormalMultilinearSeries.ofScalars ℝ cosCoef).radius :=
    FormalMultilinearSeries.hasFPowerSeriesOnBall _
      (by rw [radius_cosCoef]; exact ENNReal.zero_lt_top)
  have hd := hfp.hasFPowerSeriesAt.hasFDerivAt.hasDerivAt
  rw [curry_fin1_apply] at hd
  rw [FormalMultilinearSeries.ofScalars_apply_eq] at hd
  convert hd using 1
  norm_num [cosCoef, Nat.factorial]

/-- `cosSqrt` is analytic everywhere (with infinite radius of convergence). -/
private lemma analyticOnNhd_cosSqrt :
    AnalyticOnNhd ℝ (FormalMultilinearSeries.ofScalars ℝ cosCoef).sum Set.univ := by
  have hfp : HasFPowerSeriesOnBall (FormalMultilinearSeries.ofScalars ℝ cosCoef).sum
      (FormalMultilinearSeries.ofScalars ℝ cosCoef) 0
      (FormalMultilinearSeries.ofScalars ℝ cosCoef).radius :=
    FormalMultilinearSeries.hasFPowerSeriesOnBall _
      (by rw [radius_cosCoef]; exact ENNReal.zero_lt_top)
  intro x _
  refine hfp.analyticAt_of_mem ?_
  rw [Metric.mem_eball, radius_cosCoef]
  exact lt_top_iff_ne_top.mpr (edist_ne_top x 0)

theorem cosSqrt_props :
    ContDiff ℝ ∞ Work.Diff.C.cosSqrt ∧ Work.Diff.C.cosSqrt 0 = 1 ∧
      HasDerivAt Work.Diff.C.cosSqrt (-(1 / 2)) 0 ∧
      (∀ x : ℝ, Work.Diff.C.cosSqrt (x ^ 2) = Real.cos x) := by
  have hsum := cosSqrt_eq_ofScalars_sum
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hsum]
    exact analyticOnNhd_cosSqrt.contDiff
  · rw [hsum, FormalMultilinearSeries.sum]
    simp only [FormalMultilinearSeries.ofScalars_apply_eq]
    rw [show (fun n => cosCoef n • (0 : ℝ) ^ n) = fun n => if n = 0 then (1 : ℝ) else 0 by
      funext n
      rcases eq_or_ne n 0 with rfl | hn
      · simp [cosCoef, Nat.factorial]
      · simp [hn]]
    simp
  · rw [hsum]
    exact hasDerivAt_ofScalars_sum
  · intro x
    rw [Real.cos_eq_tsum]
    simp only [cosSqrt]
    refine tsum_congr fun n => ?_
    rw [← pow_mul]

end Work.Diff.C
