import Mathlib
import Submission.Work.Koebe.gwDefs
import Submission.Work.Koebe.signedArea_coeff_bound

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Uniform convergence of the Taylor truncations of a function holomorphic on the unit disc

For `H : ℂ → ℂ` complex differentiable on the open unit ball and `0 < r < 1`, the Taylor
polynomials

`z ↦ ∑_{n < N} gco H n * z ^ n`,   where `gco H n = (n!)⁻¹ * iteratedDeriv n H 0`,

converge uniformly to `H` on the circle `‖z‖ = r`, and their derivatives converge uniformly to
`deriv H` there.

The proof is the standard one.  Since `H` is holomorphic on the unit disc, the same holds on a
closed disc of radius `R < 1`, so `H` admits a power series on the open disc of radius `R`
(`DifferentiableOn.hasFPowerSeriesOnBall`).  The coefficients of that power series agree with the
Taylor coefficients `gco H n` (this is `AnalyticAt.hasFPowerSeriesAt` together with the uniqueness
of the power series, `HasFPowerSeriesAt.eq_formalMultilinearSeries`, after rewriting the
multilinear series `ofScalars ℂ (gco H)` as a scalar series).  Picking an intermediate radius
`r < s < R`, `HasFPowerSeriesOnBall.tendstoUniformlyOn` gives uniform convergence of the partial
sums on the disc `‖z‖ < s`.

Restricting to the sphere of radius `r` gives the first conjunct.  For the second conjunct,
uniform convergence on the disc `‖z‖ < s` is in particular locally uniform convergence, so
`TendstoLocallyUniformlyOn.deriv` yields locally uniform convergence of the derivatives, and a
compact (the sphere) test turns this into uniform convergence on the sphere.
-/

namespace Work.Koebe

open Complex Metric Set Filter
open scoped Topology

/-- **Uniform convergence of the Taylor truncations on a circle.** -/
theorem gwTruncUniformOnSphere (H : ℂ → ℂ) (hH : DifferentiableOn ℂ H (Metric.ball 0 1))
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    TendstoUniformlyOn
        (fun N z => ∑ n ∈ Finset.range N, Work.Koebe.gco H n * z ^ n)
        H atTop (Metric.sphere 0 r) ∧
      TendstoUniformlyOn
        (fun N z => deriv (fun w : ℂ => ∑ n ∈ Finset.range N, Work.Koebe.gco H n * w ^ n) z)
        (deriv H) atTop (Metric.sphere 0 r) := by
  -- An intermediate radius `R < 1` on whose closed disc the power series is available.
  have hRpos : (0 : ℝ) < (r + 1) / 2 := by linarith
  let R : NNReal := ⟨(r + 1) / 2, hRpos.le⟩
  have hRcoe : (R : ℝ) = (r + 1) / 2 := rfl
  have hrR : r < (R : ℝ) := by rw [hRcoe]; linarith
  have hR1 : (R : ℝ) < 1 := by rw [hRcoe]; linarith
  have hRpos' : 0 < R := by
    rw [← NNReal.coe_pos, hRcoe]
    exact hRpos
  -- The power series provided by Cauchy's theorem on the closed disc of radius `R`.
  have hps0 : HasFPowerSeriesOnBall H (cauchyPowerSeries H 0 (R : ℝ)) 0 (↑R : ENNReal) :=
    (hH.mono (closedBall_subset_ball hR1)).hasFPowerSeriesOnBall hRpos'
  -- `H` is analytic at `0`, with a scalar power series whose coefficients are the Taylor
  -- coefficients.
  have hana : AnalyticAt ℂ H 0 := hH.analyticAt (ball_mem_nhds (0 : ℂ) (by norm_num))
  have hana2 : HasFPowerSeriesAt H
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n => iteratedDeriv n H 0 / (n.factorial : ℂ))) 0 :=
    hana.hasFPowerSeriesAt
  -- Uniqueness of the power series identifies the two series.
  have heq : FormalMultilinearSeries.ofScalars ℂ
      (fun n => iteratedDeriv n H 0 / (n.factorial : ℂ)) = cauchyPowerSeries H 0 (R : ℝ) :=
    HasFPowerSeriesAt.eq_formalMultilinearSeries hana2 hps0.hasFPowerSeriesAt
  have hcoef : (fun n => iteratedDeriv n H 0 / (n.factorial : ℂ)) = fun n => gco H n := by
    funext n; rw [gco, div_eq_mul_inv, mul_comm]
  have hps : HasFPowerSeriesOnBall H (FormalMultilinearSeries.ofScalars ℂ (gco H)) 0
      (↑R : ENNReal) := by
    have hser : (FormalMultilinearSeries.ofScalars ℂ (gco H)) = cauchyPowerSeries H 0 (R : ℝ) := by
      rw [show (gco H) = (fun n => iteratedDeriv n H 0 / (n.factorial : ℂ)) from hcoef.symm, heq]
    rw [hser]; exact hps0
  -- An intermediate radius `r < s < R`: the partial sums converge uniformly on the disc of
  -- radius `s`, which contains the sphere of radius `r`.
  have hs_pos : (0 : ℝ) < (r + (R : ℝ)) / 2 := by linarith
  let s : NNReal := ⟨(r + (R : ℝ)) / 2, hs_pos.le⟩
  have hsv : (s : ℝ) = (r + (R : ℝ)) / 2 := rfl
  have hrs : r < (s : ℝ) := by rw [hsv]; linarith
  have hsR : (s : ℝ) < (R : ℝ) := by rw [hsv]; linarith
  have hsR' : (↑s : ENNReal) < (↑R : ENNReal) := by exact_mod_cast hsR
  have hconv := hps.tendstoUniformlyOn (r' := s) hsR'
  -- The partial sums of the scalar series are the Taylor truncations.
  have hpart : ∀ N z, (FormalMultilinearSeries.ofScalars ℂ (gco H)).partialSum N z
      = ∑ n ∈ Finset.range N, gco H n * z ^ n := by
    intro N z
    simp only [FormalMultilinearSeries.partialSum]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp [FormalMultilinearSeries.ofScalars, ContinuousMultilinearMap.mkPiAlgebraFin_apply]
  have hconv' : TendstoUniformlyOn (fun N z => ∑ n ∈ Finset.range N, gco H n * z ^ n)
      H atTop (Metric.ball 0 (s : ℝ)) := by
    have h2 := hconv.congr (Eventually.of_forall fun N => fun z _ => (hpart N z))
    exact h2.congr_right (fun z _ => by simp)
  refine ⟨hconv'.mono (sphere_subset_ball hrs), ?_⟩
  -- Locally uniform convergence on the disc of radius `s`, hence locally uniform convergence of
  -- the derivatives by Weierstrass' theorem.
  have hloc : TendstoLocallyUniformlyOn (fun N z => ∑ n ∈ Finset.range N, gco H n * z ^ n)
      H atTop (Metric.ball 0 (s : ℝ)) := hconv'.tendstoLocallyUniformlyOn
  have hdiff : ∀ᶠ N in atTop, DifferentiableOn ℂ
      (fun z => ∑ n ∈ Finset.range N, gco H n * z ^ n) (Metric.ball 0 (s : ℝ)) :=
    Eventually.of_forall fun N => by fun_prop
  have hderiv := hloc.deriv hdiff Metric.isOpen_ball
  -- A compact set (the sphere) upgrades locally uniform convergence to uniform convergence.
  have hfin := (tendstoLocallyUniformlyOn_iff_forall_isCompact Metric.isOpen_ball).mp hderiv
      (Metric.sphere 0 r) (sphere_subset_ball hrs) (isCompact_sphere 0 r)
  simpa [Function.comp_def] using hfin

end Work.Koebe
