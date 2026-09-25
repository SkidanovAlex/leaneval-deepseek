import Mathlib
import Submission.Work.BourgainPlan.Maximal.MtaDefs
import Submission.Work.BourgainPlan.MtaLin.integrable_tildeFam

/-!
# A.e. measurability of the norm of the block operator `mtaBlkOp`

The block operator

`mtaBlkOp P K ε s u = ∑_{k<K} S̃_{L k} (ε k · S_{L k} (D_k u))`,  `L k = deg P · k + s`,

is a finite sum of *compositions* of two Littlewood–Paley projections (`S̃` the projection with the
wider bump `dyadTilde`, `S` the one with the symbol `dyadPsi`), applied to the dyadic differences
`D_k u = σ_{2^k} u − σ_{2^{k+1}} u` of the curve averages of `u`.

For `u ∈ L¹(ℝ)` every ingredient is an honest `L¹` function:

* `σ_N u` is integrable for `u ∈ L¹` (`memLp_curveSigma'`), hence so is `D_k u` (`integrable_curveSigma`);
* the projection `S_{L k} (D_k u)` of an `L¹` function is integrable (`integrable_dyadicProj`), so
  `ε k · S_{L k} (D_k u)` is integrable, and the outer projection `S̃_{L k}` of an `L¹` function is
  continuous (`continuous_dyadicProj_dyadTilde`), hence a.e. strongly measurable.

Summing over the finite range `k < K` yields the a.e. strong measurability of `mtaBlkOp P K ε s u`,
and taking the extended norm gives the statement.
-/

open MeasureTheory
open scoped ENNReal BigOperators FourierTransform

namespace Work.BourgainPlan.MtaLin

open Work.BourgainPlan.Maximal

/-- The curve average `curveSigma P N g` of an integrable `g` is integrable.  This is the `p = 1`
instance of `memLp_curveSigma'`. -/
lemma integrable_curveSigma (P : Polynomial ℤ) (N : ℕ) {g : ℝ → ℂ}
    (hg : MeasureTheory.Integrable g) :
    MeasureTheory.Integrable (curveSigma P N g) := by
  refine MeasureTheory.memLp_one_iff_integrable.mp ?_
  have h1 : MemLp g (ENNReal.ofReal (1:ℝ)) (volume : Measure ℝ) := by
    simpa using (MeasureTheory.memLp_one_iff_integrable.mpr hg : MemLp g 1 (volume : Measure ℝ))
  have h := (memLp_curveSigma' P N (le_refl (1:ℝ)) h1).1
  simpa using h

/-- The projection with the wide bump `dyadTilde` of an integrable function is **continuous**: its
symbol `ξ ↦ ψ̃(2^m ξ) · 𝓕G(ξ)` is continuous with compact support, hence integrable. -/
lemma continuous_dyadicProj_dyadTilde {m : ℤ} {G : ℝ → ℂ} (hG : MeasureTheory.Integrable G) :
    Continuous (dyadicProj dyadTilde m G) :=
  Commons.Analysis.Fourier.continuous_fourierInv_of_integrable _
    (((continuous_tildeFam m).mul
        (Commons.Analysis.Fourier.continuous_fourier_of_integrable G hG))
      |>.integrable_of_hasCompactSupport ((hasCompactSupport_tildeFam m).mul_right))

theorem mtaBlkOp_aemeasurable (P : Polynomial ℤ) (K : ℕ) (ε : ℕ → ℂ) (s : ℤ) {u : ℝ → ℂ} (hu : MeasureTheory.Integrable u) :
    AEMeasurable (fun x : ℝ => ‖Work.BourgainPlan.Maximal.mtaBlkOp P K ε s u x‖ₑ) (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  have hmeas : AEStronglyMeasurable (mtaBlkOp P K ε s u) (volume : Measure ℝ) := by
    have hterm : ∀ k ∈ Finset.range K, AEStronglyMeasurable (fun x : ℝ =>
        dyadicProj dyadTilde ((P.natDegree : ℤ) * (k : ℤ) + s)
          (fun y => ε k * dyadicProj dyadPsi ((P.natDegree : ℤ) * (k : ℤ) + s) (dyadD P k u) y) x)
        (volume : Measure ℝ) := by
      intro k _
      have hD : Integrable (dyadD P k u) := by
        unfold dyadD
        exact (integrable_curveSigma P (2^k) hu).sub
          (integrable_curveSigma P (2^(k+1)) hu)
      exact (continuous_dyadicProj_dyadTilde
        ((integrable_dyadicProj (m := (P.natDegree : ℤ) * (k : ℤ) + s) hD).const_mul
          (ε k))).aestronglyMeasurable
    have hsum := Finset.aestronglyMeasurable_sum (Finset.range K) hterm
    have hfun : (∑ k ∈ Finset.range K, fun x : ℝ =>
        dyadicProj dyadTilde ((P.natDegree : ℤ) * (k : ℤ) + s)
          (fun y => ε k * dyadicProj dyadPsi ((P.natDegree : ℤ) * (k : ℤ) + s) (dyadD P k u) y) x)
        = mtaBlkOp P K ε s u := by
      funext x
      simp only [mtaBlkOp, Finset.sum_apply]
    rw [← hfun]
    exact hsum
  exact hmeas.aemeasurable.enorm

end Work.BourgainPlan.MtaLin
