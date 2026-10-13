import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.FarHyp
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.FarReflect
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.far_vBound
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.sinDivDerivBounds
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.FarGDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of the low-order `v`-slots on the far window

For `k ≥ 2`, `γ ≥ 1` and `u`, `g` satisfying `FarHyp k γ u g`, the weighted square of every
low slot `∂^m (u / cos θ)`, `m ≤ k`, is integrable on the far window `[3π/8, π/2]` against
`qW k γ θ = sin(2θ)^{2k-γ}`.

This is the *integrability* half of the far-window estimate (`far_vBound`), separated out so
that the far slots can be fed to the dominated-convergence arguments of the angular estimate.

Route (the reflected variable `x = π/2 - θ ∈ [0, π/8]`, `shiftV u x = u(π/2-x)/sin x`,
`shiftU u x = u(π/2-x)`, `secH x = x/sin x`):

* `shiftV u = (shiftU u / ·) * secH` near the interior of `(0, π/8)`, so Leibniz
  (`shiftV_deriv_sq_le`) bounds `(∂^m (shiftV u))²` pointwise by a constant times
  `∑_{i ≤ m} (∂^i (shiftU u / ·))²`, the `secH`-derivatives being bounded by `K`
  (`sinDivDerivBounds`);
* each summand, multiplied by `sin(2x)^{2k-γ}`, is integrable on `(0, π/8]`
  (`integrableOn_sinWeight_xDivX`, i.e. the weighted Hardy division followed by the slots `H1`,
  `H3`, `H4` of `FarHyp`);
* `a.e.`-monotonicity (`Integrable.mono'`) and the reflection transfer
  (`MeasurePreserving.integrableOn_comp_preimage`) give the claim on `farSet`.
-/

namespace Work.FTS.EllipticEst.remov

open scoped Real Topology
open MeasureTheory Set Filter

theorem farVIntLow (k : ℕ) (hk : 2 ≤ k) :
    ∀ (γ : ℝ) (u g : ℝ → ℝ),
      Work.FTS.EllipticEst.remov.TopCoreB.FarHyp k γ u g →
      ∀ m : ℕ, m ≤ k →
        MeasureTheory.IntegrableOn
          (fun θ : ℝ => (iteratedDeriv m (Work.FTS.EllipticEst.remov.TopCoreB.vF u) θ) ^ 2
            * Work.FTS.EllipticEst.remov.TopCoreB.qW k γ θ)
          Work.FTS.EllipticEst.remov.TopCoreB.farSet := by
  intro γ u g hF m hm
  obtain ⟨K, hKpos, hKb⟩ := TopCoreB.sinDivDerivBounds k
  have hK : ∀ i ≤ m, ∀ y ∈ Set.Ioc 0 TopCoreB.xEnd, |iteratedDeriv i TopCoreB.secH y| ≤ K :=
    fun i hi y hy => hKb i (le_trans hi hm) y hy
  have huC : ContDiffOn ℝ m u (Set.Ioo 0 (Real.pi / 2)) :=
    hF.huC.of_le (by exact_mod_cast (by omega : m ≤ k + 2))
  set A : ℝ := ((2 : ℝ) ^ m * K) ^ 2 * ((m + 1 : ℕ) : ℝ) with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  set G : ℝ → ℝ := fun x => A * ∑ i ∈ Finset.range (m + 1),
      ((iteratedDeriv i (fun y : ℝ => TopCoreB.shiftU u y / y) x) ^ 2
        * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)) with hG
  have hGint : IntegrableOn G (Set.Ioc 0 TopCoreB.xEnd) := by
    rw [hG]
    exact (MeasureTheory.integrable_finsetSum (Finset.range (m + 1))
      (fun i hi => TopCoreB.integrableOn_sinWeight_xDivX hk hF
        (le_trans (by simpa [Finset.mem_range] using hi) hm))).const_mul A
  -- smoothness of the reflected `v` on the interior of `(0, π/8)`
  have hsv : ContDiffOn ℝ m (TopCoreB.shiftV u) (Set.Ioo 0 TopCoreB.xEnd) := by
    have h1 : ContDiffOn ℝ m (TopCoreB.shiftU u) (Set.Ioo 0 TopCoreB.xEnd) :=
      TopCoreB.contDiffOn_shiftU huC
    have h2 : ContDiffOn ℝ m (fun x : ℝ => Real.sin x) (Set.Ioo 0 TopCoreB.xEnd) :=
      Real.contDiff_sin.contDiffOn
    have h3 : ContDiffOn ℝ m (TopCoreB.shiftU u / fun x : ℝ => Real.sin x)
        (Set.Ioo 0 TopCoreB.xEnd) :=
      h1.div h2 (fun x hx => ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hx.1
        (by linarith [hx.2, TopCoreB.xEnd_lt_pi_half, Real.pi_pos])))
    have hfun : (TopCoreB.shiftU u / fun x : ℝ => Real.sin x) = TopCoreB.shiftV u := by
      funext x; simp [TopCoreB.shiftV, Pi.div_apply]
    rw [hfun] at h3
    exact h3
  -- the shifted integrand is integrable on `(0, π/8]`
  have hshift : IntegrableOn (fun x => (iteratedDeriv m (TopCoreB.shiftV u) x) ^ 2
      * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)) (Set.Ioc 0 TopCoreB.xEnd) := by
    have hsm : AEStronglyMeasurable (fun x => (iteratedDeriv m (TopCoreB.shiftV u) x) ^ 2
        * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
        (volume.restrict (Set.Ioc 0 TopCoreB.xEnd)) :=
      TopCoreB.aestronglyMeasurable_Ioc_of_continuousOn
        (((HardyFin.continuousOn_iteratedDeriv_Ioo_fin' hsv le_rfl).pow 2).mul
          (TopCoreB.continuousOn_sin_rpow (p := 2 * (k : ℝ) - γ)))
    refine hGint.mono' hsm ?_
    have hsub : ∀ᵐ x ∂(volume.restrict (Set.Ioc 0 TopCoreB.xEnd)),
        x ∈ Set.Ioo 0 TopCoreB.xEnd := by
      rw [← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := volume) (a := (0 : ℝ))
        (b := TopCoreB.xEnd))]
      exact (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => hx)
    filter_upwards [hsub] with x hx
    have hw_nn : 0 ≤ Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ) :=
      Real.rpow_nonneg (TopCoreB.sin_two_nonneg_Ioc ⟨hx.1, le_of_lt hx.2⟩) _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hw_nn)]
    have h1 := TopCoreB.shiftV_deriv_sq_le (u := u) (m := m) (K := K) hK huC hx
    calc (iteratedDeriv m (TopCoreB.shiftV u) x) ^ 2
          * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)
        ≤ (((2 : ℝ) ^ m * K) ^ 2 * ((m + 1 : ℕ) : ℝ)
            * ∑ i ∈ Finset.range (m + 1),
                (iteratedDeriv i (fun y : ℝ => TopCoreB.shiftU u y / y) x) ^ 2)
            * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ) :=
          mul_le_mul_of_nonneg_right h1 hw_nn
      _ = G x := by
          simp only [hG, hA]
          rw [← Finset.sum_mul]
          ring
  -- pass from `(0, π/8]` to `[0, π/8]`
  have hIcc : IntegrableOn (fun x => (iteratedDeriv m (TopCoreB.shiftV u) x) ^ 2
      * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)) (Set.Icc 0 TopCoreB.xEnd) :=
    (integrableOn_congr_set_ae (Ioc_ae_eq_Icc (μ := volume) (a := (0 : ℝ))
      (b := TopCoreB.xEnd))).mp hshift
  -- reflect back to the far window
  refine (MeasurePreserving.integrableOn_comp_preimage (μ := volume) (ν := volume)
    TopCoreB.measurePreserving_reflectC TopCoreB.measurableEmbedding_reflectC
    (s := TopCoreB.farSet)).mp ?_
  rw [TopCoreB.preimage_reflectC_farSet]
  refine hIcc.congr_fun (fun x _ => ?_) measurableSet_Icc
  exact (TopCoreB.farSet_integrand_eq k γ m u x).symm

end Work.FTS.EllipticEst.remov
