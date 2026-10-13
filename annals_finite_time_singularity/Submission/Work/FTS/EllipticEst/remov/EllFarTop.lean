import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.FarHyp
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.FarReflect
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.far_vBound
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.sinDivDerivBounds
import Submission.Work.FTS.EllipticEst.remov.farVIntLow
import Submission.Work.FTS.EllipticEst.remov.slice_ang_reduce

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The top-order far-window bound, assembled from the two slot estimates

This module contains the **assembly** of the far-window estimate for the top-order slot
`∂^{k+1}(v)` (`v = u / cos θ`) from

* the `i ≤ k` slot bounds `TopCoreB.xTerm_le` + `TopCoreB.integrableOn_sinWeight_xDivX`
  (proved in `TopCoreB/far_vBound.lean`), and
* the `i = k + 1` slot bound, taken as an explicit hypothesis
  (`htop`, the statement of `Work.FTS.EllipticEst.remov.sinWeight_xDivX_top_le`).

Produced here:

* `farTopXAuxLive_of_top` — the reflected-variable form
  `∫_{(0)..xEnd} (∂^{k+1}(shiftV u))² sin(2x)^{2k-γ} ≤ C·FarR k γ u g` together with its
  integrability.  This is exactly the `hTopXph` gap of `remov/slice_ang_v_far.lean`.
* `slice_ang_v_far_live_of_top` — a *copy* of `Work.FTS.EllipticEst.remov.slice_ang_v_far`
  (whose only missing step is that `hTopXph` gap), with the gap filled by `htop`.

The wiring to the child lemma `sinWeight_xDivX_top_le` is done in `EllFarTopWired.lean`.

The pointwise input is `TopCoreB.shiftV_deriv_sq_le` with the derivative bounds of
`TopCoreB.sinDivDerivBounds (k+1)`: `(∂^{k+1} v)² ≤ A · Σ_{i ≤ k+1} (∂^i (U/x))²`,
`U = shiftU u`, `A = (2^{k+1}K)²(k+2)`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Work.FTS.EllipticEst.remov.TopCoreB

/-- `secH` is smooth on `(0, xEnd)`. -/
private theorem contDiffOn_secH_local (n : ℕ) :
    ContDiffOn ℝ n TopCoreB.secH (Set.Ioo 0 TopCoreB.xEnd) := by
  intro x hx
  exact (TopCoreB.contDiffAt_secH (m := n) (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hx.1
    (by linarith [hx.2, TopCoreB.xEnd_lt_pi_half, Real.pi_pos])))).contDiffWithinAt

/-- The reflected `v = u/cos θ` is `C^n` on `(0, xEnd)`. -/
private theorem contDiffOn_shiftV_local {n : ℕ} {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ (n + 1) u (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ n (TopCoreB.shiftV u) (Set.Ioo 0 TopCoreB.xEnd) := by
  intro x hx
  have h1 : ContDiffWithinAt ℝ n (fun y : ℝ => TopCoreB.shiftU u y / y)
      (Set.Ioo 0 TopCoreB.xEnd) x :=
    (TopCoreB.contDiffOn_divX hu).contDiffWithinAt hx
  have h2 : ContDiffWithinAt ℝ n TopCoreB.secH (Set.Ioo 0 TopCoreB.xEnd) x :=
    (contDiffOn_secH_local n).contDiffWithinAt hx
  have h3 : ContDiffWithinAt ℝ n
      (fun y : ℝ => (TopCoreB.shiftU u y / y) * TopCoreB.secH y)
      (Set.Ioo 0 TopCoreB.xEnd) x := h1.mul h2
  have hev : (fun y : ℝ => (TopCoreB.shiftU u y / y) * TopCoreB.secH y)
      =ᶠ[𝓝[Set.Ioo (0:ℝ) TopCoreB.xEnd] x] TopCoreB.shiftV u := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy0 : y ≠ 0 := ne_of_gt hy.1
    simp only [TopCoreB.shiftV, TopCoreB.secH]
    field_simp
  exact h3.congr_of_eventuallyEq hev.symm (hev.self_of_nhdsWithin hx).symm

/-- **The top-order far-window bound**, in the reflected variable, from the `i = k+1` slot. -/
theorem farTopXAuxLive_of_top (k : ℕ) (hk : 2 ≤ k)
    (htop : ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ),
      TopCoreB.FarHyp k γ u g →
      MeasureTheory.IntegrableOn
        (fun x : ℝ => (iteratedDeriv (k + 1) (fun y : ℝ => TopCoreB.shiftU u y / y) x) ^ 2
          * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
        (Set.Ioc 0 TopCoreB.xEnd) ∧
      (∫ x in (0 : ℝ)..TopCoreB.xEnd,
          (iteratedDeriv (k + 1) (fun y : ℝ => TopCoreB.shiftU u y / y) x) ^ 2
            * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
        ≤ C * TopCoreB.FarR k γ u g) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ),
      TopCoreB.FarHyp k γ u g →
      (∫ x in (0 : ℝ)..TopCoreB.xEnd,
          (iteratedDeriv (k + 1) (TopCoreB.shiftV u) x) ^ 2
            * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
        ≤ C * TopCoreB.FarR k γ u g ∧
      MeasureTheory.IntegrableOn
        (fun x : ℝ => (iteratedDeriv (k + 1) (TopCoreB.shiftV u) x) ^ 2
          * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
        (Set.Ioc 0 TopCoreB.xEnd) := by
  obtain ⟨Ct, hCtpos, htop'⟩ := htop
  obtain ⟨K, hKpos, hKb⟩ := TopCoreB.sinDivDerivBounds (k + 1)
  set A : ℝ := ((2 : ℝ) ^ (k + 1) * K) ^ 2 * ((k + 2 : ℕ) : ℝ) with hAdef
  have hApos : 0 < A := by rw [hAdef]; positivity
  set Cs : ℝ := ((k + 2 : ℕ) : ℝ) * ((2 : ℝ) ^ (2 * k + 3) + Ct) with hCsdef
  have hCspos : 0 < Cs := by
    rw [hCsdef]
    have : (0 : ℝ) < (2 : ℝ) ^ (2 * k + 3) + Ct := by positivity
    positivity
  refine ⟨A * Cs + 1, by positivity, ?_⟩
  intro γ u g h
  have hFnn : 0 ≤ TopCoreB.FarR k γ u g := TopCoreB.FarR_nonneg hk h
  have hK : ∀ i ≤ k + 1, ∀ y ∈ Set.Ioc (0 : ℝ) TopCoreB.xEnd,
      |iteratedDeriv i TopCoreB.secH y| ≤ K := fun i hi y hy => hKb i hi y hy
  have hu1 : ContDiffOn ℝ (k + 1) u (Set.Ioo 0 (Real.pi / 2)) :=
    h.huC.of_le (by exact_mod_cast (by omega : k + 1 ≤ k + 2))
  -- a.e. only the interior matters
  have haeIoo : ∀ᵐ x ∂(volume.restrict (Set.Ioc (0:ℝ) TopCoreB.xEnd)),
      x ∈ Set.Ioo 0 TopCoreB.xEnd := by
    have h1 : ∀ᵐ x ∂(volume.restrict (Set.Ioo (0:ℝ) TopCoreB.xEnd)),
        x ∈ Set.Ioo 0 TopCoreB.xEnd := ae_restrict_mem measurableSet_Ioo
    rwa [Measure.restrict_congr_set
      (Ioo_ae_eq_Ioc (μ := volume) (a := (0:ℝ)) (b := TopCoreB.xEnd))] at h1
  -- the pointwise Leibniz bound
  have hpt : ∀ x ∈ Set.Ioo (0 : ℝ) TopCoreB.xEnd,
      (iteratedDeriv (k + 1) (TopCoreB.shiftV u) x) ^ 2
          * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)
        ≤ A * ∑ i ∈ Finset.range (k + 2),
            ((iteratedDeriv i (fun y : ℝ => TopCoreB.shiftU u y / y) x) ^ 2
              * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)) := by
    intro x hx
    have hsnn : 0 ≤ Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ) :=
      Real.rpow_nonneg (TopCoreB.sin_two_nonneg_Ioc ⟨hx.1, le_of_lt hx.2⟩) _
    have h1 := TopCoreB.shiftV_deriv_sq_le (u := u) (m := k + 1) hK hu1 hx
    rw [show k + 1 + 1 = k + 2 from by omega] at h1
    have h2 : (iteratedDeriv (k + 1) (TopCoreB.shiftV u) x) ^ 2
          * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)
        ≤ (A * ∑ i ∈ Finset.range (k + 2),
              (iteratedDeriv i (fun y : ℝ => TopCoreB.shiftU u y / y) x) ^ 2)
          * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ) := by
      rw [hAdef]
      exact mul_le_mul_of_nonneg_right h1 hsnn
    refine h2.trans_eq ?_
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  -- the per-slot integrability
  have hslotint : ∀ i ∈ Finset.range (k + 2),
      MeasureTheory.IntegrableOn
        (fun x : ℝ => (iteratedDeriv i (fun y : ℝ => TopCoreB.shiftU u y / y) x) ^ 2
          * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)) (Set.Ioc 0 TopCoreB.xEnd) := by
    intro i hi
    have hik : i ≤ k + 1 := by have := Finset.mem_range.mp hi; omega
    rcases eq_or_lt_of_le hik with h1 | h1
    · subst h1
      exact (htop' γ u g h).1
    · exact TopCoreB.integrableOn_sinWeight_xDivX hk h (i := i) (by omega)
  have hGint : MeasureTheory.IntegrableOn (fun x : ℝ => ∑ i ∈ Finset.range (k + 2),
      ((iteratedDeriv i (fun y : ℝ => TopCoreB.shiftU u y / y) x) ^ 2
        * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))) (Set.Ioc 0 TopCoreB.xEnd) :=
    integrable_finsetSum _ fun i hi => hslotint i hi
  -- the slot bounds, summed
  have hslotbnd : (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd,
        ∑ i ∈ Finset.range (k + 2),
          ((iteratedDeriv i (fun y : ℝ => TopCoreB.shiftU u y / y) x) ^ 2
            * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)))
      ≤ Cs * TopCoreB.FarR k γ u g := by
    rw [integral_finsetSum _ fun i hi => hslotint i hi]
    have hterm : ∀ i ∈ Finset.range (k + 2),
        (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd,
          (iteratedDeriv i (fun y : ℝ => TopCoreB.shiftU u y / y) x) ^ 2
            * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
          ≤ ((2 : ℝ) ^ (2 * k + 3) + Ct) * TopCoreB.FarR k γ u g := by
      intro i hi
      have hik : i ≤ k + 1 := by have := Finset.mem_range.mp hi; omega
      have hconv : (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd,
          (iteratedDeriv i (fun y : ℝ => TopCoreB.shiftU u y / y) x) ^ 2
            * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
          = ∫ x in (0 : ℝ)..TopCoreB.xEnd,
              (iteratedDeriv i (fun y : ℝ => TopCoreB.shiftU u y / y) x) ^ 2
                * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ) :=
        (intervalIntegral.integral_of_le TopCoreB.xEnd_pos.le).symm
      rw [hconv]
      have hb : (∫ x in (0 : ℝ)..TopCoreB.xEnd,
              (iteratedDeriv i (fun y : ℝ => TopCoreB.shiftU u y / y) x) ^ 2
                * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
            ≤ (2 : ℝ) ^ (2 * k + 3) * TopCoreB.FarR k γ u g
          ∨ (∫ x in (0 : ℝ)..TopCoreB.xEnd,
              (iteratedDeriv i (fun y : ℝ => TopCoreB.shiftU u y / y) x) ^ 2
                * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
            ≤ Ct * TopCoreB.FarR k γ u g := by
        rcases eq_or_lt_of_le hik with h1 | h1
        · subst h1
          exact Or.inr (htop' γ u g h).2
        · exact Or.inl (TopCoreB.xTerm_le hk h (i := i) (by omega))
      have h2pos : (0 : ℝ) < (2 : ℝ) ^ (2 * k + 3) := by positivity
      rcases hb with hb | hb
      · exact hb.trans (by nlinarith [hFnn, hCtpos.le, h2pos])
      · exact hb.trans (by nlinarith [hFnn, hCtpos, h2pos])
    calc (∑ i ∈ Finset.range (k + 2),
            ∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd,
              (iteratedDeriv i (fun y : ℝ => TopCoreB.shiftU u y / y) x) ^ 2
                * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
        ≤ ∑ _i ∈ Finset.range (k + 2),
            ((2 : ℝ) ^ (2 * k + 3) + Ct) * TopCoreB.FarR k γ u g :=
          Finset.sum_le_sum hterm
      _ = Cs * TopCoreB.FarR k γ u g := by
          rw [hCsdef, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  -- integrability of the left-hand side
  have hLHSint : MeasureTheory.IntegrableOn
      (fun x : ℝ => (iteratedDeriv (k + 1) (TopCoreB.shiftV u) x) ^ 2
        * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)) (Set.Ioc 0 TopCoreB.xEnd) := by
    have hcont : ContinuousOn (fun x : ℝ => (iteratedDeriv (k + 1) (TopCoreB.shiftV u) x) ^ 2
        * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)) (Set.Ioo 0 TopCoreB.xEnd) := by
      have hcdV : ContDiffOn ℝ (k + 1) (TopCoreB.shiftV u) (Set.Ioo 0 TopCoreB.xEnd) :=
        contDiffOn_shiftV_local (n := k + 1) h.huC
      have hunic : UniqueDiffOn ℝ (Set.Ioo (0:ℝ) TopCoreB.xEnd) := isOpen_Ioo.uniqueDiffOn
      have hcontW : ContinuousOn
          (iteratedDerivWithin (k + 1) (TopCoreB.shiftV u) (Set.Ioo 0 TopCoreB.xEnd))
          (Set.Ioo 0 TopCoreB.xEnd) :=
        hcdV.continuousOn_iteratedDerivWithin le_rfl hunic
      have hcont' : ContinuousOn (iteratedDeriv (k + 1) (TopCoreB.shiftV u))
          (Set.Ioo 0 TopCoreB.xEnd) :=
        hcontW.congr fun x hx =>
          (iteratedDerivWithin_eq_iteratedDeriv hunic
            (hcdV.contDiffAt (isOpen_Ioo.mem_nhds hx)) hx).symm
      exact (hcont'.pow 2).mul (TopCoreB.continuousOn_sin_rpow)
    have hass : AEStronglyMeasurable
        (fun x : ℝ => (iteratedDeriv (k + 1) (TopCoreB.shiftV u) x) ^ 2
          * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
        (volume.restrict (Set.Ioc (0:ℝ) TopCoreB.xEnd)) :=
      TopCoreB.aestronglyMeasurable_Ioc_of_continuousOn hcont
    refine (hGint.const_mul A).mono' hass ?_
    filter_upwards [haeIoo] with x hx
    have hsnn : 0 ≤ Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ) :=
      Real.rpow_nonneg (TopCoreB.sin_two_nonneg_Ioc ⟨hx.1, le_of_lt hx.2⟩) _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hsnn)]
    exact hpt x hx
  -- the integral bound
  have hLHSle : (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd,
        (iteratedDeriv (k + 1) (TopCoreB.shiftV u) x) ^ 2
          * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
      ≤ A * (Cs * TopCoreB.FarR k γ u g) := by
    have hae : (fun x : ℝ => (iteratedDeriv (k + 1) (TopCoreB.shiftV u) x) ^ 2
          * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
        ≤ᵐ[volume.restrict (Set.Ioc (0:ℝ) TopCoreB.xEnd)]
        (fun x : ℝ => A * ∑ i ∈ Finset.range (k + 2),
              ((iteratedDeriv i (fun y : ℝ => TopCoreB.shiftU u y / y) x) ^ 2
                * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))) := by
      filter_upwards [haeIoo] with x hx
      exact hpt x hx
    have h0 : 0 ≤ᵐ[volume.restrict (Set.Ioc (0:ℝ) TopCoreB.xEnd)]
        (fun x : ℝ => (iteratedDeriv (k + 1) (TopCoreB.shiftV u) x) ^ 2
          * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (TopCoreB.sin_two_nonneg_Ioc ⟨hx.1, hx.2⟩) _)
    calc (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd,
          (iteratedDeriv (k + 1) (TopCoreB.shiftV u) x) ^ 2
            * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
        ≤ ∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd, A * ∑ i ∈ Finset.range (k + 2),
              ((iteratedDeriv i (fun y : ℝ => TopCoreB.shiftU u y / y) x) ^ 2
                * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)) :=
          integral_mono_of_nonneg h0 (hGint.const_mul A) hae
      _ = A * (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd, ∑ i ∈ Finset.range (k + 2),
              ((iteratedDeriv i (fun y : ℝ => TopCoreB.shiftU u y / y) x) ^ 2
                * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))) :=
          integral_const_mul A _
      _ ≤ A * (Cs * TopCoreB.FarR k γ u g) := mul_le_mul_of_nonneg_left hslotbnd hApos.le
  refine ⟨?_, hLHSint⟩
  rw [intervalIntegral.integral_of_le TopCoreB.xEnd_pos.le]
  calc (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd,
          (iteratedDeriv (k + 1) (TopCoreB.shiftV u) x) ^ 2
            * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
      ≤ A * (Cs * TopCoreB.FarR k γ u g) := hLHSle
    _ ≤ (A * Cs + 1) * TopCoreB.FarR k γ u g := by nlinarith [hFnn, hApos, hCspos]


open scoped Real Topology
open MeasureTheory Set Filter

/-- On the angular interval `Iθ` the weight `sin(2θ)` is nonnegative. -/
private lemma sin_two_nonneg_Iθ_local {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])

/-- `AngRHS` is a sum of integrals of nonnegative functions. -/
private lemma angRHS_nonneg (k : ℕ) (γ : ℝ) (u g : ℝ → ℝ) : 0 ≤ AngRHS k γ u g := by
  unfold AngRHS
  refine add_nonneg (add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_) ?_
  · exact setIntegral_nonneg measurableSet_Icc fun θ hθ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ_local hθ) _)
  · exact Finset.sum_nonneg fun j _ =>
      setIntegral_nonneg measurableSet_Icc fun θ hθ =>
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ_local hθ) _)
  · exact setIntegral_nonneg measurableSet_Icc fun θ hθ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ_local hθ) _)
  · exact setIntegral_nonneg measurableSet_Icc fun θ _ => sq_nonneg _
  · exact setIntegral_nonneg measurableSet_Icc fun θ _ => sq_nonneg _

/-- `TopCoreB.FarR` is `AngRHS`, definitionally. -/
private lemma farR_eq_angRHS (k : ℕ) (γ : ℝ) (u g : ℝ → ℝ) :
    TopCoreB.FarR k γ u g = AngRHS k γ u g := by
  simp only [TopCoreB.FarR, AngRHS]

/-- The far window, as an explicit interval. -/
private lemma farSet_eq : TopCoreB.farSet = Set.Icc (3 * Real.pi / 8) (Real.pi / 2) := rfl

/-- The far-window integrand, written in the `TopCoreB` vocabulary. -/
private lemma integrand_eq (k : ℕ) (γ : ℝ) (m : ℕ) (u : ℝ → ℝ) (θ : ℝ) :
    (iteratedDeriv m (TopCoreB.vF u) θ) ^ 2 * TopCoreB.qW k γ θ
      = (iteratedDeriv m (fun t : ℝ => u t / Real.cos t) θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) := by
  have h1 : TopCoreB.vF u = fun t : ℝ => u t / Real.cos t := rfl
  have h2 : TopCoreB.qW k γ θ = Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) := rfl
  rw [h1, h2]

/-- The far-window integral in the target's notation equals the `TopCoreB` one. -/
private lemma farIntegral_eq (k : ℕ) (γ : ℝ) (m : ℕ) (u : ℝ → ℝ) :
    (∫ θ in Set.Icc (3 * Real.pi / 8) (Real.pi / 2),
        (iteratedDeriv m (fun t : ℝ => u t / Real.cos t) θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
      = ∫ θ in TopCoreB.farSet,
          (iteratedDeriv m (TopCoreB.vF u) θ) ^ 2 * TopCoreB.qW k γ θ := by
  rw [farSet_eq]
  exact setIntegral_congr_fun measurableSet_Icc fun θ _ => (integrand_eq k γ m u θ).symm

/-- Integrability on the far window, transferred to the reflected variable. -/
private lemma integrableOn_farSet_iff (F : ℝ → ℝ) :
    MeasureTheory.IntegrableOn F TopCoreB.farSet ↔
      MeasureTheory.IntegrableOn (fun x : ℝ => F (Real.pi / 2 - x))
        (Set.Icc 0 TopCoreB.xEnd) := by
  have h := (MeasureTheory.MeasurePreserving.integrableOn_comp_preimage
    TopCoreB.measurePreserving_reflectC TopCoreB.measurableEmbedding_reflectC
    (s := TopCoreB.farSet) (f := F)).symm
  rw [TopCoreB.preimage_reflectC_farSet] at h
  simpa [TopCoreB.reflectC, Function.comp_def] using h

/-- **Weighted `v = u / cos θ` bound on the far window `[3π/8, π/2]`.**

For `k ≥ 2`, `γ ∈ [1,5/4]`, `u ∈ C^{k+2}(0,π/2)` continuous on `[0,π/2]` with `u 0 = u (π/2) = 0`
and `g = Lzero1 u` on the open interval, with the six integrability hypotheses of the target
`slice_ang_gen`, one has for every `m ≤ k+1`

`∫_{[3π/8,π/2]} (∂^m (u/cos))² · sin(2θ)^(2k-γ) ≤ C · AngRHS k γ u g`

(`AngRHS` as in `Submission/Work/FTS/EllipticEst/remov/slice_ang_reduce.lean`), together with the
integrability of the left-hand integrand.

Route (see `Submission/Work/FTS/EllipticEst/remov/NOTES_slice_ang_v_bound.md`): substitute
`x = π/2 - θ ∈ (0,π/8]`, `U x := u (π/2 - x)`, `V x := U x / sin x`.  Then
`v(π/2-x) = V x`, `sin(2θ) = sin(2x)`, `∂_θ^m v(θ) = ± V^{(m)}(x)`, so the far integral becomes
`∫_0^{π/8}(V^{(m)})² sin(2x)^{2k-γ} dx ≤ 2^{2k-γ} ∫_0^{π/8}(V^{(m)})² x^{2k-γ} dx`.  Write
`V = (U h)/x` with `h = x/sin x` smooth on `[0,π/8]` with bounded derivatives (Leibniz):
`V^{(m)} = Σ_{i≤m}C(m,i)h^{(i)}(U/x)^{(m-i)}`.  For each division order `j ≤ k` apply the
Hilbert/Hardy division inequality `∫ x^{2j-γ}((U/x)^{(j)})² ≤ C∫x^{2j-γ}(U^{(j+1)})²` at the needed
finite smoothness — this is the lemma `Work.FTS.EllipticEst.remov.hardyDiv_fin` being produced in
parallel; if `Submission/Work/FTS/EllipticEst/remov/hardyDiv_fin.lean` is not yet on disk, prove
that division inequality locally in your own file (it is the statement of
`Work.FTS.H2.DivQ.hardyA_le_W` with `⊤` weakened to `C^{j+2}`; the `C^∞` case is already proved).
The weight comparison `x^{2k-γ} ≤ x^{2j-γ}` (`j ≤ k`) and
`∫x^{2j-γ}(U^{(j+1)})² ≤ C·H3(j+1)` (`H3(j+1) = ∫(u^{(j+1)})²sin(2θ)^{2(j+1)-4-γ}`) close every
term with `1 ≤ j ≤ k`; `j+1 = 2` is dominated by `H4 = ∫(u'')²sin(2θ)^{-η}`, and `j = 0` by
`H6 = ∫u²`.  For `m = k+1` the term `j = k+1` (from `i = 0`) is handled by the exact Leibniz
relation `x(U/x)^{(k+1)} = U^{(k+1)} - (k+1)(U/x)^{(k)}`, the first piece being exactly the
`H3(k+1)` slot; the second is reduced with the same relation at order `k` (giving `H3(k)`) and the
division inequality at order `k-1`. -/
theorem slice_ang_v_far_live_of_top (k : ℕ) (hk : 2 ≤ k)
    (htop : ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ),
      TopCoreB.FarHyp k γ u g →
      (∫ x in (0 : ℝ)..TopCoreB.xEnd,
          (iteratedDeriv (k + 1) (TopCoreB.shiftV u) x) ^ 2
            * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
        ≤ C₂ * TopCoreB.FarR k γ u g ∧
      MeasureTheory.IntegrableOn
        (fun x : ℝ => (iteratedDeriv (k + 1) (TopCoreB.shiftV u) x) ^ 2
          * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
        (Set.Ioc 0 TopCoreB.xEnd)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ),
      1 ≤ γ → γ ≤ 5 / 4 →
      ContDiffOn ℝ (k + 2) u (Set.Ioo 0 (Real.pi / 2)) →
      ContinuousOn u (Set.Icc 0 (Real.pi / 2)) →
      u 0 = 0 → u (Real.pi / 2) = 0 →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), g θ = Work.FTS.EllipticEst.Lzero1 u θ) →
      MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv (k + 2) u θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv k g θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ →
      (∀ j ∈ Finset.Icc 3 (k + 1), MeasureTheory.IntegrableOn
          (fun θ => (iteratedDeriv j u θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ)) Work.Spaces.Iθ) →
      MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta))) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ →
      ∀ m : ℕ, m ≤ k + 1 →
        MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv m (fun t => u t / Real.cos t) θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
          (Set.Icc (3 * Real.pi / 8) (Real.pi / 2)) ∧
        (∫ θ in Set.Icc (3 * Real.pi / 8) (Real.pi / 2),
            (iteratedDeriv m (fun t => u t / Real.cos t) θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
          ≤ C * Work.FTS.EllipticEst.remov.AngRHS k γ u g := by
  -- ### the case `m ≤ k`: the bound is `TopCoreB.far_vBound`
  obtain ⟨C₁, hC₁pos, hLowB⟩ := TopCoreB.far_vBound k hk
  -- ### the integrability for `m ≤ k`
  have hLowInt : ∀ (γ : ℝ) (u g : ℝ → ℝ), TopCoreB.FarHyp k γ u g → ∀ m : ℕ, m ≤ k →
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => (iteratedDeriv m (TopCoreB.vF u) θ) ^ 2 * TopCoreB.qW k γ θ)
        TopCoreB.farSet := by
    intro γ u g hF m hm
    exact farVIntLow k hk γ u g hF m hm
  -- ### the case `m = k + 1`: the reflected-window estimate and its integrability
  -- replaced by `obtain ⟨C₂, hC₂pos, hTopX⟩ := farTopXAux k hk` once that module lands
  obtain ⟨C₂, hC₂pos, hTopX⟩ := htop
  have hTopB : ∀ (γ : ℝ) (u g : ℝ → ℝ), TopCoreB.FarHyp k γ u g →
      (∫ θ in TopCoreB.farSet,
          (iteratedDeriv (k + 1) (TopCoreB.vF u) θ) ^ 2 * TopCoreB.qW k γ θ)
        ≤ C₂ * TopCoreB.FarR k γ u g := by
    intro γ u g hF
    rw [TopCoreB.farSet_LHS_eq k γ (k + 1) u]
    exact (hTopX γ u g hF).1
  have hTopI : ∀ (γ : ℝ) (u g : ℝ → ℝ), TopCoreB.FarHyp k γ u g →
      MeasureTheory.IntegrableOn (fun θ : ℝ =>
          (iteratedDeriv (k + 1) (TopCoreB.vF u) θ) ^ 2 * TopCoreB.qW k γ θ)
        TopCoreB.farSet := by
    intro γ u g hF
    have hx := (hTopX γ u g hF).2
    have hIcc : MeasureTheory.IntegrableOn
        (fun x : ℝ => (iteratedDeriv (k + 1) (TopCoreB.shiftV u) x) ^ 2
          * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)) (Set.Icc 0 TopCoreB.xEnd) :=
      hx.congr_set_ae
        (MeasureTheory.Ioc_ae_eq_Icc (μ := volume) (a := 0) (b := TopCoreB.xEnd)).symm
    refine (integrableOn_farSet_iff (fun θ : ℝ =>
      (iteratedDeriv (k + 1) (TopCoreB.vF u) θ) ^ 2 * TopCoreB.qW k γ θ)).2 ?_
    refine hIcc.congr_fun (fun x _ => ?_) measurableSet_Icc
    exact (TopCoreB.farSet_integrand_eq k γ (k + 1) u x).symm
  -- ### assembly
  refine ⟨C₁ + C₂, by linarith, ?_⟩
  intro γ u g hγ1 hγ2 hu hcont hu0 hupi hg hIk2 hIgk hIhigh hI2 hI1 hI0 m hm
  have hF : TopCoreB.FarHyp k γ u g :=
    ⟨hγ1, hγ2, hu, hcont, hu0, hupi, hg, hIk2, hIgk, hIhigh, hI2, hI1, hI0⟩
  have hAng := angRHS_nonneg k γ u g
  by_cases hmk : m ≤ k
  · -- `m ≤ k`
    refine ⟨?_, ?_⟩
    · exact (hLowInt γ u g hF m hmk).congr_fun
        (fun θ _ => (integrand_eq k γ m u θ).symm) measurableSet_Icc
    · rw [farIntegral_eq k γ m u]
      calc (∫ θ in TopCoreB.farSet,
              (iteratedDeriv m (TopCoreB.vF u) θ) ^ 2 * TopCoreB.qW k γ θ)
          ≤ C₁ * TopCoreB.FarR k γ u g := hLowB γ u g hF m hmk
        _ = C₁ * AngRHS k γ u g := by rw [farR_eq_angRHS]
        _ ≤ (C₁ + C₂) * AngRHS k γ u g :=
            mul_le_mul_of_nonneg_right (by linarith) hAng
  · -- `m = k + 1`
    have hm' : m = k + 1 := by omega
    subst hm'
    refine ⟨?_, ?_⟩
    · exact (hTopI γ u g hF).congr_fun
        (fun θ _ => (integrand_eq k γ (k + 1) u θ).symm) measurableSet_Icc
    · rw [farIntegral_eq k γ (k + 1) u]
      calc (∫ θ in TopCoreB.farSet,
              (iteratedDeriv (k + 1) (TopCoreB.vF u) θ) ^ 2 * TopCoreB.qW k γ θ)
          ≤ C₂ * TopCoreB.FarR k γ u g := hTopB γ u g hF
        _ = C₂ * AngRHS k γ u g := by rw [farR_eq_angRHS]
        _ ≤ (C₁ + C₂) * AngRHS k γ u g :=
            mul_le_mul_of_nonneg_right (by linarith) hAng


end Work.FTS.EllipticEst.remov

