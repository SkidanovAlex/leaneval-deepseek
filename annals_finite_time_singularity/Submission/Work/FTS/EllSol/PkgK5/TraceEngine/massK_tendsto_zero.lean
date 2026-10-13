import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllSol.PkgK5.InterpTraceCore
import Submission.Work.FTS.EllipticEst.EllTwoAsm.LightSliceRate
import Submission.Work.FTS.EllSol.PkgK5.TraceEngine.slice_rate_thEta
import Submission.Work.FTS.EllSol.PkgK5.TraceEngine.massK_iterated_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllSol.PkgK5.TraceEngine

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

theorem massK_tendsto_zero {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ) {ψ : ℝ → ℝ → ℝ}
    (hψ : Work.FTS.EllipticEst.SmoothOpen ψ)
    (htr0 : ∀ z : ℝ, 0 < z → Filter.Tendsto (fun θ : ℝ => ψ z θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (htr1 : ∀ z : ℝ, 0 < z → Filter.Tendsto (fun θ : ℝ => ψ z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hE : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
        * (Work.Spaces.pth ψ p.1 p.2) ^ 2 * Work.FTS.EllipticEst.thEta p.2)
      (Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k) ×ˢ Work.Spaces.Iθ)) :
    Filter.Tendsto (fun θ => ∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
        χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto (fun θ => ∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
        χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by

  have ha : 0 < Work.FTS.EllSol.PkgK5.cA k := Work.FTS.EllSol.PkgK5.cA_pos k
  have hab : Work.FTS.EllSol.PkgK5.cA k ≤ Work.FTS.EllSol.PkgK5.cB k :=
    Work.FTS.EllSol.PkgK5.cA_le_cB k
  -- the angular weight is nonnegative on `Iθ`
  have hthnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Work.FTS.EllipticEst.thEta θ := by
    intro θ hθ
    have h2 : (0 : ℝ) ≤ 2 * θ := by linarith [hθ.1]
    have hpi : 2 * θ ≤ Real.pi := by linarith [hθ.2, Real.pi_pos]
    exact Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc ⟨h2, hpi⟩) _
  set M : ℝ := ∫ p in (Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k) ×ˢ
      Work.Spaces.Iθ),
      (Work.Spaces.w p.1) ^ 2 * (Work.Spaces.pth ψ p.1 p.2) ^ 2 * Work.FTS.EllipticEst.thEta p.2
    with hM
  obtain ⟨hiter, -, hIntIθ, hIntLp, hIntRp⟩ := massK_iterated_eq (k := k) (ψ := ψ) hE
  -- the a.e. slice integrability on `Iθ` (this is the `prod_right_ae` of `hE`)
  have hzmem' : ∀ᵐ z ∂(MeasureTheory.volume.restrict
      (Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k))),
      z ∈ Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k) :=
    MeasureTheory.ae_restrict_mem measurableSet_Icc
  have haeIθ : ∀ᵐ z ∂(MeasureTheory.volume.restrict
      (Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k))),
      MeasureTheory.Integrable (fun s : ℝ => (Work.Spaces.pth ψ z s) ^ 2 *
        Work.FTS.EllipticEst.thEta s) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h1 : MeasureTheory.Integrable (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 *
        (Work.Spaces.pth ψ p.1 p.2) ^ 2 * Work.FTS.EllipticEst.thEta p.2)
        ((MeasureTheory.volume.restrict (Set.Icc (Work.FTS.EllSol.PkgK5.cA k)
            (Work.FTS.EllSol.PkgK5.cB k))).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
      exact hE
    filter_upwards [h1.prod_right_ae, hzmem'] with z hz hzm
    have hzpos : 0 < z := lt_of_lt_of_le ha hzm.1
    have hwne : (Work.Spaces.w z) ^ 2 ≠ 0 := by
      rw [Work.Spaces.w]
      exact pow_ne_zero 2 (div_ne_zero (by positivity) (pow_ne_zero 2 (ne_of_gt hzpos)))
    have h2 : MeasureTheory.Integrable (fun s : ℝ => (Work.Spaces.w z) ^ 2 *
        ((Work.Spaces.pth ψ z s) ^ 2 * Work.FTS.EllipticEst.thEta s))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      hz.congr (Filter.Eventually.of_forall (fun s => by ring))
    have h3 := h2.const_mul (((Work.Spaces.w z) ^ 2)⁻¹)
    refine h3.congr (Filter.Eventually.of_forall (fun s => ?_))
    exact inv_mul_cancel_left₀ hwne _
  have haeIoo : ∀ᵐ z ∂(MeasureTheory.volume.restrict
      (Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k))),
      MeasureTheory.IntegrableOn (fun s : ℝ => (Work.Spaces.pth ψ z s) ^ 2 *
        Work.FTS.EllipticEst.thEta s) (Set.Ioo 0 (Real.pi / 2)) := by
    filter_upwards [haeIθ] with z hz
    exact MeasureTheory.IntegrableOn.mono_set hz
      (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
  -- the key two-sided bound
  have key : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (∫ z in Work.FTS.EllSol.PkgK5.cA k..Work.FTS.EllSol.PkgK5.cB k,
          χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2) ≤ θ * M ∧
      (∫ z in Work.FTS.EllSol.PkgK5.cA k..Work.FTS.EllSol.PkgK5.cB k,
          χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2) ≤ (Real.pi / 2 - θ) * M ∧
      (0 ≤ ∫ z in Work.FTS.EllSol.PkgK5.cA k..Work.FTS.EllSol.PkgK5.cB k,
          χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2) := by
    intro θ hθ
    have hθ0 : 0 < θ := hθ.1
    have hθpi : θ < Real.pi / 2 := hθ.2
    have hθnn : 0 ≤ θ := le_of_lt hθ0
    have hconv : (∫ z in Work.FTS.EllSol.PkgK5.cA k..Work.FTS.EllSol.PkgK5.cB k,
          χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2)
        = ∫ z in Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k),
          χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2 := by
      rw [intervalIntegral.integral_of_le hab, MeasureTheory.integral_Icc_eq_integral_Ioc]
    -- the slice bounds, a.e. in `z`
    have hbdL : ∀ᵐ z ∂(MeasureTheory.volume.restrict
        (Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k))),
        ψ z θ ^ 2 ≤ θ * ∫ s in Set.Ioo 0 θ,
          (Work.Spaces.pth ψ z s) ^ 2 * Work.FTS.EllipticEst.thEta s := by
      filter_upwards [haeIoo, hzmem'] with z hzint hzm
      have hzpos : 0 < z := lt_of_lt_of_le ha hzm.1
      have hf : ContDiffOn ℝ 1 (fun s => ψ z s) (Set.Ioo 0 (Real.pi / 2)) :=
        (hψ.curry_θ hzpos).of_le (by simp [Work.Stability.smoothOrder])
      exact (slice_rate_thEta (fun s => ψ z s) hf (htr0 z hzpos) (htr1 z hzpos) hzint).1 θ hθ
    have hbdR : ∀ᵐ z ∂(MeasureTheory.volume.restrict
        (Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k))),
        ψ z θ ^ 2 ≤ (Real.pi / 2 - θ) * ∫ s in Set.Ioo θ (Real.pi / 2),
          (Work.Spaces.pth ψ z s) ^ 2 * Work.FTS.EllipticEst.thEta s := by
      filter_upwards [haeIoo, hzmem'] with z hzint hzm
      have hzpos : 0 < z := lt_of_lt_of_le ha hzm.1
      have hf : ContDiffOn ℝ 1 (fun s => ψ z s) (Set.Ioo 0 (Real.pi / 2)) :=
        (hψ.curry_θ hzpos).of_le (by simp [Work.Stability.smoothOrder])
      exact (slice_rate_thEta (fun s => ψ z s) hf (htr0 z hzpos) (htr1 z hzpos) hzint).2 θ hθ
    -- integrability of the two dominating functions
    have hIntL : MeasureTheory.Integrable (fun z : ℝ => (Work.Spaces.w z) ^ 2 *
        (θ * ∫ s in Set.Ioo 0 θ, (Work.Spaces.pth ψ z s) ^ 2 * Work.FTS.EllipticEst.thEta s))
        (MeasureTheory.volume.restrict (Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k))) :=
      ((hIntLp θ hθ).const_mul θ).congr (Filter.Eventually.of_forall (fun z => by ring))
    have hIntR : MeasureTheory.Integrable (fun z : ℝ => (Work.Spaces.w z) ^ 2 *
        ((Real.pi / 2 - θ) * ∫ s in Set.Ioo θ (Real.pi / 2),
          (Work.Spaces.pth ψ z s) ^ 2 * Work.FTS.EllipticEst.thEta s))
        (MeasureTheory.volume.restrict (Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k))) :=
      ((hIntRp θ hθ).const_mul (Real.pi / 2 - θ)).congr
        (Filter.Eventually.of_forall (fun z => by ring))
    -- nonnegativity of the mass integrand a.e.
    have hnn_ae : 0 ≤ᵐ[MeasureTheory.volume.restrict
        (Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k))]
        (fun z : ℝ => χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2) := by
      filter_upwards [hzmem'] with z hzm
      have hzpos : 0 < z := lt_of_lt_of_le ha hzm.1
      exact mul_nonneg (mul_nonneg (hχ.bnd k z hzpos).1 (sq_nonneg _)) (sq_nonneg _)
    -- integrability of the dominating functions: only the `Iθ`-integral is used
    have hIntL : MeasureTheory.Integrable (fun z : ℝ => (Work.Spaces.w z) ^ 2 *
        (θ * ∫ s in Work.Spaces.Iθ, (Work.Spaces.pth ψ z s) ^ 2 * Work.FTS.EllipticEst.thEta s))
        (MeasureTheory.volume.restrict (Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k))) :=
      (hIntIθ.const_mul θ).congr (Filter.Eventually.of_forall (fun z => by ring))
    have hIntR : MeasureTheory.Integrable (fun z : ℝ => (Work.Spaces.w z) ^ 2 *
        ((Real.pi / 2 - θ) * ∫ s in Work.Spaces.Iθ, (Work.Spaces.pth ψ z s) ^ 2 *
          Work.FTS.EllipticEst.thEta s))
        (MeasureTheory.volume.restrict (Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k))) :=
      (hIntIθ.const_mul (Real.pi / 2 - θ)).congr (Filter.Eventually.of_forall (fun z => by ring))
    -- the inner-integral monotonicity: `Ioo 0 θ ⊆ Iθ` resp. `Ioo θ (π/2) ⊆ Iθ`
    have hinnerL : ∀ᵐ z ∂(MeasureTheory.volume.restrict
        (Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k))),
        (∫ s in Set.Ioo 0 θ, (Work.Spaces.pth ψ z s) ^ 2 * Work.FTS.EllipticEst.thEta s)
          ≤ (∫ s in Work.Spaces.Iθ, (Work.Spaces.pth ψ z s) ^ 2 *
              Work.FTS.EllipticEst.thEta s) := by
      filter_upwards [haeIθ] with z hz
      refine MeasureTheory.setIntegral_mono_set hz ?_ ?_
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with s hs
        exact mul_nonneg (sq_nonneg _) (hthnn s hs)
      · filter_upwards with s hs
        exact ⟨le_of_lt hs.1, le_of_lt (lt_trans hs.2 hθpi)⟩
    have hinnerR : ∀ᵐ z ∂(MeasureTheory.volume.restrict
        (Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k))),
        (∫ s in Set.Ioo θ (Real.pi / 2), (Work.Spaces.pth ψ z s) ^ 2 *
            Work.FTS.EllipticEst.thEta s)
          ≤ (∫ s in Work.Spaces.Iθ, (Work.Spaces.pth ψ z s) ^ 2 *
              Work.FTS.EllipticEst.thEta s) := by
      filter_upwards [haeIθ] with z hz
      refine MeasureTheory.setIntegral_mono_set hz ?_ ?_
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with s hs
        exact mul_nonneg (sq_nonneg _) (hthnn s hs)
      · filter_upwards with s hs
        exact ⟨le_of_lt (lt_trans hθ0 hs.1), le_of_lt hs.2⟩
    -- the left bound
    have hboundL : (∫ z in Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k),
          χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2) ≤ θ * M := by
      have hsym : (∫ z in Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k),
            (Work.Spaces.w z) ^ 2 * (θ * ∫ s in Work.Spaces.Iθ,
              (Work.Spaces.pth ψ z s) ^ 2 * Work.FTS.EllipticEst.thEta s))
          = θ * ∫ z in Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k),
              (Work.Spaces.w z) ^ 2 * ∫ s in Work.Spaces.Iθ,
                (Work.Spaces.pth ψ z s) ^ 2 * Work.FTS.EllipticEst.thEta s := by
        rw [← MeasureTheory.integral_const_mul]
        exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => by ring))
      have hmono := MeasureTheory.integral_mono_of_nonneg hnn_ae hIntL ?_
      · rw [hsym] at hmono
        rw [hM, ← hiter]
        exact hmono
      · filter_upwards [hbdL, hzmem', hinnerL] with z hzbd hzm hzin
        have hzpos : 0 < z := lt_of_lt_of_le ha hzm.1
        have hχ1 : χ k z ≤ 1 := (hχ.bnd k z hzpos).2
        have hw : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
        have hψ2 : 0 ≤ ψ z θ ^ 2 := sq_nonneg _
        calc χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2
            ≤ (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2 := by
              have h := mul_le_mul_of_nonneg_right hχ1 (mul_nonneg hw hψ2)
              simpa only [one_mul, mul_assoc] using h
          _ ≤ (Work.Spaces.w z) ^ 2 * (θ * ∫ s in Set.Ioo 0 θ,
                (Work.Spaces.pth ψ z s) ^ 2 * Work.FTS.EllipticEst.thEta s) :=
              mul_le_mul_of_nonneg_left hzbd hw
          _ ≤ (Work.Spaces.w z) ^ 2 * (θ * ∫ s in Work.Spaces.Iθ,
                (Work.Spaces.pth ψ z s) ^ 2 * Work.FTS.EllipticEst.thEta s) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hzin hθnn) hw
    -- the right bound
    have hboundR : (∫ z in Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k),
          χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2) ≤ (Real.pi / 2 - θ) * M := by
      have hsym : (∫ z in Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k),
            (Work.Spaces.w z) ^ 2 * ((Real.pi / 2 - θ) * ∫ s in Work.Spaces.Iθ,
              (Work.Spaces.pth ψ z s) ^ 2 * Work.FTS.EllipticEst.thEta s))
          = (Real.pi / 2 - θ) * ∫ z in Set.Icc (Work.FTS.EllSol.PkgK5.cA k)
              (Work.FTS.EllSol.PkgK5.cB k),
              (Work.Spaces.w z) ^ 2 * ∫ s in Work.Spaces.Iθ,
                (Work.Spaces.pth ψ z s) ^ 2 * Work.FTS.EllipticEst.thEta s := by
        rw [← MeasureTheory.integral_const_mul]
        exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => by ring))
      have hmono := MeasureTheory.integral_mono_of_nonneg hnn_ae hIntR ?_
      · rw [hsym] at hmono
        rw [hM, ← hiter]
        exact hmono
      · filter_upwards [hbdR, hzmem', hinnerR] with z hzbd hzm hzin
        have hzpos : 0 < z := lt_of_lt_of_le ha hzm.1
        have hχ1 : χ k z ≤ 1 := (hχ.bnd k z hzpos).2
        have hw : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
        have hψ2 : 0 ≤ ψ z θ ^ 2 := sq_nonneg _
        have hπ : 0 ≤ Real.pi / 2 - θ := by linarith [Real.pi_pos]
        calc χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2
            ≤ (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2 := by
              have h := mul_le_mul_of_nonneg_right hχ1 (mul_nonneg hw hψ2)
              simpa only [one_mul, mul_assoc] using h
          _ ≤ (Work.Spaces.w z) ^ 2 * ((Real.pi / 2 - θ) * ∫ s in Set.Ioo θ (Real.pi / 2),
                (Work.Spaces.pth ψ z s) ^ 2 * Work.FTS.EllipticEst.thEta s) :=
              mul_le_mul_of_nonneg_left hzbd hw
          _ ≤ (Work.Spaces.w z) ^ 2 * ((Real.pi / 2 - θ) * ∫ s in Work.Spaces.Iθ,
                (Work.Spaces.pth ψ z s) ^ 2 * Work.FTS.EllipticEst.thEta s) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hzin hπ) hw

    have hmnn : 0 ≤ ∫ z in Work.FTS.EllSol.PkgK5.cA k..Work.FTS.EllSol.PkgK5.cB k,
        χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2 :=
      intervalIntegral.integral_nonneg hab (fun u hu => by
        have hu0 : 0 < u := lt_of_lt_of_le ha hu.1
        exact mul_nonneg (mul_nonneg (hχ.bnd k u hu0).1 (sq_nonneg _)) (sq_nonneg _))
    refine ⟨?_, ?_, hmnn⟩
    · rw [hconv]; exact hboundL
    · rw [hconv]; exact hboundR
  -- the two filters
  have hIOl : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    have h1 : Set.Iio (Real.pi / 2) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
      nhdsWithin_le_nhds (isOpen_Iio.mem_nhds (show (0:ℝ) < Real.pi / 2 by linarith [Real.pi_pos]))
    have h2 : Set.Ioi (0 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := self_mem_nhdsWithin
    exact Filter.mem_of_superset (Filter.inter_mem h2 h1) (fun x hx => ⟨hx.1, hx.2⟩)
  have hIOr : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) := by
    have h1 : Set.Ioi (0 : ℝ) ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) :=
      nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds (show (0:ℝ) < Real.pi / 2 by linarith [Real.pi_pos]))
    have h2 : Set.Iio (Real.pi / 2) ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) :=
      self_mem_nhdsWithin
    exact Filter.mem_of_superset (Filter.inter_mem h1 h2) (fun x hx => ⟨hx.1, hx.2⟩)
  have hnn_left : ∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      0 ≤ ∫ z in Work.FTS.EllSol.PkgK5.cA k..Work.FTS.EllSol.PkgK5.cB k,
        χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2 := by
    filter_upwards [hIOl] with θ hθ
    exact (key θ hθ).2.2
  have hbnd_left : ∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (∫ z in Work.FTS.EllSol.PkgK5.cA k..Work.FTS.EllSol.PkgK5.cB k,
        χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2) ≤ θ * M := by
    filter_upwards [hIOl] with θ hθ
    exact (key θ hθ).1
  have htend_left : Filter.Tendsto (fun θ : ℝ => θ * M)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h1 : Filter.Tendsto (fun θ : ℝ => θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using h1.mul_const M
  have hnn_right : ∀ᶠ θ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
      0 ≤ ∫ z in Work.FTS.EllSol.PkgK5.cA k..Work.FTS.EllSol.PkgK5.cB k,
        χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2 := by
    filter_upwards [hIOr] with θ hθ
    exact (key θ hθ).2.2
  have hbnd_right : ∀ᶠ θ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
      (∫ z in Work.FTS.EllSol.PkgK5.cA k..Work.FTS.EllSol.PkgK5.cB k,
        χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2) ≤ (Real.pi / 2 - θ) * M := by
    filter_upwards [hIOr] with θ hθ
    exact (key θ hθ).2.1
  have htend_right : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) * M)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have h1 : Filter.Tendsto (fun θ : ℝ => Real.pi / 2 - θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      have h2 : Filter.Tendsto (fun θ : ℝ => Real.pi / 2 - θ) (nhds (Real.pi / 2))
          (nhds (Real.pi / 2 - Real.pi / 2)) := tendsto_const_nhds.sub tendsto_id
      simpa using h2.mono_left nhdsWithin_le_nhds
    simpa using h1.mul_const M
  exact ⟨squeeze_zero' hnn_left hbnd_left htend_left,
    squeeze_zero' hnn_right hbnd_right htend_right⟩

end Work.FTS.EllSol.PkgK5.TraceEngine
