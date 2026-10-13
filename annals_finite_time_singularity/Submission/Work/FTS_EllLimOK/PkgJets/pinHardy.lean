/-
Copyright: work module for the Elgindi finite-time singularity project.

# `PkgJets.pinHardy` — the angular Hardy inequality behind the pinning estimate

The pinning estimate `PkgJets.pinningBound` reduces, through the reconstruction
`∂_θ(cos θ·Ψ) = cos θ · Vop Ψ`, to the one-dimensional weighted Hardy inequality
(with `A := cos θ·Ψ`, `A' := cos θ·Vop Ψ`, `ν := sin(2θ)^{-η}`)

`∫_θ A²·W₁ ≤ K · ∫_θ (A')²·W₂`,   `W₁ = ν/cos⁴θ`, `W₂ = ν/cos²θ`,

for `A` whose `π/2`-boundary value vanishes (the *pinning* `cos θ·Ψ → 0`).  This module
assembles the pieces proved in `PkgJets.pinBase` (the slices and the primitive), `PkgJets.pinCs`
(the auxiliary Cauchy–Schwarz facts) and `PkgJets.pinMid` (the boundary term, the integration
by parts and the weighted Cauchy–Schwarz), and derives the final inequality with the explicit
constant `4(C₁+C₂)`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS_EllLimOK.PkgJets.pinMid
import Submission.Work.FTS_EllLimOK.PkgJets.integral_Icc_le_of_subinterval_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.PkgJets

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The angular weighted Hardy inequality behind the pinning estimate.**  With the two
quantitative inputs `hLamB` (`Λ² ≤ C₁W₁W₂`) and `hTailB` (`(∫_T^{π/2}cos²sin^η)·Λ(T) ≤ C₂`),
the `A²W₁`-integral is bounded by `4(C₁+C₂)` times the `(A')²W₂`-integral. -/
theorem thetaHardy_of_bounds {C₁ C₂ : ℝ} (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (hLamB : ∀ θ ∈ Set.Ioo 0 (π / 2), (wLam θ) ^ 2 ≤ C₁ * wOne θ * wTwo θ)
    (hTailB : ∀ T ∈ Set.Ioo 0 (π / 2),
      (∫ s in T..(π / 2), (Real.cos s) ^ 2 * (Real.sin (2 * s)) ^ (Work.Spaces.eta))
        * wLam T ≤ C₂) :
    ∀ (Ψ : ℝ → ℝ → ℝ) (z : ℝ), 0 < z →
      Work.FTS.EllipticEst.SmoothOpen Ψ →
      Filter.Tendsto (fun s => Real.cos s * Ψ z s) (𝓝[<] (π / 2)) (𝓝 0) →
      MeasureTheory.IntegrableOn (fun θ => (Ψ z θ / Real.cos θ) ^ 2 * wNu θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (pinV Ψ z θ) ^ 2 * wNu θ) Work.Spaces.Iθ →
      (∫ θ in Work.Spaces.Iθ, (Ψ z θ / Real.cos θ) ^ 2 * wNu θ)
        ≤ (4 * (C₁ + C₂)) * (∫ θ in Work.Spaces.Iθ, (pinV Ψ z θ) ^ 2 * wNu θ) := by
  intro Ψ z hz hsm hpin hL hR
  set B : ℝ := ∫ θ in Work.Spaces.Iθ, (pinV Ψ z θ) ^ 2 * wNu θ with hB
  set At : ℝ := ∫ θ in Work.Spaces.Iθ, (Ψ z θ / Real.cos θ) ^ 2 * wNu θ with hAt
  have hBnn : 0 ≤ B := by
    rw [hB]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (wNu_nonneg hθ))
  have hAtnn : 0 ≤ At := by
    rw [hAt]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (wNu_nonneg hθ))
  have hCn : 0 ≤ C₁ * B := mul_nonneg hC₁.le hBnn
  -- the identification of the left hand side
  have hLHSid : (∫ θ in Work.Spaces.Iθ, (pinA Ψ z θ) ^ 2 * wOne θ) = At := by
    rw [hAt]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    by_cases hc : Real.cos θ = 0
    · simp [pinA, wOne, hc]
    · unfold pinA wOne
      field_simp
  have hAintIθ : MeasureTheory.IntegrableOn (fun θ => (pinA Ψ z θ) ^ 2 * wOne θ)
      Work.Spaces.Iθ := by
    refine hL.congr_fun ?_ measurableSet_Icc
    intro θ _
    by_cases hc : Real.cos θ = 0
    · simp [pinA, wOne, hc]
    · unfold pinA wOne
      field_simp
  have hAint : MeasureTheory.IntegrableOn (fun θ => (pinA Ψ z θ) ^ 2 * wOne θ)
      (Set.Ioo 0 (π / 2)) :=
    hAintIθ.mono_set (fun t ht => ⟨ht.1.le, ht.2.le⟩)
  have hAnn : ∀ x ∈ Set.Ioo 0 (π / 2), 0 ≤ (pinA Ψ z x) ^ 2 * wOne x := fun x hx =>
    mul_nonneg (sq_nonneg _) (wOne_pos hx).le
  -- the per-interval bound
  have key : ∀ x ∈ Set.Ioo 0 (π / 2), ∀ y ∈ Set.Ioo 0 (π / 2), x < y →
      (∫ t in x..y, (pinA Ψ z t) ^ 2 * wOne t)
        ≤ 2 * C₂ * B + 2 * Real.sqrt (At * (C₁ * B)) := by
    intro x hx y hy hxy
    have hibp := pinA_ibp hz hsm hx hy hxy
    have hbd := pinA_tail_bound hz hsm hpin hR hTailB hy
    have hLx : pinL x y ≤ wLam y := pinL_le_wLam hx.1.le hxy.le hy
    have hcs := pinA_cs_mid hz hsm hLamB hx hy hxy
    have hAtxy : (∫ t in x..y, (pinA Ψ z t) ^ 2 * wOne t) ≤ At := by
      rw [← hLHSid, intervalIntegral.integral_of_le hxy.le]
      refine MeasureTheory.setIntegral_mono_set hAintIθ ?_ ?_
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with u hu
        exact mul_nonneg (sq_nonneg _) (wOne_nonneg hu)
      · exact Filter.Eventually.of_forall (fun u hu =>
          ⟨le_of_lt (lt_trans hx.1 hu.1), le_trans hu.2 hy.2.le⟩)
    have hVxy : (∫ t in x..y, (pinV Ψ z t) ^ 2 * wNu t) ≤ B := by
      rw [hB, intervalIntegral.integral_of_le hxy.le]
      refine MeasureTheory.setIntegral_mono_set hR ?_ ?_
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with u hu
        exact mul_nonneg (sq_nonneg _) (wNu_nonneg hu)
      · exact Filter.Eventually.of_forall (fun u hu =>
          ⟨le_of_lt (lt_trans hx.1 hu.1), le_trans hu.2 hy.2.le⟩)
    have hVnn : 0 ≤ ∫ t in x..y, (pinV Ψ z t) ^ 2 * wNu t :=
      intervalIntegral.integral_nonneg hxy.le (fun t ht =>
        mul_nonneg (sq_nonneg _)
          (wNu_nonneg ⟨le_of_lt (lt_of_lt_of_le hx.1 ht.1), le_trans ht.2 hy.2.le⟩))
    have hCSat : (∫ t in x..y, |pinA Ψ z t * (Real.cos t * pinV Ψ z t) * pinL x t|) ^ 2
        ≤ At * (C₁ * B) := by
      refine le_trans hcs ?_
      exact mul_le_mul hAtxy (mul_le_mul_of_nonneg_left hVxy hC₁.le)
        (mul_nonneg hC₁.le hVnn) hAtnn
    have hmid : 2 * (∫ t in x..y, |pinA Ψ z t * (Real.cos t * pinV Ψ z t) * pinL x t|)
        ≤ 2 * Real.sqrt (At * (C₁ * B)) := by
      have h1 : (∫ t in x..y, |pinA Ψ z t * (Real.cos t * pinV Ψ z t) * pinL x t|)
          ≤ Real.sqrt (At * (C₁ * B)) :=
        (Real.le_sqrt (intervalIntegral.integral_nonneg hxy.le (fun t _ => abs_nonneg _))
          (mul_nonneg hAtnn hCn)).mpr hCSat
      linarith
    have hneg : -(∫ t in x..y, pinA Ψ z t * (Real.cos t * pinV Ψ z t) * pinL x t)
        ≤ ∫ t in x..y, |pinA Ψ z t * (Real.cos t * pinV Ψ z t) * pinL x t| :=
      le_trans (neg_le_abs _)
        (intervalIntegral.abs_integral_le_integral_abs (f := fun t =>
          pinA Ψ z t * (Real.cos t * pinV Ψ z t) * pinL x t) hxy.le)
    have hAy : (pinA Ψ z y) ^ 2 * pinL x y ≤ 2 * C₂ * B :=
      le_trans (mul_le_mul_of_nonneg_left hLx (sq_nonneg _)) hbd
    calc (∫ t in x..y, (pinA Ψ z t) ^ 2 * wOne t)
        = (pinA Ψ z y) ^ 2 * pinL x y
          - 2 * ∫ t in x..y, pinA Ψ z t * (Real.cos t * pinV Ψ z t) * pinL x t := hibp
      _ ≤ (pinA Ψ z y) ^ 2 * pinL x y
          + 2 * (∫ t in x..y, |pinA Ψ z t * (Real.cos t * pinV Ψ z t) * pinL x t|) := by
          linarith
      _ ≤ 2 * C₂ * B + 2 * Real.sqrt (At * (C₁ * B)) := by linarith
  -- the sup over subintervals
  have hsup := integral_Icc_le_of_subinterval_le (a := 0) (b := π / 2)
    (by linarith [Real.pi_pos]) hAint hAnn key
  have hAtle : At ≤ 2 * C₂ * B + 2 * Real.sqrt (At * (C₁ * B)) :=
    le_of_eq_of_le hLHSid.symm hsup
  -- the elementary AM–GM, and the conclusion
  have hAM : 2 * Real.sqrt (At * (C₁ * B)) ≤ At / 2 + 2 * (C₁ * B) := by
    have hs : (Real.sqrt (At * (C₁ * B))) ^ 2 = At * (C₁ * B) := Real.sq_sqrt (mul_nonneg hAtnn hCn)
    have h2 : 0 ≤ 2 * Real.sqrt (At * (C₁ * B)) := by positivity
    have h3 : 0 ≤ At / 2 + 2 * (C₁ * B) := by linarith
    have h4 : (2 * Real.sqrt (At * (C₁ * B))) ^ 2 ≤ (At / 2 + 2 * (C₁ * B)) ^ 2 := by
      nlinarith [hs, Real.sqrt_nonneg (At * (C₁ * B)), sq_nonneg (At / 2 - 2 * (C₁ * B))]
    have h5 := sq_le_sq.mp h4
    rwa [abs_of_nonneg h2, abs_of_nonneg h3] at h5
  have hfin : At ≤ 4 * (C₁ + C₂) * B := by nlinarith [hAtle, hAM, hCn, hBnn, hC₂.le]
  exact hfin

end Work.FTS_EllLimOK.PkgJets
