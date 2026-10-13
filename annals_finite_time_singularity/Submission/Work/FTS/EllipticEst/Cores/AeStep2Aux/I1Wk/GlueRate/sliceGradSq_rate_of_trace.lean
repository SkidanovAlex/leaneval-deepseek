/-
Copyright: work module for the Elgindi finite-time singularity project.

# The *squared* endpoint rate of the angular slice of `U = z ∂_z u`, from the trace data

`Work.FTS.EllipticEst.remov.AeNj.sliceRateTwoLeft` / `...sliceRateTwoRight` give, for a `C¹`
slice `f` on `(0,π/2)` with integrable weighted derivative energy
`∫ (f')² σ` (`σ = thEta = sin(2θ)^{-η}`) and vanishing endpoint traces, the two *square-root*
rates

* `|f θ| ≤ 2 √(∫_{0<θ'<θ} (f')²σ) · θ^{(1+η)/2}`,
* `|f θ| ≤ 2 √(∫_{θ<θ'<π/2} (f')²σ) · (π/2-θ)^{(1+η)/2}`.

Squaring them turns the rate into the *quadratic* form used by the assembly of the `I₁`
estimate:

* `f(θ)² ≤ 4 θ^{1+η} ∫_{0<θ'<θ} (f')²σ`,
* `f(θ)² ≤ 4 (π/2-θ)^{1+η} ∫_{θ<θ'<π/2} (f')²σ`.

Here the slice is `f = (θ ↦ U u z θ)` with `U u = z ∂_z u` (the radial-weighted derivative of
the datum), whose derivative is the mixed slot `V u = z ∂_z∂_θ u` by Clairaut
(`AeI1Fts.slice_deriv_eq`).  The hypotheses are the trace conditions at the two endpoints
(`z ∂_zu → 0`) and the integrability of the slice energy, so the result is the squared,
explicit-constant form of `AeI1Fts.slice_rate` restricted to a single slice `z > 0`.

Everything is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.AngAWeak.aeGradTraceAe
import Submission.Work.FTS.EllipticEst.remov.AeNj.sliceRateUniformFts
import Submission.Work.FTS.EllipticEst.remov.AeNj.sliceRateTwoRight

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.GlueRate

set_option autoImplicit false

/-- **Squaring a square-root rate.**  From `|f| ≤ 2 √B · c^{(1+η)/2}` with `c > 0` and `B ≥ 0`
deduce `f² ≤ 4 c^{1+η} B` (the two constants `2` and `√B` are squared with
`(√B)² = B`, and `(c^{(1+η)/2})² = c^{1+η}` by `rpow_add`). -/
private theorem sq_le_of_abs_le_sqrt {f B c : ℝ} (hc : 0 < c) (hB : 0 ≤ B)
    (h : |f| ≤ 2 * Real.sqrt B * c ^ ((1 + Work.Spaces.eta) / 2)) :
    f ^ 2 ≤ 4 * c ^ (1 + Work.Spaces.eta) * B := by
  have hc0 : 0 ≤ c := hc.le
  have hRnn : 0 ≤ 2 * Real.sqrt B * c ^ ((1 + Work.Spaces.eta) / 2) :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg B)) (Real.rpow_nonneg hc0 _)
  have hsq : |f| ^ 2 ≤ (2 * Real.sqrt B * c ^ ((1 + Work.Spaces.eta) / 2)) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg f) h 2
  have hc2 : (c ^ ((1 + Work.Spaces.eta) / 2)) ^ 2 = c ^ (1 + Work.Spaces.eta) := by
    rw [sq, ← Real.rpow_add hc]
    congr 1
    ring
  have hR2 : (2 * Real.sqrt B * c ^ ((1 + Work.Spaces.eta) / 2)) ^ 2
      = 4 * B * c ^ (1 + Work.Spaces.eta) := by
    calc (2 * Real.sqrt B * c ^ ((1 + Work.Spaces.eta) / 2)) ^ 2
        = 4 * (Real.sqrt B) ^ 2 * (c ^ ((1 + Work.Spaces.eta) / 2)) ^ 2 := by ring
      _ = 4 * B * c ^ (1 + Work.Spaces.eta) := by rw [Real.sq_sqrt hB, hc2]
  rw [sq_abs, hR2] at hsq
  calc f ^ 2 ≤ 4 * B * c ^ (1 + Work.Spaces.eta) := hsq
    _ = 4 * c ^ (1 + Work.Spaces.eta) * B := by ring

theorem sliceGradSq_rate_of_trace {u : ℝ → ℝ → ℝ}
    (hS : Work.FTS.EllipticEst.SmoothOpen u)
    {z : ℝ} (hz : 0 < z)
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) (Set.Ioo 0 (Real.pi / 2)))
    (htrL : Filter.Tendsto (fun θ => z * Work.Spaces.pz u z θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (htrR : Filter.Tendsto (fun θ => z * Work.Spaces.pz u z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (z * Work.Spaces.pz u z θ) ^ 2
        ≤ 4 * θ ^ (1 + Work.Spaces.eta)
          * ∫ t in Set.Ioo 0 θ, (z * Work.Spaces.pz (Work.Spaces.pth u) z t) ^ 2
              * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)))
    ∧ (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (z * Work.Spaces.pz u z θ) ^ 2
        ≤ 4 * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)
          * ∫ t in Set.Ioo θ (Real.pi / 2), (z * Work.Spaces.pz (Work.Spaces.pth u) z t) ^ 2
              * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta))) := by
  -- The slice `θ ↦ U u z θ` is `C¹` on the open interval.
  have hf : ContDiffOn ℝ 1 (fun θ : ℝ => Work.FTS.EllipticEst.AeI1Fts.U u z θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Work.FTS.EllipticEst.AeI1Fts.contDiffOn_slice_U_one hS hz
  -- Transport the integrability of the weighted derivative square along Clairaut.
  have hintD : MeasureTheory.IntegrableOn
      (fun θ : ℝ =>
        (deriv (fun θ' : ℝ => Work.FTS.EllipticEst.AeI1Fts.U u z θ') θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    refine hint.congr_fun (fun θ hθ => ?_) measurableSet_Ioo
    rw [Work.FTS.EllipticEst.AeI1Fts.slice_deriv_eq hS hz hθ]
    rfl
  -- the two square-root rates
  have hL := Work.FTS.EllipticEst.remov.AeNj.sliceRateTwoLeft hf hintD htrL
  have hR := Work.FTS.EllipticEst.remov.AeNj.sliceRateTwoRight hf hintD htrR
  -- the two truncated energies, rewritten with the mixed slot
  have hintEqL : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (∫ t in Set.Ioo 0 θ,
          (deriv (fun θ' : ℝ => Work.FTS.EllipticEst.AeI1Fts.U u z θ') t) ^ 2
            * Work.FTS.EllipticEst.thEta t)
        = ∫ t in Set.Ioo 0 θ, (z * Work.Spaces.pz (Work.Spaces.pth u) z t) ^ 2
            * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)) := by
    intro θ hθ
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
    rw [Work.FTS.EllipticEst.AeI1Fts.slice_deriv_eq hS hz ⟨ht.1, lt_trans ht.2 hθ.2⟩]
    rfl
  have hintEqR : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (∫ t in Set.Ioo θ (Real.pi / 2),
          (deriv (fun θ' : ℝ => Work.FTS.EllipticEst.AeI1Fts.U u z θ') t) ^ 2
            * Work.FTS.EllipticEst.thEta t)
        = ∫ t in Set.Ioo θ (Real.pi / 2),
            (z * Work.Spaces.pz (Work.Spaces.pth u) z t) ^ 2
              * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)) := by
    intro θ hθ
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
    rw [Work.FTS.EllipticEst.AeI1Fts.slice_deriv_eq hS hz
      ⟨lt_trans hθ.1 ht.1, ht.2⟩]
    rfl
  constructor
  · -- the `0⁺` half
    intro θ hθ
    have h := hL θ hθ
    rw [hintEqL θ hθ] at h
    have hE : 0 ≤ ∫ t in Set.Ioo 0 θ,
        (z * Work.Spaces.pz (Work.Spaces.pth u) z t) ^ 2
          * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)) :=
      MeasureTheory.setIntegral_nonneg measurableSet_Ioo fun t ht =>
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
          (by linarith [ht.1]) (by linarith [ht.2, hθ.2, Real.pi_pos])) _)
    exact sq_le_of_abs_le_sqrt hθ.1 hE h
  · -- the `(π/2)⁻` half
    intro θ hθ
    have h := hR θ hθ
    rw [hintEqR θ hθ] at h
    have hE : 0 ≤ ∫ t in Set.Ioo θ (Real.pi / 2),
        (z * Work.Spaces.pz (Work.Spaces.pth u) z t) ^ 2
          * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)) :=
      MeasureTheory.setIntegral_nonneg measurableSet_Ioo fun t ht =>
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
          (by linarith [hθ.1, ht.1]) (by linarith [ht.2, Real.pi_pos])) _)
    exact sq_le_of_abs_le_sqrt (by linarith [hθ.2]) hE h

end Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.GlueRate
