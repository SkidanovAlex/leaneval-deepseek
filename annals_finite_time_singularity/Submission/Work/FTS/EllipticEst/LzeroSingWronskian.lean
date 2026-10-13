/-
Copyright: work module for the Elgindi finite-time singularity project.

# The Wronskian certificate of the two solutions of `Lzero` at `θ = π/2`

`LzeroSing θ = sin(2θ) · ∫_{π/4}^{π/2-θ} ds/(sin s · sin(2s)²)` is the reduction-of-order
solution of `Lzero Ψ = -∂_θθΨ + ∂_θ(tan θ · Ψ) - 6Ψ = 0` built on the regular solution
`LzeroReg θ = sin 2θ`, with the Wronskian normalised so that `W = -1/cos θ` on `(0, π/2)`.
This module proves that identity.  The computation is the elementary one: with
`A θ = ∫_{π/4}^{π/2-θ} g`, `g = LzeroSingIntegrand`, the fundamental theorem of calculus gives
`A' θ = -g(π/2-θ)`, hence

`LzeroReg θ · LzeroSing' θ - LzeroReg' θ · LzeroSing θ = -sin(2θ)² · g(π/2-θ)`

and `g(π/2-θ) = 1/(cos θ · sin(2θ)²)`.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EllipticEst.LzeroSingDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

/-- The reduction weight `s ↦ 1/(sin s · sin(2s)²)` of the singular solution is continuous
on the open interval `(0, π/2)` (its two zeros are exactly the endpoints). -/
lemma continuousOn_LzeroSingIntegrand :
    ContinuousOn LzeroSingIntegrand (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  show ContinuousOn (fun s : ℝ => 1 / (Real.sin s * Real.sin (2 * s) ^ 2))
    (Set.Ioo (0 : ℝ) (Real.pi / 2))
  refine ContinuousOn.div continuousOn_const ?_ ?_
  · refine ContinuousOn.mul Real.continuous_sin.continuousOn ?_
    exact ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).pow 2
  · intro s hs
    obtain ⟨hs0, hsp⟩ := hs
    refine mul_ne_zero ?_ (pow_ne_zero 2 ?_)
    · exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hs0 (by linarith [Real.pi_pos]))
    · exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))

theorem LzeroSingWronskian : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
    Work.FTS.EllipticEst.LzeroReg θ * deriv Work.FTS.EllipticEst.LzeroSing θ
      - deriv Work.FTS.EllipticEst.LzeroReg θ * Work.FTS.EllipticEst.LzeroSing θ
      = -1 / Real.cos θ := by
  intro θ hθ
  obtain ⟨hθ0, hθπ⟩ := hθ
  -- Positivity facts at the point `θ` and at the integration endpoint `π/2 - θ`.
  have hcos_pos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθπ⟩
  have hcos_ne : Real.cos θ ≠ 0 := ne_of_gt hcos_pos
  have hsin2_ne : Real.sin (2 * θ) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
  have hb0 : 0 < Real.pi / 2 - θ := by linarith
  have hbp : Real.pi / 2 - θ < Real.pi / 2 := by linarith
  have hmem : (Real.pi / 2 - θ) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hb0, hbp⟩
  -- The integrand is continuous at the (variable) upper endpoint.
  have hcont_g : ContinuousAt LzeroSingIntegrand (Real.pi / 2 - θ) :=
    continuousOn_LzeroSingIntegrand.continuousAt (isOpen_Ioo.mem_nhds hmem)
  have hsm : StronglyMeasurableAtFilter LzeroSingIntegrand (nhds (Real.pi / 2 - θ)) volume :=
    ContinuousAt.stronglyMeasurableAtFilter (s := Set.Ioo (0 : ℝ) (Real.pi / 2)) isOpen_Ioo
      (fun x hx => continuousOn_LzeroSingIntegrand.continuousAt (isOpen_Ioo.mem_nhds hx))
      (Real.pi / 2 - θ) hmem
  -- ... and interval-integrable over `[π/4, π/2 - θ]`, a compact subinterval of `(0, π/2)`.
  have hsub : Set.uIcc (Real.pi / 4) (Real.pi / 2 - θ) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro s hs
    rw [Set.mem_uIcc] at hs
    have hmin : 0 < min (Real.pi / 4) (Real.pi / 2 - θ) := lt_min (by linarith) hb0
    have hmax : max (Real.pi / 4) (Real.pi / 2 - θ) < Real.pi / 2 := max_lt (by linarith) hbp
    rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by linarith, by linarith⟩
    · exact ⟨by linarith, by linarith⟩
  have hII : IntervalIntegrable LzeroSingIntegrand volume (Real.pi / 4) (Real.pi / 2 - θ) :=
    (continuousOn_LzeroSingIntegrand.mono hsub).intervalIntegrable
  -- Fundamental theorem of calculus for the variable upper limit, composed with `π/2 - ·`.
  have hA' : HasDerivAt (fun u : ℝ => ∫ s in (Real.pi / 4)..u, LzeroSingIntegrand s)
      (LzeroSingIntegrand (Real.pi / 2 - θ)) (Real.pi / 2 - θ) :=
    intervalIntegral.integral_hasDerivAt_right hII hsm hcont_g
  have hinner : HasDerivAt (fun u : ℝ => Real.pi / 2 - u) (-1) θ := by
    have h : HasDerivAt (fun u : ℝ => Real.pi / 2 - u) (0 - 1) θ :=
      (hasDerivAt_const (x := θ) (Real.pi / 2)).sub (hasDerivAt_id θ)
    exact h.congr_deriv (by ring)
  have hA : HasDerivAt (fun t : ℝ =>
        ∫ s in (Real.pi / 4)..(Real.pi / 2 - t), LzeroSingIntegrand s)
      (-(LzeroSingIntegrand (Real.pi / 2 - θ))) θ := by
    have h := hA'.comp θ hinner
    exact h.congr_deriv (by ring)
  -- Derivative of the regular solution `sin 2θ`.
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (2 * Real.cos (2 * θ)) θ := by
    have h2 : HasDerivAt (fun t : ℝ => (2 : ℝ) * t) 2 θ := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id θ).const_mul 2
    exact ((Real.hasDerivAt_sin (2 * θ)).comp θ h2).congr_deriv (by ring)
  -- Derivative of the singular solution: product rule with `A` above.
  have hLS : HasDerivAt LzeroSing
      (2 * Real.cos (2 * θ) * (∫ s in (Real.pi / 4)..(Real.pi / 2 - θ),
          LzeroSingIntegrand s)
        + Real.sin (2 * θ) * (-(LzeroSingIntegrand (Real.pi / 2 - θ)))) θ :=
    hsin.mul hA
  have hReg : HasDerivAt LzeroReg (2 * Real.cos (2 * θ)) θ := hsin
  have hderivS : deriv LzeroSing θ
      = 2 * Real.cos (2 * θ) * (∫ s in (Real.pi / 4)..(Real.pi / 2 - θ),
          LzeroSingIntegrand s)
        + Real.sin (2 * θ) * (-(LzeroSingIntegrand (Real.pi / 2 - θ))) := hLS.deriv
  have hderivR : deriv LzeroReg θ = 2 * Real.cos (2 * θ) := hReg.deriv
  rw [hderivS, hderivR]
  have hLSθ : LzeroSing θ
      = Real.sin (2 * θ) * (∫ s in (Real.pi / 4)..(Real.pi / 2 - θ),
          LzeroSingIntegrand s) := rfl
  have hRegθ : LzeroReg θ = Real.sin (2 * θ) := rfl
  rw [hLSθ, hRegθ]
  -- Evaluate the weight at the endpoint and finish with field arithmetic.
  have hgval : LzeroSingIntegrand (Real.pi / 2 - θ)
      = 1 / (Real.cos θ * Real.sin (2 * θ) ^ 2) := by
    have h1 : Real.sin (Real.pi / 2 - θ) = Real.cos θ := Real.sin_pi_div_two_sub θ
    have h2 : Real.sin (2 * (Real.pi / 2 - θ)) = Real.sin (2 * θ) := by
      rw [show 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ by ring, Real.sin_pi_sub]
    simp only [LzeroSingIntegrand, h1, h2]
  rw [hgval]
  field_simp
  ring

end Work.FTS.EllipticEst
