/-
Work module for the Elgindi finite-time singularity project.

# Derivative of the reduction-of-order integral `SingInt`

`SingInt θ = ∫_{π/4}^{π/2-θ} ds/(sin s · sin(2s)²)`; the fundamental theorem of calculus for the
variable upper limit, composed with `θ ↦ π/2 - θ` (whose derivative is `-1`), gives

`deriv SingInt θ = -LzeroSingIntegrand (π/2 - θ)` for `θ ∈ (0, π/2)`.

This is the `hA` step of `Submission/Work/FTS/EllipticEst/LzeroSingWronskian.lean`, exported as a
standalone lemma.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EllipticEst.LzeroSingAuxDefs
import Submission.Work.FTS.EllipticEst.LzeroSingWronskian

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

theorem SingInt_hasDerivAt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
    HasDerivAt SingInt (-(LzeroSingIntegrand (Real.pi / 2 - θ))) θ := by
  intro θ hθ
  obtain ⟨hθ0, hθπ⟩ := hθ
  have hb0 : 0 < Real.pi / 2 - θ := by linarith
  have hbp : Real.pi / 2 - θ < Real.pi / 2 := by linarith
  have hmem : (Real.pi / 2 - θ) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hb0, hbp⟩
  have hcont_g : ContinuousAt LzeroSingIntegrand (Real.pi / 2 - θ) :=
    continuousOn_LzeroSingIntegrand.continuousAt (isOpen_Ioo.mem_nhds hmem)
  have hsm : StronglyMeasurableAtFilter LzeroSingIntegrand (nhds (Real.pi / 2 - θ)) volume :=
    ContinuousAt.stronglyMeasurableAtFilter (s := Set.Ioo (0 : ℝ) (Real.pi / 2)) isOpen_Ioo
      (fun x hx => continuousOn_LzeroSingIntegrand.continuousAt (isOpen_Ioo.mem_nhds hx))
      (Real.pi / 2 - θ) hmem
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
  change HasDerivAt (fun t : ℝ =>
      ∫ s in (Real.pi / 4)..(Real.pi / 2 - t), LzeroSingIntegrand s)
    (-(LzeroSingIntegrand (Real.pi / 2 - θ))) θ
  exact hA

end Work.FTS.EllipticEst
