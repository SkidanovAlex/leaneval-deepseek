import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.AeI1Fts.Defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.identity
import Submission.Work.FTS.EllipticEst.AeI1Fts.radial_identity2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeI1Fts/identity_local` — the chain identity, using `radial_identity2`

A copy of `AeI1Fts.identity`'s proof in which the radial half is the (fresh, complete)
`AeI1Fts.radial_identity2`; this keeps the target `I1Paper_mixed` free of the `sorry` of
`AeI1Fts.radial_identity`.  All the auxiliary lemmas (`IP_self_eq`, `integral_Iz_eq_Ioi`, the
slicewise integrability facts, ...) are the ones of `AeI1Fts.identity`.
-/

namespace Work.FTS.EllipticEst.AeI1Fts

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)

theorem identity_local {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.AeI1Fts.U u))
    (hV : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.AeI1Fts.V u))
    (hA : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.AeI1Fts.AA u))
    (hB : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.AeI1Fts.BB u)) :
    Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeI1Fts.AA u)
        (Work.FTS.EllipticEst.AeI1Fts.BB u)
      = (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2
            * ∫ θ in Set.Ioo 0 (Real.pi / 2),
                (Work.FTS.EllipticEst.AeI1Fts.V u z θ) ^ 2
                  * Work.FTS.EllipticEst.AeI1Fts.sigE θ)
        - 2 * Work.Spaces.eta
            * Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeI1Fts.U u)
                (Work.FTS.EllipticEst.AeI1Fts.U u)
        - 2 * Work.Spaces.eta * (1 + Work.Spaces.eta)
            * (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2
                * ∫ θ in Set.Ioo 0 (Real.pi / 2),
                    (Work.FTS.EllipticEst.AeI1Fts.U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
                      * Work.FTS.EllipticEst.AeI1Fts.sig2 θ)
        - Work.FTS.EllipticEst.AngSecond.IP
            (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
              * Work.FTS.EllipticEst.AeI1Fts.U u z θ)
            (Work.FTS.EllipticEst.AeI1Fts.BB u) := by
  have hS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  -- ## the slicewise integrability hypotheses of the cross identity
  have hintA : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn (fun θ => (U u z θ) ^ 2 * sigE θ) Iθo := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    exact slice_sigE_int hU hz
  have hintV2 : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn
        (fun θ => (V u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Iθo := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    exact slice_sigE_int hV hz
  have hintN : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn (fun θ => (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))) Iθo := by
    have h0 := (N_bound h hV).1
    filter_upwards [h0] with z hz
    exact MeasureTheory.IntegrableOn.congr_fun hz (fun θ _ => by rw [sig2]) measurableSet_Ioo
  have hintC : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn (fun θ => U u z θ * V u z θ * Real.cos (2 * θ)
        * sig1 θ) Iθo := by
    filter_upwards [hintN, hintV2, MeasureTheory.ae_restrict_mem measurableSet_Ioi]
      with z hNz hVz hz
    have hmeas : MeasureTheory.AEStronglyMeasurable
        (fun θ => U u z θ * V u z θ * Real.cos (2 * θ)
          * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)))
        (MeasureTheory.volume.restrict Iθo) := by
      have hcontU : ContinuousOn (fun θ => U u z θ) Iθo :=
        (contDiffOn_slice_U_one hS hz).continuousOn
      have hcontV : ContinuousOn (fun θ => V u z θ) Iθo :=
        (contDiffOn_slice_V_one hS hz).continuousOn
      have hcontc : ContinuousOn (fun θ => Real.cos (2 * θ)) Iθo :=
        (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
      have hsin2 : Continuous (fun θ : ℝ => Real.sin (2 * θ)) :=
        Real.continuous_sin.comp (continuous_const.mul continuous_id)
      have hconts : ContinuousOn
          (fun θ => (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))) Iθo :=
        hsin2.continuousOn.rpow_const (fun θ hθ => by
          left
          have h1 : (0:ℝ) < 2 * θ := by linarith [hθ.1]
          have h2 : 2 * θ < Real.pi := by linarith [hθ.2, Real.pi_pos]
          exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 h2))
      exact (((hcontU.mul hcontV).mul hcontc).mul hconts).aestronglyMeasurable measurableSet_Ioo
    have hintC' := slice_cross_int hNz hVz hmeas
    exact MeasureTheory.IntegrableOn.congr_fun hintC' (fun θ _ => by rw [sig1]) measurableSet_Ioo
  -- ## the two halves of the chain
  have hR := radial_identity2 h hU hV hA hB
  have hC := cross_joint_h h hU hV hintA hintN hintC
  have hIp := IP_self_eq (U u)
  have h1 : Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeI1Fts.AA u)
        (Work.FTS.EllipticEst.AeI1Fts.BB u)
      = (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * ∫ θ in Set.Ioo 0 (Real.pi / 2),
            (Work.FTS.EllipticEst.AeI1Fts.V u z θ) ^ 2 * Work.FTS.EllipticEst.AeI1Fts.sigE θ)
        - 2 * Work.Spaces.eta * (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2
            * ∫ θ in Set.Ioo 0 (Real.pi / 2),
                Work.FTS.EllipticEst.AeI1Fts.U u z θ * Work.FTS.EllipticEst.AeI1Fts.V u z θ
                  * Real.cos (2 * θ) * Work.FTS.EllipticEst.AeI1Fts.sig1 θ)
        - Work.FTS.EllipticEst.AngSecond.IP
            (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
              * Work.FTS.EllipticEst.AeI1Fts.U u z θ)
            (Work.FTS.EllipticEst.AeI1Fts.BB u) := by
    linarith [hR]
  rw [h1, hC, hIp]
  ring


end

end Work.FTS.EllipticEst.AeI1Fts
