/-
Copyright: work module for the Elgindi finite-time singularity project.

# Step 3 (the angular term `u = ∂_θ(tan θ · Ψ)`) of the honest level-`0` estimate

This module proves `Work.FTS.EllipticEst.Honest.step3Angle`: in the honest class `Hon α F Ψ`
of `Honest/Basic.lean` there is a universal constant `C > 0` with

  `‖∂_θ(tan θ · Ψ)‖_ρ ≤ C (‖F‖_ρ + α ‖z ∂_z Ψ‖_ρ)`,

where `‖g‖_ρ² = Work.Spaces.HkSq α 0 g = ∫_z ∫_θ (g z θ · w z / sin(2θ)^{η/2})²`.

## Route

On the open quadrant the pointwise identity

  `∂_θ(tan θ · Ψ) = Ψ + sin θ · ∂_θ(Ψ / cos θ)`

holds (`Honest.pth_tan_mul_eq_open`, in `Honest/step3Defs.lean`), so with
`P = sin θ · ∂_θ(Ψ/cos θ)` the two `HkSq`-norms are related by the triangle inequality
(`HkSq_add_le_of_pointwise`)

  `√(HkSq α 0 u) ≤ √2 (√(HkSq α 0 Ψ) + √(HkSq α 0 P))`.

The three analytic ingredients are then

* `√(HkSq α 0 Ψ) ≤ C‖F‖_ρ`, together with `HkMem α 0 Ψ` and `HkMem α 0 (z∂_zΨ)`
  (Step 1, `Honest/step1FirstOrder`),
* `√(HkSq α 0 (∂_θθΨ)) ≤ C(‖F‖_ρ + α‖z∂_zΨ‖_ρ)` (Step 2, `Honest/step2Angular`),
* `√(HkSq α 0 P) ≤ C(√(HkSq α 0 Ψ) + √(HkSq α 0 (∂_θθΨ)))`
  (the `I₄`/`I_{4,2}` positivity of Step 2, `Honest/step3PsiBar`),

plus the honesty `HkMem α 0 P` of `P` (`Honest/step3PMem`).  The assembly below isolates the
two purely `HkSq`-level steps (`HkSq_uOf_le`, `sqrt_HkSq_uOf_le`) and the arithmetic
(`step3Angle_of_pieces`), so that the final theorem is a short instantiation.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.Final.Step3Helpers
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.Honest.step3Defs
import Submission.Work.FTS.EllipticEst.HkNorm_add_le
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Blocks.HkMem_of_majorant_aesm
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem
import Submission.Work.FTS.EllipticEst.AngClean.IPMem_F_Phi
import Submission.Work.FTS.EllipticEst.Honest.AesmCross.aesmSliceCross
import Submission.Work.FTS.EllipticEst.Honest.AesmCross.aesmProdCross
import Submission.Work.FTS.EllipticEst.Honest.HonMemU.honMemPthTan
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.Honest.firstOrderHonest
import Submission.Work.FTS.EllipticEst.Honest.step3BAngularClean
import Submission.Work.FTS.EllipticEst.Honest.step3PsiBoundFree
import Submission.Work.FTS.EllipticEst.Honest.I1LowerHonest

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The assembly from the three analytic pieces

(The slice helpers that used to precede this — `HkIntegrand_zero_boundary`, `HkSq_uOf_le`,
`sqrt_HkSq_uOf_le`, `smoothOpen_POf`, `HkIntegrand_POf_le`, … — now live in
`Submission/Work/FTS/EllipticEst/Final/Step3Helpers.lean`, which this file imports.) -/

theorem step3Angle_of_pieces
    (C1 C2 C3 : ℝ) (hC1 : 0 < C1) (hC2 : 0 < C2) (hC3 : 0 < C3)
    (S1mem : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), Hon α F Ψ → Work.Spaces.HkMem α 0 Ψ)
    (S1memG : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), Hon α F Ψ → Work.Spaces.HkMem α 0 (GOf Ψ))
    (S1b : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), Hon α F Ψ →
      Real.sqrt (Work.Spaces.HkSq α 0 Ψ) ≤ C1 * Real.sqrt (Work.Spaces.HkSq α 0 F))
    (S2b : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), Hon α F Ψ →
      Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ))
        ≤ C2 * (Real.sqrt (Work.Spaces.HkSq α 0 F)
          + α * Real.sqrt (Work.Spaces.HkSq α 0 (GOf Ψ))))
    (S3b : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), Hon α F Ψ →
      Real.sqrt (Work.Spaces.HkSq α 0 (POf Ψ))
        ≤ C3 * (Real.sqrt (Work.Spaces.HkSq α 0 Ψ)
          + Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ))))
    (Pmem : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), Hon α F Ψ → Work.Spaces.HkMem α 0 (POf Ψ)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), Hon α F Ψ →
        Real.sqrt (Work.Spaces.HkSq α 0 (uOf Ψ))
          ≤ C * (Real.sqrt (Work.Spaces.HkSq α 0 F)
            + α * Real.sqrt (Work.Spaces.HkSq α 0 (GOf Ψ))) := by
  have hC0 : (0 : ℝ) < Real.sqrt 2 * (C1 + C3 * (C1 + C2)) + 1 := by positivity
  refine ⟨Real.sqrt 2 * (C1 + C3 * (C1 + C2)) + 1, hC0, ?_⟩
  intro α F Ψ h
  have htr := sqrt_HkSq_uOf_le (α := α) (Ψ := Ψ) h.sm (S1mem α F Ψ h) (Pmem α F Ψ h)
  have h1 := S1b α F Ψ h
  have h2 := S2b α F Ψ h
  have h3 := S3b α F Ψ h
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hF : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 0 F) := Real.sqrt_nonneg _
  have hG : 0 ≤ α * Real.sqrt (Work.Spaces.HkSq α 0 (GOf Ψ)) :=
    mul_nonneg (le_of_lt h.hα) (Real.sqrt_nonneg _)
  have hfg : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 0 F)
      + α * Real.sqrt (Work.Spaces.HkSq α 0 (GOf Ψ)) := by linarith
  -- the two `HkSq`-level bounds give `√u ≤ √2 (m + p)`
  have hmp : Real.sqrt 2 * (Real.sqrt (Work.Spaces.HkSq α 0 Ψ)
        + Real.sqrt (Work.Spaces.HkSq α 0 (POf Ψ)))
      ≤ Real.sqrt 2 * (C1 * Real.sqrt (Work.Spaces.HkSq α 0 F)
          + C3 * (C1 * Real.sqrt (Work.Spaces.HkSq α 0 F)
            + C2 * (Real.sqrt (Work.Spaces.HkSq α 0 F)
              + α * Real.sqrt (Work.Spaces.HkSq α 0 (GOf Ψ))))) := by
    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hs2)
    have h3' : C3 * (Real.sqrt (Work.Spaces.HkSq α 0 Ψ)
          + Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ)))
        ≤ C3 * (C1 * Real.sqrt (Work.Spaces.HkSq α 0 F)
          + C2 * (Real.sqrt (Work.Spaces.HkSq α 0 F)
            + α * Real.sqrt (Work.Spaces.HkSq α 0 (GOf Ψ)))) :=
      mul_le_mul_of_nonneg_left (by linarith [h1, h2]) (le_of_lt hC3)
    linarith [h1, h3']
  -- and the arithmetic: `√2 (C1 f + C3 (C1 f + C2 (f + αg))) ≤ C (f + α g)`
  have hfinal : Real.sqrt 2 * (C1 * Real.sqrt (Work.Spaces.HkSq α 0 F)
        + C3 * (C1 * Real.sqrt (Work.Spaces.HkSq α 0 F)
          + C2 * (Real.sqrt (Work.Spaces.HkSq α 0 F)
            + α * Real.sqrt (Work.Spaces.HkSq α 0 (GOf Ψ)))))
      ≤ Real.sqrt 2 * ((C1 + C3 * (C1 + C2))
        * (Real.sqrt (Work.Spaces.HkSq α 0 F)
          + α * Real.sqrt (Work.Spaces.HkSq α 0 (GOf Ψ)))) := by
    have hA : C1 * Real.sqrt (Work.Spaces.HkSq α 0 F)
        + C3 * (C1 * Real.sqrt (Work.Spaces.HkSq α 0 F)
          + C2 * (Real.sqrt (Work.Spaces.HkSq α 0 F)
            + α * Real.sqrt (Work.Spaces.HkSq α 0 (GOf Ψ))))
        ≤ (C1 + C3 * (C1 + C2)) * (Real.sqrt (Work.Spaces.HkSq α 0 F)
          + α * Real.sqrt (Work.Spaces.HkSq α 0 (GOf Ψ))) := by
      nlinarith [mul_nonneg (le_of_lt hC1) hG,
        mul_nonneg (mul_nonneg (le_of_lt hC3) (le_of_lt hC1)) hG,
        mul_nonneg (mul_nonneg (le_of_lt hC3) (le_of_lt hC2)) hG,
        mul_nonneg (le_of_lt hC1) hF]
    exact mul_le_mul_of_nonneg_left hA (le_of_lt hs2)
  have hfin2 : (Real.sqrt 2 * (C1 + C3 * (C1 + C2)))
        * (Real.sqrt (Work.Spaces.HkSq α 0 F)
          + α * Real.sqrt (Work.Spaces.HkSq α 0 (GOf Ψ)))
      ≤ (Real.sqrt 2 * (C1 + C3 * (C1 + C2)) + 1)
        * (Real.sqrt (Work.Spaces.HkSq α 0 F)
          + α * Real.sqrt (Work.Spaces.HkSq α 0 (GOf Ψ))) := by
    have h1' : Real.sqrt 2 * (C1 + C3 * (C1 + C2))
        * (Real.sqrt (Work.Spaces.HkSq α 0 F)
          + α * Real.sqrt (Work.Spaces.HkSq α 0 (GOf Ψ)))
        + (Real.sqrt (Work.Spaces.HkSq α 0 F)
          + α * Real.sqrt (Work.Spaces.HkSq α 0 (GOf Ψ)))
        = (Real.sqrt 2 * (C1 + C3 * (C1 + C2)) + 1)
        * (Real.sqrt (Work.Spaces.HkSq α 0 F)
          + α * Real.sqrt (Work.Spaces.HkSq α 0 (GOf Ψ))) := by ring
    linarith [h1', hfg]
  linarith [htr, hmp, hfinal, hfin2]

/-- **`step3Angle` from the three analytic pieces, with the first-order input in the
`Honest/firstOrderHonest` form** (`√(HkSq α 0 Ψ) ≤ C(√(HkSq α 0 F) + α√(HkSq α 0 (z∂_zΨ)))`
instead of `≤ C√(HkSq α 0 F)`; the two are interchangeable in the assembly because the `αG`-term
is already on the right-hand side). -/
theorem step3Angle_of_pieces'
    (C1 C2 C3 : ℝ) (hC1 : 0 < C1) (hC2 : 0 < C2) (hC3 : 0 < C3)
    (S1mem : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), Hon α F Ψ → Work.Spaces.HkMem α 0 Ψ)
    (S1memG : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), Hon α F Ψ → Work.Spaces.HkMem α 0 (GOf Ψ))
    (S1b : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), Hon α F Ψ →
      Real.sqrt (Work.Spaces.HkSq α 0 Ψ)
        ≤ C1 * (Real.sqrt (Work.Spaces.HkSq α 0 F)
          + α * Real.sqrt (Work.Spaces.HkSq α 0 (GOf Ψ))))
    (S2b : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), Hon α F Ψ →
      Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ))
        ≤ C2 * (Real.sqrt (Work.Spaces.HkSq α 0 F)
          + α * Real.sqrt (Work.Spaces.HkSq α 0 (GOf Ψ))))
    (S3b : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), Hon α F Ψ →
      Real.sqrt (Work.Spaces.HkSq α 0 (POf Ψ))
        ≤ C3 * (Real.sqrt (Work.Spaces.HkSq α 0 Ψ)
          + Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ))))
    (Pmem : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), Hon α F Ψ → Work.Spaces.HkMem α 0 (POf Ψ)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), Hon α F Ψ →
        Real.sqrt (Work.Spaces.HkSq α 0 (uOf Ψ))
          ≤ C * (Real.sqrt (Work.Spaces.HkSq α 0 F)
            + α * Real.sqrt (Work.Spaces.HkSq α 0 (GOf Ψ))) := by
  have hC0 : (0 : ℝ) < Real.sqrt 2 * (C1 + C3 * (C1 + C2)) + 1 := by positivity
  refine ⟨Real.sqrt 2 * (C1 + C3 * (C1 + C2)) + 1, hC0, ?_⟩
  intro α F Ψ h
  have htr := sqrt_HkSq_uOf_le (α := α) (Ψ := Ψ) h.sm (S1mem α F Ψ h) (Pmem α F Ψ h)
  have h1 := S1b α F Ψ h
  have h2 := S2b α F Ψ h
  have h3 := S3b α F Ψ h
  have hf : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 0 F) := Real.sqrt_nonneg _
  have hg : 0 ≤ α * Real.sqrt (Work.Spaces.HkSq α 0 (GOf Ψ)) :=
    mul_nonneg (le_of_lt h.hα) (Real.sqrt_nonneg _)
  have hR : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 0 F)
      + α * Real.sqrt (Work.Spaces.HkSq α 0 (GOf Ψ)) := by linarith
  have hsq2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  -- the three bounds, in terms of the single quantity `R`
  have hm : Real.sqrt (Work.Spaces.HkSq α 0 Ψ)
      ≤ C1 * (Real.sqrt (Work.Spaces.HkSq α 0 F)
        + α * Real.sqrt (Work.Spaces.HkSq α 0 (GOf Ψ))) := h1
  have hb : Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ))
      ≤ C2 * (Real.sqrt (Work.Spaces.HkSq α 0 F)
        + α * Real.sqrt (Work.Spaces.HkSq α 0 (GOf Ψ))) := h2
  have hp : Real.sqrt (Work.Spaces.HkSq α 0 (POf Ψ))
      ≤ C3 * (Real.sqrt (Work.Spaces.HkSq α 0 Ψ)
        + Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ))) := h3
  have hm0 : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 0 Ψ) := Real.sqrt_nonneg _
  have hb0 : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ)) := Real.sqrt_nonneg _
  have hp0 : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 0 (POf Ψ)) := Real.sqrt_nonneg _
  -- `m + p ≤ (C1 + C3 (C1 + C2)) R`
  have hmp : Real.sqrt (Work.Spaces.HkSq α 0 Ψ) + Real.sqrt (Work.Spaces.HkSq α 0 (POf Ψ))
      ≤ (C1 + C3 * (C1 + C2)) * (Real.sqrt (Work.Spaces.HkSq α 0 F)
        + α * Real.sqrt (Work.Spaces.HkSq α 0 (GOf Ψ))) := by
    nlinarith [hm, hb, hp, hR, hC1, hC2, hC3,
      mul_nonneg (le_of_lt hC3) hR, mul_nonneg (mul_nonneg (le_of_lt hC3) (le_of_lt hC2)) hR,
      mul_nonneg (mul_nonneg (le_of_lt hC3) (le_of_lt hC1)) hR]
  -- assemble
  have hstep1 : Real.sqrt (Work.Spaces.HkSq α 0 (uOf Ψ))
      ≤ Real.sqrt 2 * ((C1 + C3 * (C1 + C2))
        * (Real.sqrt (Work.Spaces.HkSq α 0 F)
          + α * Real.sqrt (Work.Spaces.HkSq α 0 (GOf Ψ)))) := by
    refine le_trans htr (mul_le_mul_of_nonneg_left hmp (le_of_lt hsq2))
  refine le_trans hstep1 ?_
  have hstep2 : Real.sqrt 2 * ((C1 + C3 * (C1 + C2))
        * (Real.sqrt (Work.Spaces.HkSq α 0 F)
          + α * Real.sqrt (Work.Spaces.HkSq α 0 (GOf Ψ))))
      ≤ (Real.sqrt 2 * (C1 + C3 * (C1 + C2)))
        * (Real.sqrt (Work.Spaces.HkSq α 0 F)
          + α * Real.sqrt (Work.Spaces.HkSq α 0 (GOf Ψ))) := by
    rw [mul_assoc]
  refine le_trans hstep2 ?_
  have hCnn : 0 ≤ Real.sqrt 2 * (C1 + C3 * (C1 + C2)) := by positivity
  nlinarith [mul_nonneg hCnn hR]

/-! ## The six cross-honesty pairings (clash-free copy of `Honest.honCrossIPMems`)

`Honest/honCrossIPMems` proves the six `AngSecond.IPMem` facts below, but its file imports
`EllHyp_certificates` (which its proof does not use); that single import pulls
`ThetaPoincareDefs` and the `TT` frontier into the cone of every consumer, and `ThetaPoincareDefs`
declares `Work.FTS.EllipticEst.sin_two_nonneg`, which `TanTheta/Defs` also declares.  Since
`step3Angle`'s assembly also needs the `TanTheta`-based `step3PsiBar`, the pairings are reproved
here with the same proof and only the imports that proof uses.  Reported in `HANDOFF.md`. -/

/-- **Cross honesty from the two diagonal honesties and open-quadrant smoothness.** -/
theorem stepIPMem_of_HkMem_agreeOnQ {α : ℝ} {g h g' h' : ℝ → ℝ → ℝ}
    (hg' : Work.FTS.EllipticEst.SmoothOpen g') (hh' : Work.FTS.EllipticEst.SmoothOpen h')
    (hgg : Work.FTS.EllipticEst.AgreeOnQ g g') (hhh : Work.FTS.EllipticEst.AgreeOnQ h h')
    (hmg : Work.Spaces.HkMem α 0 g) (hmh : Work.Spaces.HkMem α 0 h) :
    Work.FTS.EllipticEst.AngSecond.IPMem g h :=
  Work.FTS.EllipticEst.AngClean.IPMem_of_diag_aesm
    (Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hmg)
    (Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hmh)
    (fun z hz => Work.FTS.EllipticEst.Honest.AesmCross.aesmSliceCross hg' hh' hgg hhh z hz)
    (Work.FTS.EllipticEst.Honest.AesmCross.aesmProdCross hg' hh' hgg hhh)

/-- **The six pairings against `B = ∂_θθΨ` that the Step-2 identity consumes.** -/
theorem stepCrossIPMems : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), Hon α F Ψ →
    Work.Spaces.HkMem α 0 Ψ →
    Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ) →
    Work.FTS.EllipticEst.AngSecond.IPMem F (Work.Spaces.pthIter 2 Ψ) ∧
    Work.FTS.EllipticEst.AngSecond.IPMem (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      (Work.Spaces.pthIter 2 Ψ) ∧
    Work.FTS.EllipticEst.AngSecond.IPMem (fun z θ => z * Work.Spaces.pz Ψ z θ)
      (Work.Spaces.pthIter 2 Ψ) ∧
    Work.FTS.EllipticEst.AngSecond.IPMem Ψ (Work.Spaces.pthIter 2 Ψ) ∧
    Work.FTS.EllipticEst.AngSecond.IPMem
      (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
      (Work.Spaces.pthIter 2 Ψ) ∧
    Work.FTS.EllipticEst.AngSecond.IPMem (Work.Spaces.pthIter 2 Ψ) (Work.Spaces.pthIter 2 Ψ) := by
  intro α F Ψ hHon hΨ hG
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hHon.sm
  have hBso : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) :=
    Work.FTS.EllipticEst.SmoothOpen.pth (Work.FTS.EllipticEst.SmoothOpen.pth hΨso)
  have hAso : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl Work.FTS.EllipticEst.Cert.smoothOpen_zsq_bsl
      (Work.FTS.EllipticEst.SmoothOpen.pzIter hΨso 2)
  have hGso : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z * Work.Spaces.pz Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl Work.FTS.EllipticEst.Cert.smoothOpen_z_bsl
      (Work.FTS.EllipticEst.SmoothOpen.pz hΨso)
  have huso : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ) :=
    Work.FTS.EllipticEst.SmoothOpen.pth (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
      Work.FTS.EllipticEst.Cert.smoothOpen_tan_bsl hΨso)
  have hFso : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α Ψ) :=
    Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hΨso
  have hFag : Work.FTS.EllipticEst.AgreeOnQ F (Work.Elliptic.bslOp α Ψ) :=
    fun z θ hz hθ0 hθ1 => (hHon.eq z hz θ hθ0 hθ1).symm
  have hu : Work.Spaces.HkMem α 0
      (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ) :=
    Work.FTS.EllipticEst.Honest.HonMemU.honMemPthTan α F Ψ hHon hΨ hG
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact stepIPMem_of_HkMem_agreeOnQ hFso hBso hFag (fun _ _ _ _ _ => rfl) hHon.memF hHon.memB
  · exact stepIPMem_of_HkMem_agreeOnQ hAso hBso (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
      hHon.memA hHon.memB
  · exact stepIPMem_of_HkMem_agreeOnQ hGso hBso (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
      hG hHon.memB
  · exact stepIPMem_of_HkMem_agreeOnQ hΨso hBso (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
      hΨ hHon.memB
  · exact stepIPMem_of_HkMem_agreeOnQ huso hBso (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
      hu hHon.memB
  · exact stepIPMem_of_HkMem_agreeOnQ hBso hBso (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
      hHon.memB hHon.memB

theorem step3Angle : ∃ C : ℝ, 0 < C ∧
  ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), Hon α F Ψ →
    Real.sqrt (Work.Spaces.HkSq α 0
        (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ))
      ≤ C * (Real.sqrt (Work.Spaces.HkSq α 0 F)
        + α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ))) := by
  obtain ⟨C₁, hC₁, hS1⟩ := firstOrderHonest
  obtain ⟨C₂, hC₂, hI1⟩ := I1LowerHonest
  obtain ⟨C₃, hC₃, hP3⟩ := step3PsiBoundFree
  obtain ⟨C₄, hC₄, hS2⟩ := step3BAngularClean C₁ C₂ hC₁ hC₂
    (fun α F Ψ h => (hS1 α F Ψ h).1)
    (fun α F Ψ h => (hS1 α F Ψ h).2.1)
    (fun α F Ψ h => (hS1 α F Ψ h).2.2.1)
    (fun α F Ψ h => (hS1 α F Ψ h).2.2.2.1)
    (fun α F Ψ h => (hS1 α F Ψ h).2.2.2.2)
    stepCrossIPMems
    (fun α F Ψ h hG => hI1 α F Ψ h hG)
  exact step3Angle_of_pieces' C₁ C₄ C₃ hC₁ hC₄ hC₃
    (fun α F Ψ h => (hS1 α F Ψ h).1)
    (fun α F Ψ h => (hS1 α F Ψ h).2.1)
    (fun α F Ψ h => (hS1 α F Ψ h).2.2.2.1)
    (fun α F Ψ h => hS2 α F Ψ h)
    (fun α F Ψ h => hP3 α F Ψ h (hS1 α F Ψ h).1 h.memB (hS1 α F Ψ h).2.2.1
      (hkMem_POf h (hS1 α F Ψ h).1 (hS1 α F Ψ h).2.1))
    (fun α F Ψ h => hkMem_POf h (hS1 α F Ψ h).1 (hS1 α F Ψ h).2.1)

end Work.FTS.EllipticEst.Honest
