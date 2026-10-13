import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.FTS.BSIdent.Defs
import Submission.Work.FTS.BSIdent.Cyl.DecayAux.Basic
import Submission.Work.FTS.BSIdent.Defs.contDiffAt_psiField_merPsi_of_mem_Uax
import Submission.Work.FTS_BSIdentP.Slim.DevStub
import Submission.Work.FTS_BSIdentP.Slim.Dev5

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FTS.BSIdentP.Dev6

open Work.FTS.BSIdent

open Filter Set MeasureTheory
open scoped Topology
open Work.FTS.BSIdentP.Dev5 (GG)

variable {τ : ℝ}

/-! ## The chain-rule formulas for the meridian derivatives -/

theorem pdZ_merPsiT_eq {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ} (hτ : τ = Physical.clockInv C t)
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (hB : 0 < B τ) {r z : ℝ} (hr : 0 < r) (hz : z ≠ 0) :
    Work.Cyl.pdZ (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) r z
      = 2 * z * (A τ)⁻¹ * GG Φ τ (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ)
            (Work.Cyl.thetaP r z)
        + (A τ)⁻¹ *
          (Work.FTS.Regularity.pExp α * z * (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ)
              * Work.Cyl.pdR (GG Φ τ) (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ)
                  (Work.Cyl.thetaP r z)
            + r * Work.Cyl.pdZ (GG Φ τ) (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ)
                  (Work.Cyl.thetaP r z)) := by
  rw [Dev5.merPsiT_eq_core α A B Φ C t hτ]
  refine Work.FTS.BSIdent.Cyl.pdZ_psiCore_eq (G := GG Φ τ) ?hG hr
  refine Dev5.diffAt2_GG_of_ne (τ := τ) hsm ?_ ?_ ?_
  · have := Work.Cyl.rhoP_pos (z := z) hr
    have : (0:ℝ) < Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ :=
      div_pos (Real.rpow_pos_of_pos this _) hB
    linarith
  · simp only [Work.Cyl.thetaP]
    exact fun h => hz (by
      have hzr : z / r = 0 := Real.arctan_eq_zero_iff.mp h
      rcases div_eq_zero_iff.mp hzr with h' | h'
      · exact h'
      · exact absurd h' (ne_of_gt hr))
  · have := Work.FTS.BSIdent.Cyl.abs_thetaP_lt r z
    linarith [Real.pi_pos]

theorem pdR_merPsiT_eq {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ} (hτ : τ = Physical.clockInv C t)
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (hB : 0 < B τ) {r z : ℝ} (hr : 0 < r) (hz : z ≠ 0) :
    Work.Cyl.pdR (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) r z
      = 2 * r * (A τ)⁻¹ * GG Φ τ (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ)
            (Work.Cyl.thetaP r z)
        + (A τ)⁻¹ *
          (Work.FTS.Regularity.pExp α * r * (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ)
              * Work.Cyl.pdR (GG Φ τ) (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ)
                  (Work.Cyl.thetaP r z)
            + (-z) * Work.Cyl.pdZ (GG Φ τ)
                  (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ)
                  (Work.Cyl.thetaP r z)) := by
  rw [Dev5.merPsiT_eq_core α A B Φ C t hτ]
  refine Work.FTS.BSIdent.Cyl.pdR_psiCore_eq (G := GG Φ τ) ?hG hr
  refine Dev5.diffAt2_GG_of_ne (τ := τ) hsm ?_ ?_ ?_
  · have := Work.Cyl.rhoP_pos (z := z) hr
    have : (0:ℝ) < Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ :=
      div_pos (Real.rpow_pos_of_pos this _) hB
    linarith
  · simp only [Work.Cyl.thetaP]
    exact fun h => hz (by
      have hzr : z / r = 0 := Real.arctan_eq_zero_iff.mp h
      rcases div_eq_zero_iff.mp hzr with h' | h'
      · exact h'
      · exact absurd h' (ne_of_gt hr))
  · have := Work.FTS.BSIdent.Cyl.abs_thetaP_lt r z
    linarith [Real.pi_pos]

end Work.FTS.BSIdentP.Dev6
