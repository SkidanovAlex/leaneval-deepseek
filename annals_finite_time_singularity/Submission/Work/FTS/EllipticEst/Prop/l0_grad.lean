import Mathlib.Analysis.Real.Sqrt
import Submission.Work.FTS.EllipticEst.Honest.FOH.psiRho
import Submission.Work.FTS.EllipticEst.Prop.cutEnergyProof
import Submission.Work.FTS.EllipticEst.Prop.sigmaEnergy
import Submission.Work.FTS.LocDataExt.LocG5
import Submission.Work.FTS.StrongPersist.QangSq6Full
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Prop

set_option autoImplicit false

open scoped Real Topology
open MeasureTheory Set Filter

theorem l0_grad : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ →
      Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ) ∧
      α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ))
        ≤ C * Real.sqrt (Work.Spaces.HkSq α 0 F) := by
  -- the `u`-mass bound, from the `w²`-weighted radial energy inequality
  obtain ⟨Cm, hCmpos, hmass⟩ :=
    Work.FTS.EllipticEst.Cores.Pieces.AeGradRho.ae_mass_bound_of
      (fun α u G hA => Work.FTS.EllipticEst.Cores.Pieces.AeGradRho.aeEnergyOfCutEnergy
        cutEnergyProof α u G hA)
  -- the `σ`-weighted radial energy inequality
  obtain ⟨Cs, hCspos, hsig⟩ := sigmaEnergy
  refine ⟨Real.sqrt (Cs * (1 + Cm ^ 2)), Real.sqrt_pos.mpr (by positivity), ?_⟩
  intro α F Ψ hα hα4 hW
  have hA : Work.FTS.EllipticEst.H2W.Ae.AeData α Ψ F :=
    aeData_of_ellWeakPos hα hα4 hW
  -- ## the honesty of `z ∂_zΨ` (Agmon–Nirenberg)
  have hgrad : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ) :=
    Work.FTS.EllipticEst.Dispatch.hkMem_gradUD α Ψ F hA
  refine ⟨hgrad, ?_⟩
  -- ## the quantitative bound
  have hm := hmass α Ψ F hA
  have hs := hsig α Ψ F hA
  have hCm0 : (0 : ℝ) ≤ Cm := le_of_lt hCmpos
  have hCs0 : (0 : ℝ) ≤ Cs := le_of_lt hCspos
  have hFu : (Work.FTS.EllipticEst.H2W.Ae.nrm α Ψ) ^ 2 = Work.Spaces.HkSq α 0 Ψ :=
    Work.FTS.EllipticEst.Honest.hksq_sqrt_sq α Ψ
  have hFG : (Work.FTS.EllipticEst.H2W.Ae.nrm α F) ^ 2 = Work.Spaces.HkSq α 0 F :=
    Work.FTS.EllipticEst.Honest.hksq_sqrt_sq α F
  have hFg : (Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.grad Ψ)) ^ 2
      = Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad Ψ) :=
    Work.FTS.EllipticEst.Honest.hksq_sqrt_sq α _
  -- the `u`-mass, squared
  have hmu : Work.Spaces.HkSq α 0 Ψ ≤ Cm ^ 2 * Work.Spaces.HkSq α 0 F := by
    have h0 : (0 : ℝ) ≤ Work.FTS.EllipticEst.H2W.Ae.nrm α Ψ := Real.sqrt_nonneg _
    have h1 : (0 : ℝ) ≤ Work.FTS.EllipticEst.H2W.Ae.nrm α F := Real.sqrt_nonneg _
    have h2 : (Work.FTS.EllipticEst.H2W.Ae.nrm α Ψ) ^ 2
        ≤ (Cm * Work.FTS.EllipticEst.H2W.Ae.nrm α F) ^ 2 := pow_le_pow_left₀ h0 hm 2
    rw [mul_pow, hFu, hFG] at h2
    exact h2
  have hkey : α ^ 2 * Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad Ψ)
      ≤ Cs * (1 + Cm ^ 2) * Work.Spaces.HkSq α 0 F := by
    have h1 := mul_le_mul_of_nonneg_left
      (add_le_add_left hmu (Work.Spaces.HkSq α 0 F)) hCs0
    have h2 : Cs * (Work.Spaces.HkSq α 0 F + Cm ^ 2 * Work.Spaces.HkSq α 0 F)
        = Cs * (1 + Cm ^ 2) * Work.Spaces.HkSq α 0 F := by ring
    linarith [hs, h1, h2.le, h2.ge]
  -- square everything (both sides are nonnegative)
  have hsq : (α * Work.FTS.EllipticEst.H2W.Ae.nrm α
        (Work.FTS.EllipticEst.H2W.Ae.grad Ψ)) ^ 2
      ≤ (Real.sqrt (Cs * (1 + Cm ^ 2))
          * Work.FTS.EllipticEst.H2W.Ae.nrm α F) ^ 2 := by
    have hleft : (α * Work.FTS.EllipticEst.H2W.Ae.nrm α
        (Work.FTS.EllipticEst.H2W.Ae.grad Ψ)) ^ 2
        = α ^ 2 * Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad Ψ) := by
      rw [mul_pow, hFg]
    have hright : (Real.sqrt (Cs * (1 + Cm ^ 2))
          * Work.FTS.EllipticEst.H2W.Ae.nrm α F) ^ 2
        = Cs * (1 + Cm ^ 2) * Work.Spaces.HkSq α 0 F := by
      rw [mul_pow, Real.sq_sqrt (by positivity), hFG]
    rw [hleft, hright]
    exact hkey
  have hnn : (0 : ℝ) ≤ α * Work.FTS.EllipticEst.H2W.Ae.nrm α
      (Work.FTS.EllipticEst.H2W.Ae.grad Ψ) :=
    mul_nonneg (le_of_lt hα) (Real.sqrt_nonneg _)
  have hnn2 : (0 : ℝ) ≤ Real.sqrt (Cs * (1 + Cm ^ 2))
      * Work.FTS.EllipticEst.H2W.Ae.nrm α F :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hfin := le_of_sq_le_sq hsq hnn2
  change α * Real.sqrt (Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad Ψ))
      ≤ Real.sqrt (Cs * (1 + Cm ^ 2)) * Real.sqrt (Work.Spaces.HkSq α 0 F)
  exact hfin

end Work.FTS.EllipticEst.Prop
