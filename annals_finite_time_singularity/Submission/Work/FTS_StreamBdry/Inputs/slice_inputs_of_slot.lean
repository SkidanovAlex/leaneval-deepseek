import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB25.Defs
import Submission.Work.FTS_StreamBdry.sb1_gauge_proved
import Submission.Work.FTS_FinalLeaves.psiCan_C3_proved
import Submission.Work.FTS_StreamBdry.Inputs.SliceTr
import Submission.Work.FTS_StreamBdry.Inputs.ftau_Dz_le
import Submission.Work.FTS_StreamBdry.Inputs.ftau_cont
import Submission.Work.FTS_StreamBdry.Inputs.ftau_Dz_cont

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS_StreamBdry.Inputs

/-- **Assembly of the three conjuncts** from `Work.FTS_StreamBdry.Inputs.SliceTr` (the `Γ`-decay,
the support and the angular vanishing of the profile) and the three leaves
`ftau_Dz_le` (pointwise bound of `D_z F`), `ftau_cont` (continuity of `F`) and `ftau_Dz_cont`
(continuity of `D_z F`):
`M` is the slot constant given by the hypothesis, and `Mf := max Cg MDz`, where `Cg` is the
constant of the `Γ`-bound of `F(τ)` (`|F| ≤ Cg·Γ ≤ Cg`) and `MDz` the bound of `D_z F(τ)`. -/
theorem slice_inputs_of_slot {a C₀ Ce Cs : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g G : Work.FTS.Galerkin.Fam} {A B : ℝ → ℝ}
    (hEL : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp a) E)
    (hStar : Work.FTS.VocabO2.StarPkgo2 (Work.FTS.Regularity.pExp a) Cs Φs)
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp a) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp a) C₀ Φs E g)
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' a S A B (Work.FTS.RegPkgGal.extG G))
    (hG : ∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ → G z θ τ = g z θ τ)
    (hslot : ∀ τ : ℝ, 0 ≤ τ → ∃ M : ℝ,
      Work.FTS.StreamBdryIface.SlotBd (Work.FTS.Regularity.pExp a)
        (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ) M) :
    ∀ τ, 0 ≤ τ → ∃ M L Mf : ℝ,
      ContDiffOn ℝ 3 (Function.uncurry
        (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ)) Work.Construction.Qd ∧
      Work.FTS.StreamBdryIface.SlotBd (Work.FTS.Regularity.pExp a)
        (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ) M ∧
      Work.FTS.StreamBdryIface.SrcOK
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ) L Mf := by
  intro τ hτ
  obtain ⟨M, hM⟩ := hslot τ hτ
  obtain ⟨MDz, hMDz0, hMDz⟩ := ftau_Dz_le ha ha13 hOK hreg hG τ hτ
  obtain ⟨Cg, hCg0, hCg⟩ := ftau_abs_le_Gamma ha ha13 hτ hreg hG
  obtain ⟨L, hL0, hL⟩ := ftau_supp hτ hreg hG
  have hvan : ∀ z : ℝ, 0 < z →
      Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ z 0 = 0 ∧
      Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ z (π / 2) = 0 :=
    ftau_vanish ha.ne' hτ hreg hG
  have hC3 : ContDiffOn ℝ 3 (Function.uncurry
      (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ)) Work.Construction.Qd := by
    have h := Work.FTS_FinalLeaves.psiCan_C3_proved (α := Work.FTS.Regularity.pExp a)
      hEL hStar hOK τ hτ
    have heq : (fun q : ℝ × ℝ => Work.FTS.Nonlin.PsiCan Φs E g q.1 q.2 τ)
        = Function.uncurry (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ) := by
      funext q
      simp only [Function.uncurry, Work.FTS.Galerkin.slice]
    rwa [heq] at h
  refine ⟨M, L, max Cg MDz, hC3, hM, ?_⟩
  refine ⟨ftau_cont ha ha13 hOK hreg hG τ hτ, ftau_Dz_cont ha ha13 hOK hreg hG τ hτ, ?_,
    hvan, hL0, hL⟩
  intro z θ hz hθ
  have hΓ : Work.FTS.Regularity.Gamma a θ ≤ 1 := by
    rw [Work.FTS.Regularity.Gamma_eq_Gam]
    exact Gam_le_one_of_Iθ ha hθ
  refine ⟨?_, le_trans (hMDz z θ hz hθ) (le_max_right _ _)⟩
  calc |Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ z θ|
      ≤ Cg * Work.FTS.Regularity.Gamma a θ := hCg z θ hz hθ
    _ ≤ Cg * 1 := mul_le_mul_of_nonneg_left hΓ hCg0
    _ = Cg := mul_one Cg
    _ ≤ max Cg MDz := le_max_left _ _

end Work.FTS_StreamBdry.Inputs
