import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.Inputs.slice_assy
import Submission.Work.FTS_StreamBdry.Inputs.srcOK_Ftau
import Submission.Work.FTS_StreamBdry.Inputs.residual_slot_jetsB
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_jets

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.Inputs

theorem slice_inputs {a C₀ Ce Cs : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp a) u →
      Work.FTS.VocabO.EllPkgGo (Work.FTS.Regularity.pExp a) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp a) 6 Ce u (E u))
    (hEL : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp a) E)
    (hStar : Work.FTS.VocabO2.StarPkgo2 (Work.FTS.Regularity.pExp a) Cs Φs)
    {g G : Work.FTS.Galerkin.Fam} {A B : ℝ → ℝ}
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp a) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp a) C₀ Φs E g)
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' a S A B (Work.FTS.RegPkgGal.extG G))
    (hG : ∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ → G z θ τ = g z θ τ) :
    ∀ τ, 0 ≤ τ → ∃ M L Mf : ℝ,
      ContDiffOn ℝ 3 (Function.uncurry
        (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ)) Work.Construction.Qd ∧
      Work.FTS.StreamBdryIface.SlotBd (Work.FTS.Regularity.pExp a)
        (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ) M ∧
      Work.FTS.StreamBdryIface.SrcOK
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ) L Mf := by
  exact slice_inputs_of_pieces ha ha13 hEll hEL hStar hSol hOK hreg hG
    (fun τ hτ => srcOK_Ftau ha ha13 hreg hG τ hτ)
    (fun τ hτ => residual_slot_jetsB ha ha13 hEll hEL hStar hSol hOK τ hτ)
    (fun τ hτ => by
      obtain ⟨C, hC0, -, hU, -, hV⟩ := theta_part_jets ha ha13 hOK hreg hG τ hτ
      exact ⟨C, hC0, hU, hV⟩)

end Work.FTS_StreamBdry.Inputs
