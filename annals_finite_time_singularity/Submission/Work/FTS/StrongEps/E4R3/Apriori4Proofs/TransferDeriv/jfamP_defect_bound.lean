import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.Defs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.IP4_transfer_deriv
import Submission.Work.FTS.StrongEps.EpsE4Thr.HnegCore
import Submission.Work.FTS.StrongEps.EpsE4Thr.HkNorm_epsRHSP_le
import Submission.Work.FTS.StrongEps.epsWP_hkMem4_bnd
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenBarrier
import Submission.Work.FTS.StrongEps.JfamP_norm
import Submission.Work.FTS.StrongEps.L12_Jeps_sub_le4
import Submission.Work.FTS.StrongEps.EpsZeroMode
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.JfamPDefectAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

theorem jfamP_defect_bound {ρ : ℝ × ℝ → ℝ} (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ)
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α₂ cc clo Cup Ccs CcN : ℝ}
    (hU : Work.FTS.StrongEps.EpsE4Thr.UnifIPO
      (Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'') α₂ cc clo Cup Ccs)
    {Ce Cs : ℝ}
    (hN4 : ∀ α ∈ Set.Ioc 0 α₂, ∀ {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α g → Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α g →
      Work.FTS.VocabO2.StarPkgo2 α Cs Φs → Work.FTS.VocabO.EllPkgGo α Ce g Φg →
      Work.FTS.Nonlin.Xn α g ≤ α ^ (7 / 4 : ℝ) →
      |Work.FTS.Apriori.rhsPair (Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'')
        α g (fun z θ => Φs z θ + Φg z θ)|
        ≤ CcN * Work.FTS.Nonlin.Pbd α (Work.FTS.Nonlin.Xn α g))
    {α C₀ M : ℝ} (hα : α ∈ Set.Ioc 0 α₂) (hα1 : α ≤ 1) (hC₀ : 0 < C₀) (hM : 0 ≤ M)
    (hsmall : C₀ * α ^ (1 / 4 : ℝ) ≤ 1) :
    ∃ Kc : ℝ, 0 ≤ Kc ∧
      ∀ {T τ ε : ℝ} {Φs : Work.FTS.Galerkin.Fn}
        {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn}
        {g : Work.FTS.Galerkin.Fam},
        0 < T → τ ∈ Set.Ioo 0 T → ε ∈ Set.Ioc 0 1 →
        Work.FTS.StrongEps.IsEpsSolP α ρ ε T Φs E g₀ g →
        Work.FTS.StrongEps.EpsRegP α ρ ε T g →
        (∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
          Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u)) →
        Work.FTS.VocabO2.StarPkgo2 α Cs Φs → Work.FTS.StrongEps.MuLamOK α C₀ Φs E →
        (∀ s ∈ Set.Icc 0 T, Work.FTS.StrongGlobal.Xn6 α (Work.FTS.Galerkin.slice g s) ≤ M) →
        (∀ t ∈ Set.Icc 0 τ, Work.FTS.Nonlin.Xn α
          (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) t) ≤ C₀ * α ^ 2) →
        |Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
            (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε
              (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ)))
            (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)
          - Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
              (Work.FTS.Galerkin.dynLin α (Work.FTS.StrongEps.JfamP ρ ε g) τ
                + Work.FTS.Galerkin.dynRHS α
                    (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g))
                    (Work.FTS.StrongEps.JfamP ρ ε g) τ)
              (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)|
          ≤ Kc * ε :=
  jfamP_defect_bound_aux c₁ c₂ c₁' c₂' c₁'' c₂'' hρ hU hN4 hα hα1 hC₀ hM hsmall

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
