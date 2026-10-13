/-
# `RHS/sharp_N_diff` — the sharp Lipschitz bound of the elliptic correction `N`

The requested lemma, assembled from

* `SharpAux/Identity` (the pointwise telescoping identity of `N` along a difference),
* `SharpAux/WlInfTermsBound` and `SharpAux/HonestTermsBound` (the twenty term bounds),
* `SharpAux/Main` (`Sharp.sharp_N_diff_asm`, the assembly).
-/
import Mathlib.Basic.Real.Basic
import Submission.Work.FTS.GalFields.Defs
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.GalFields.RHS.SharpAux.Main
import Submission.Work.FTS.GalFields.RHS.SharpAux.WlInfTermsBound
import Submission.Work.FTS.GalFields.RHS.SharpAux.HonestTermsBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalFields.RHS

theorem sharp_N_diff {α α₂ Ci Ct Ce Cs : ℝ}
    {IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {EllSol : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hell : ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.Nonlin.GalClass α g →
      Work.FTS.VocabO.EllPkgGo α Ce g (EllSol g))
    (hEllSub : ∀ g g' : Work.FTS.Galerkin.Fn,
      EllSol (fun z θ => g z θ - g' z θ) = fun z θ => EllSol g z θ - EllSol g' z θ)
    (hα : 0 < α) (hαα₂ : α ≤ α₂) :
    ∃ K : ℝ, 0 < K ∧ ∀ g g' h : Work.FTS.Galerkin.Fn,
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.GalClass α g' →
      Work.FTS.Nonlin.GalClass α h →
      (∀ z θ, h z θ = g z θ - g' z θ) → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
          Work.Construction.N α (Work.Construction.Ftot α g)
              (fun z θ => Φs z θ + EllSol g z θ) z θ
            - Work.Construction.N α (Work.Construction.Ftot α g')
              (fun z θ => Φs z θ + EllSol g' z θ) z θ) ∧
      Work.Spaces.HkMem α 4 (fun z θ =>
          Work.Construction.N α (Work.Construction.Ftot α g)
              (fun z θ => Φs z θ + EllSol g z θ) z θ
            - Work.Construction.N α (Work.Construction.Ftot α g')
              (fun z θ => Φs z θ + EllSol g' z θ) z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ =>
          Work.Construction.N α (Work.Construction.Ftot α g)
              (fun z θ => Φs z θ + EllSol g z θ) z θ
            - Work.Construction.N α (Work.Construction.Ftot α g')
              (fun z θ => Φs z θ + EllSol g' z θ) z θ)
        ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
            * Work.FTS.GalFields.Xn5 α h ∧
      |Work.Construction.L12
          (Work.Construction.N α (Work.Construction.Ftot α g)
            (fun z θ => Φs z θ + EllSol g z θ)) 0
        - Work.Construction.L12
          (Work.Construction.N α (Work.Construction.Ftot α g')
            (fun z θ => Φs z θ + EllSol g' z θ)) 0|
        ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
            * Work.FTS.GalFields.Xn5 α h :=
  Sharp.sharp_N_diff_asm hN hE hstar hell hEllSub hα hαα₂
    (SharpAux.WlInfTermsBound hN hstar hell hα hαα₂)
    (SharpAux.HonestTermsBound hN hstar hell hα hαα₂)

end Work.FTS.GalFields.RHS
