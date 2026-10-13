import Mathlib.Basic.Real.Basic
import Submission.Work.FTS.GalFields.Defs
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.Nonlinear.Open.Main
import Submission.Work.FTS.GalFields.RHS.HkSum
import Submission.Work.FTS.GalFields.Norm.Basic
import Submission.Work.FTS.GalFields.RHS.SharpAux.Main
import Submission.Work.FTS.GalFields.RHS.SharpAux.HonestTermsBound
import Submission.Work.FTS.GalFields.RHS.SharpMod.N_L12_WlInf

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalFields.RHS.SharpMod

theorem N_L12_diff {α α₂ Ci Ct Ce Cs : ℝ}
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
      |Work.Construction.L12
          (Work.Construction.N α (Work.Construction.Ftot α g)
            (fun z θ => Φs z θ + EllSol g z θ)) 0
        - Work.Construction.L12
          (Work.Construction.N α (Work.Construction.Ftot α g')
            (fun z θ => Φs z θ + EllSol g' z θ)) 0|
        ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
            * Work.FTS.GalFields.Xn5 α h := by
  -- `Sharp.sharp_N_diff_asm` (`SharpAux/Main`) is the master assembly: it turns the two
  -- twenty-term-bound bundles of `SharpAux/Defs` (the `𝒲^{4,∞}`-priced half and the `ℋ⁴`-honest
  -- half) into the four clauses of `sharp_N_diff`.  The first bundle is the proved
  -- `SharpMod.N_L12_WlInf`; the second is `SharpAux.HonestTermsBound`.  Keeping the last
  -- («`L₁₂` at `z = 0`») clause gives exactly the statement requested here.
  obtain ⟨K, hKpos, hbd⟩ := Work.FTS.GalFields.RHS.Sharp.sharp_N_diff_asm hN hE hstar hell hEllSub
    hα hαα₂ (N_L12_WlInf hN hstar hell hα hαα₂)
    (Work.FTS.GalFields.RHS.SharpAux.HonestTermsBound hN hstar hell hα hαα₂)
  exact ⟨K, hKpos, fun g g' h hg hg' hh hdiff hα1 =>
    (hbd g g' h hg hg' hh hdiff hα1).2.2.2⟩

end Work.FTS.GalFields.RHS.SharpMod
