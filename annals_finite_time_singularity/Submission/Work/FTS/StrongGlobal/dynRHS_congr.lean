import Mathlib.Basic.Real.Basic
import Submission.Work.FTS.StrongGlobal.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongGlobal

/-- **`dynRHS` depends on a family only through its slice.**  With the canonical stream function
`PsiCan Φs EllSol`, the nonlinear right-hand side `dynRHS α Φ g τ` depends on `g` only through
`slice g τ`.

Proof: unfold `dynRHS`, `muDyn`, `lamDyn` and rewrite with the slice-congruences already proved in
`Submission/Work/FTS/StrongGlobal/Defs` (`Work.FTS.StrongGlobal.muDyn_congr`,
`Work.FTS.StrongGlobal.Ftau_congr`, `Work.FTS.StrongGlobal.slice_PsiCan_congr`, and the hypothesis
`h` itself). -/
theorem dynRHS_congr {α : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {EllSol : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g g' : Work.FTS.Galerkin.Fam}
    {τ : ℝ} (h : Work.FTS.Galerkin.slice g τ = Work.FTS.Galerkin.slice g' τ) :
    Work.FTS.Galerkin.dynRHS α (Work.FTS.Nonlin.PsiCan Φs EllSol g) g τ
      = Work.FTS.Galerkin.dynRHS α (Work.FTS.Nonlin.PsiCan Φs EllSol g') g' τ := by
  have hmu : Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs EllSol g) g τ
      = Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs EllSol g') g' τ :=
    muDyn_congr h
  simp only [Work.FTS.Galerkin.dynRHS, Work.FTS.Galerkin.lamDyn, hmu, Ftau_congr h,
    slice_PsiCan_congr h, h]

end Work.FTS.StrongGlobal
