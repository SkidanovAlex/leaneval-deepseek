import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.EpsStructP
import Submission.Work.FTS.StrongEps.EpsGlue
import Submission.Work.FTS.StrongEps.StrongEpsP.Defs
import Submission.Work.FTS.StrongEps.StrongEpsP.FirstStepP
import Submission.Work.FTS.StrongEps.StrongEpsP.SolGlueP
import Submission.Work.FTS.StrongEps.StrongEpsP.RegGlueP
import Submission.Work.FTS.StrongEps.StrongEpsP.EpsGlue_of_glueP

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

theorem EpsGlueP {α ε T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn} {M : ℝ}
    (hT : 0 < T) (hM : 0 ≤ M)
    (hstep : ∀ M' : ℝ, 0 ≤ M' → ∃ δ : ℝ, 0 < δ ∧ ∀ h₀ : Work.FTS.Galerkin.Fn,
      Work.FTS.StrongEps.EpsDatumP α ρ ε h₀ →
      Work.FTS.StrongGlobal.Xn6 α h₀ ≤ M' →
      ∃ h : Work.FTS.Galerkin.Fam, Work.FTS.StrongEps.IsEpsSolP α ρ ε δ Φs E h₀ h ∧
        Work.FTS.StrongEps.EpsRegP α ρ ε δ h ∧
        ∀ τ ∈ Set.Icc (0 : ℝ) δ,
          Work.FTS.StrongGlobal.Xn6 α (Work.FTS.Galerkin.slice h τ) ≤ 2 * M' + 1)
    (hd : Work.FTS.StrongEps.EpsDatumP α ρ ε g₀)
    (hAp : Work.FTS.StrongEps.EpsAprioriBddHP α ρ ε T Φs E g₀ M) :
    ∃ g : Work.FTS.Galerkin.Fam, Work.FTS.StrongEps.IsEpsSolP α ρ ε T Φs E g₀ g ∧
      Work.FTS.StrongEps.EpsRegP α ρ ε T g ∧
      ∀ τ ∈ Set.Icc (0 : ℝ) T, Work.FTS.StrongGlobal.Xn6 α (Work.FTS.Galerkin.slice g τ) ≤ M :=
  -- The continuation for the `P₀`-corrected scheme is the same restart-and-concatenate induction
  -- as for the unprojected one: the projected scheme's right-hand side is slice-determined
  -- (`StrongEpsP.epsRHSP_congr`), the two junction glues are `SolGlueP`/`RegGlueP`, and the
  -- bootstrap value is `FirstStepP`.
  StrongEpsP.EpsGlue_of_glueP hT hM hd hstep hAp
    (fun t δ G H ht hδ hG hH => StrongEpsP.SolGlueP ht hδ hG hH)
    (fun t δ G H R ht hδ hG hH hval hderG hderH =>
      StrongEpsP.RegGlueP (Φs := Φs) (E := E) ht hδ hG hH hval hderG hderH)
    (StrongEpsP.FirstStepP (Φs := Φs) (E := E) hT hM hstep hd hAp)

end Work.FTS.StrongEps
