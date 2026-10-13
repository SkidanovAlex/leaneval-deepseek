import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.EpsODE
-- NOTE: `Submission.Work.FTS.StrongEps.Gdot` is deliberately *not* imported here: it declares
-- `Work.FTS.StrongEps.epsRHSu` (the mollified profile `J_ε (epsW …)`), while
-- `GlueParts/Basic.lean` declares `Work.FTS.StrongEps.epsRHSu` as the *unmollified* profile
-- `𝓛 + 𝓡`; the two names collide and Lean refuses to import both.  Nothing in the proof below
-- needs `Gdot`.
import Submission.Work.FTS.StrongEps.GlueParts.Basic
import Submission.Work.FTS.StrongEps.GlueParts.FirstStep
import Submission.Work.FTS.StrongEps.GlueParts.SolGlue
import Submission.Work.FTS.StrongEps.GlueParts.RegGlue
import Submission.Work.FTS.StrongEps.GlueParts.Induction

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

theorem EpsGlue {α ε T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn}
    {M : ℝ} (hT : 0 < T) (hM : 0 ≤ M)
    (hstep : ∀ M' : ℝ, 0 ≤ M' → ∃ δ : ℝ, 0 < δ ∧ ∀ h₀ : Work.FTS.Galerkin.Fn,
      Work.FTS.StrongEps.EpsDatum α ρ ε h₀ →
      Work.FTS.StrongGlobal.Xn6 α h₀ ≤ M' →
      ∃ h : Work.FTS.Galerkin.Fam, Work.FTS.StrongEps.IsEpsSol α ρ ε δ Φs E h₀ h ∧
        Work.FTS.StrongEps.EpsReg α ρ ε δ h ∧
        ∀ τ ∈ Set.Icc (0 : ℝ) δ, Work.FTS.StrongGlobal.Xn6 α (Work.FTS.Galerkin.slice h τ) ≤ 2 * M' + 1)
    (hd : Work.FTS.StrongEps.EpsDatum α ρ ε g₀)
    (hAp : Work.FTS.StrongEps.EpsAprioriBddH α ρ ε T Φs E g₀ M) :
    ∃ g : Work.FTS.Galerkin.Fam, Work.FTS.StrongEps.IsEpsSol α ρ ε T Φs E g₀ g ∧
      Work.FTS.StrongEps.EpsReg α ρ ε T g ∧
      ∀ τ ∈ Set.Icc (0 : ℝ) T, Work.FTS.StrongGlobal.Xn6 α (Work.FTS.Galerkin.slice g τ) ≤ M :=
  EpsGlue_of_glue hT hM hd hstep hAp
    (fun t δ G H ht hδ hG hH => GlueParts.SolGlue ht hδ hG hH)
    (fun t δ G H R ht hδ hG hH hval hderG hderH =>
      GlueParts.RegGlue (Φs := Φs) (E := E) ht hδ hG hH hval hderG hderH)
    (GlueParts.FirstStep (Φs := Φs) (E := E) hT hM hstep hd hAp)

end Work.FTS.StrongEps
