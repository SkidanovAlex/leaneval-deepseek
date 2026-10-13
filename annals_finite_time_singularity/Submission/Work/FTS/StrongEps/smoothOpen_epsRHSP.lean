import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.StrongEps.EpsWPContDiffOnQuad
import Submission.Work.FTS.StrongEps.PZeroAux.softClass_Pz
import Submission.Work.FTS.StrongEps.JepsSmoothOpen
import Submission.Work.FTS.StrongEps.smoothOpen_linPart
import Submission.Work.FTS.StrongEps.smoothOpen_dynRHS

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

theorem smoothOpen_epsRHSP {α ε T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam} {s : ℝ}
    (hs : s ∈ Set.Ioo 0 T) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε)
    (linc : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.FTS.StrongPersist.linPart α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s))) Work.FTS.StrongEps.Quad)
    (rhsc : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.FTS.Galerkin.dynRHS α
      (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g))
      (Work.FTS.StrongEps.JfamP ρ ε g) s)) Work.FTS.StrongEps.Quad) :
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s))
      Work.FTS.StrongEps.Quad := by
  -- `epsRHSP α ρ ε Φs E g s = P_z (J_ε (epsWP α ρ ε Φs E g s))`, and
  -- `P_z f = f − (L₁₂ f 0 / pzNorm) · bump` is a *constant* multiple of the fixed smooth
  -- profile `bump` away from `f`.  So the three ingredients are:
  --   (i) `epsWP` is `C^n` on the open quadrant (its two summands are, by hypothesis),
  --  (ii) `J_ε` preserves that smoothness for a smooth kernel and `ε > 0`,
  -- (iii) `bump` is `C^∞` (indeed everywhere).
  intro n
  -- (i) the pre-mollified right-hand side is `C^m` on the quadrant for every `m`
  have hW : ∀ m : ℕ, ContDiffOn ℝ m
      (Function.uncurry (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s))
      Work.FTS.StrongEps.Quad := by
    intro m
    have hEq : Function.uncurry (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)
        = fun p : ℝ × ℝ =>
            Function.uncurry (Work.FTS.StrongPersist.linPart α
              (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s)) p
            + Function.uncurry (Work.FTS.Galerkin.dynRHS α
              (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g))
              (Work.FTS.StrongEps.JfamP ρ ε g) s) p := by
      funext p
      simp only [Function.uncurry, Work.FTS.StrongEps.epsWP,
        Work.FTS.StrongPersist.dynLin_eq_linPart]
    rw [hEq]
    exact ContDiffOn.add (linc m) (rhsc m)
  -- (ii) the mollified pre-mollified right-hand side is `C^n` on the quadrant
  have hJ : ContDiffOn ℝ n
      (Function.uncurry (Work.FTS.StrongEps.Jeps ρ ε
        (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s))) Work.FTS.StrongEps.Quad :=
    Work.FTS.StrongEps.Jeps_contDiffOn ρ hρ hε
      (Work.FTS.StrongEps.locallyIntegrable_logPull_of_forall_contDiffOn hW) n
  -- (iii) the correction term is a constant multiple of the fixed smooth profile `bump`
  have hb : ContDiffOn ℝ n (fun p : ℝ × ℝ =>
      (Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε
          (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) 0 / Work.FTS.StrongEps.pzNorm)
        * Work.FTS.StrongEps.bump p.1 p.2) Work.FTS.StrongEps.Quad :=
    contDiffOn_const.mul ((Work.FTS.StrongEps.contDiff_bump n).contDiffOn)
  -- the uncurried projected right-hand side is the sum of the two
  have hmain : ContDiffOn ℝ n (fun p : ℝ × ℝ =>
      Function.uncurry (Work.FTS.StrongEps.Jeps ρ ε
          (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) p
        - (Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε
            (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) 0 / Work.FTS.StrongEps.pzNorm)
          * Work.FTS.StrongEps.bump p.1 p.2) Work.FTS.StrongEps.Quad :=
    hJ.sub hb
  refine hmain.congr (fun p hp => ?_)
  simp only [Function.uncurry, Work.FTS.StrongEps.Pz_apply, Work.FTS.StrongEps.epsRHSP]

end Work.FTS.StrongEps
