import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongPersist.Vocab
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

theorem EpsWPContDiffOnQuad {α ε T : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hlinc : ∀ τ ∈ Set.Ioo (0 : ℝ) T, ∀ n : ℕ, ContDiffOn ℝ n
      (Function.uncurry (Work.FTS.StrongPersist.linPart α
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)))
      Work.FTS.EllipticEst.Q0)
    (hrhsc : ∀ τ ∈ Set.Ioo (0 : ℝ) T, ∀ n : ℕ, ContDiffOn ℝ n
      (Function.uncurry (Work.FTS.Galerkin.dynRHS α
        (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g))
        (Work.FTS.StrongEps.JfamP ρ ε g) τ))
      Work.FTS.EllipticEst.Q0)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T) :
    ∀ n : ℕ, ContDiffOn ℝ n
      (Function.uncurry (Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ))
      Work.FTS.StrongEps.Quad := by
  -- `epsWP α ρ ε Φs E g τ` is, by definition, the *sum* of the two functions whose joint
  -- smoothness on the quadrant is assumed:
  -- `fun z θ => dynLin α (JfamP ρ ε g) τ z θ + dynRHS α (PsiCan Φs E (JfamP ρ ε g)) (JfamP ρ ε g) τ z θ`.
  -- Moreover `dynLin α (JfamP ρ ε g) τ = linPart α (slice (JfamP ρ ε g) τ)` holds by `rfl`
  -- (`Work.FTS.Galerkin.dynLin_eq_linPart`), and the two sets agree definitionally:
  -- `Quad = Set.Ioi 0 ×ˢ Set.Ioo 0 (π/2) = Q0`.  Hence the two hypotheses give the two
  -- `ContDiffOn` facts for the summands, and `ContDiffOn.add` closes the goal.
  intro n
  exact ContDiffOn.add (hlinc τ hτ n) (hrhsc τ hτ n)

end Work.FTS.StrongEps
