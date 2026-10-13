import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadAZop
import Submission.Work.FTS.Nonlinear.Pieces.rowsN0Q
import Submission.Work.FTS.StrongPersist.H6Aux.DzdIter_mul_of_diff
import Submission.Work.FTS.StrongPersist.H6Aux.q0Sm_Corr
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.RadSAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX.RadBound

/-- **Differentiability of the `D_z`-iterates of `ampA α · L₁₂ f`.**

`ampA α z = 2z/(c(α)(1+z)²)` is a rational function, hence `C^5` on `(0,∞)`
(`E2pkg.contDiffOn_ampA_five`), so every `D_z`-iterate of it up to order `4` is differentiable
there (`E2pkg.differentiableAt_dzdIter_of_contDiffOn_general`).  With the hypothesis that the
iterates of `L₁₂ f` up to order `3` are differentiable on `(0,∞)`, the Leibniz rule for
`D_z = z ∂_z` (`E2pkg.differentiableAt_dzdIter_mul_of`, whose proof is the finite expansion
`Nonlinear.Pieces.dzdIter_mul_leibniz`) gives the differentiability of every iterate of the
product up to order `3`. -/
theorem diffDzd_ampA_mul_L12f_open (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (f : Work.FTS.Galerkin.Fn)
    (hL12diff : ∀ b : ℕ, b ≤ 3 → ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b (Work.Coercivity.L12f f)) z) :
    ∀ b : ℕ, b ≤ 3 → ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b
        (fun z : ℝ => Work.FTS.CoercivityFix.Transfer.ampA α z
          * Work.Coercivity.L12f f z)) z := by
  intro b hb z hz
  -- `ampA α` is `C^5` on `(0,∞)`
  have hA5 : ContDiffOn ℝ 5 (Work.FTS.CoercivityFix.Transfer.ampA α) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_ampA_five α
  -- hence each of its iterates up to order `b` is differentiable there
  have hAdiff : ∀ c ≤ b, ∀ z' ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter c
        (Work.FTS.CoercivityFix.Transfer.ampA α)) z' := by
    intro c hc z' hz'
    exact Work.FTS.CoercivityFix.Transfer.E2pkg.differentiableAt_dzdIter_of_contDiffOn_general
      (N := 5) (hu := hA5) (c := c) (by omega) hz'
  -- the iterates of `L₁₂ f` up to order `b ≤ 3` are differentiable by hypothesis
  have hLdiff : ∀ c ≤ b, ∀ z' ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f)) z' :=
    fun c hc z' hz' => hL12diff c (by omega) z' hz'
  exact Work.FTS.CoercivityFix.Transfer.E2pkg.differentiableAt_dzdIter_mul_of hAdiff hLdiff hz

end Work.FTS.StrongEps.EpsRLX.RadBound
