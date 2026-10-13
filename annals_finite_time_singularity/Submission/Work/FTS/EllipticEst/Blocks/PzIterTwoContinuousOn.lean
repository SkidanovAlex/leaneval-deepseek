import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.CurrySmooth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Blocks

open scoped Topology

/-- `∂_z` lowers the order of differentiability by one: if `Function.uncurry G` is `C^{n+1}` on
the open set `U`, then `Function.uncurry (∂_z G)` is `C^n` there.

Indeed on `U` the `z`-partial is the Fréchet derivative in the direction `(1,0)`, which is `C^n`
by `ContDiffOn.fderiv_of_isOpen` followed by `ContDiffOn.clm_apply` with the constant direction
`(1,0)`. -/
theorem contDiffOn_uncurry_pz_succ {G : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {n : ℕ} (h : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (Function.uncurry G) U) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pz G)) U := by
  have hfd : ContDiffOn ℝ (n : WithTop ℕ∞) (fderiv ℝ (Function.uncurry G)) U :=
    h.fderiv_of_isOpen hU (by simp)
  have hcomp : ContDiffOn ℝ (n : WithTop ℕ∞)
      (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p (1, 0)) U :=
    hfd.clm_apply contDiffOn_const
  refine hcomp.congr ?_
  intro p hp
  exact Work.Spaces.pz_eq_fderiv
    ((h.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hp))

/-- The second `z`-partial `∂_z²V` is jointly continuous on any open set on which the
uncurried `V` is `C²`.  `pzIter 2 V z θ` is the second derivative of the one-variable slice
`z' ↦ V z' θ`, and it coincides on `U` with the second iterated Fréchet derivative of
`Function.uncurry V` evaluated on the constant direction `(1,0)`, which is continuous whenever
`Function.uncurry V` is `C²` on the open set `U`.

Suggested sorry-free route (avoid the still-`sorry` `DzAmgm.SliceIteratedDerivFDeriv`): first
prove that `pz G p.1 p.2 = fderiv ℝ (Function.uncurry G) p (1,0)` for every `p ∈ U` by
`Work.Spaces.pz_eq_fderiv` together with `ContDiffOn.differentiableOn` and
`IsOpen.mem_nhds`; then for `G` which is `C^{n+1}` on the open `U` show that
`Function.uncurry (pz G)` is `C^n` on `U` by `ContDiffOn.fderivWithin` (with
`hU.uniqueDiffOn`), `fderivWithin_of_isOpen` and `ContDiffOn.clm_apply contDiffOn_const`,
and apply this twice (`n = 1` then `n = 0`) to `V` (use `pzIter_succ`, `pzIter_zero` to
identify `pzIter 2 V` with `pz (pz V)`). -/
theorem PzIterTwoContinuousOn {V : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (h : ContDiffOn ℝ 2 (Function.uncurry V) U) :
    ContinuousOn (Function.uncurry (Work.Spaces.pzIter 2 V)) U := by
  have h1 : ContDiffOn ℝ (1 : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pz V)) U :=
    contDiffOn_uncurry_pz_succ hU (n := 1) h
  have h2 : ContDiffOn ℝ (0 : WithTop ℕ∞)
      (Function.uncurry (Work.Spaces.pz (Work.Spaces.pz V))) U :=
    contDiffOn_uncurry_pz_succ hU (n := 0) h1
  simpa [Work.Spaces.pzIter_succ] using h2.continuousOn_zero

end Work.FTS.EllipticEst.Blocks
