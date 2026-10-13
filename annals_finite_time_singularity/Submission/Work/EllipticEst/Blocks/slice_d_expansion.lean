import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.EllipticEst.Blocks.SliceDBook
import Submission.Work.FTS.EllipticEst.Lop_iter_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Blocks

/-- **The Leibniz expansion of `L^i (∂_θ u)`.**  Put this declaration in namespace `Work.FTS.EllipticEst.Blocks` (i.e. between `namespace Work.FTS.EllipticEst.Blocks` and `end Work.FTS.EllipticEst.Blocks`), in the file `Submission/Work/FTS/EllipticEst/Blocks/slice_d_expansion.lean` (module `Submission.Work.FTS.EllipticEst.Blocks.slice_d_expansion`).

Imports: `Mathlib`, `Submission.Work.FTS.EllipticEst.Blocks.SliceDBook` (which provides `Work.FTS.EllipticEst.Blocks.sliceV_contDiffAt`), `Submission.Work.FTS.EllipticEst.Lop_iter_mul` (the iterated Leibniz rule for `LopIter = (Work.Spaces.Lop)^[·]`, `Lop u θ = sin(2θ) * u'(θ)`).

Route: `LopIter 1 (deriv u) θ = sin(2θ) * sliceV u θ` (`sliceV u = deriv (deriv u)`), so by `Function.iterate_succ_apply'` one has `LopIter (j+1) (deriv u) = LopIter j (fun θ => sin(2θ) * sliceV u θ)`; apply `Work.FTS.EllipticEst.Lop_iter_mul` (with `f = fun θ => Real.sin (2*θ)`, `g = sliceV u`) and use `sliceV_contDiffAt` for the `ContDiffAt` hypothesis on `sliceV u` (the one on `sin (2θ)` is `by fun_prop`). -/
theorem slice_d_expansion {u : ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SliceSmooth u) (j : ℕ)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.EllipticEst.LopIter (j + 1) (deriv u) θ =
      ∑ a ∈ Finset.range (j + 1),
        (j.choose a : ℝ) * Work.FTS.EllipticEst.LopIter a (fun θ : ℝ => Real.sin (2 * θ)) θ
          * Work.FTS.EllipticEst.LopIter (j - a) (Work.FTS.EllipticEst.sliceV u) θ := by
  -- `LopIter (j+1) (deriv u) = LopIter j (sin(2·) * sliceV u)`, since
  -- `Lop (deriv u) θ = sin(2θ) * deriv (deriv u) θ = sin(2θ) * sliceV u θ`.
  have hstep : Work.FTS.EllipticEst.LopIter (j + 1) (deriv u)
      = Work.FTS.EllipticEst.LopIter j
          (fun θ : ℝ => Real.sin (2 * θ) * Work.FTS.EllipticEst.sliceV u θ) := by
    rw [Work.FTS.EllipticEst.LopIter, Function.iterate_succ_apply]
    rfl
  rw [hstep]
  -- the iterated Leibniz rule for the product `sin(2·) * sliceV u`
  exact Work.FTS.EllipticEst.Lop_iter_mul (f := fun θ : ℝ => Real.sin (2 * θ))
    (g := Work.FTS.EllipticEst.sliceV u) (i := j) (by fun_prop)
    (Work.FTS.EllipticEst.Blocks.sliceV_contDiffAt hsm hθ)

end Work.EllipticEst.Blocks
