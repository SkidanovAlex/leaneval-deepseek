import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.Lop_iter_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Blocks

/-- The second iterate of `L = sin(2θ) ∂_θ` on a smooth slice:
`L²u θ = sin(2θ)² · u''(θ) + 2 cos(2θ) · (L u θ)`, where `LopIter 1 u = L u` unfolds to
`fun θ => sin(2θ) * deriv u θ`.

Route: `LopIter 2 u θ = L (L u) θ`, and `L u = (fun θ => sin(2θ)) * deriv u`; apply the
pointwise Leibniz rule `Work.FTS.EllipticEst.Lop_iter_mul` with `f = fun θ => sin(2θ)`,
`g = deriv u` (both `C^∞` at `θ`: the second by `ContDiffAt.deriv` applied twice to `hu`),
then `L (deriv u) = sin(2θ) * deriv (deriv u)` and
`L (fun θ => sin(2θ)) θ = sin(2θ) * 2 cos(2θ)` (from `deriv (fun θ => sin (2θ)) = 2 cos (2θ)`).
Put the declaration in namespace `Work.FTS.EllipticEst.Blocks`. -/
theorem sf_LopIter_two {u : ℝ → ℝ} {θ : ℝ} (hu : ContDiffAt ℝ ⊤ u θ) :
    Work.FTS.EllipticEst.LopIter 2 u θ
      = (Real.sin (2 * θ)) ^ 2 * Work.FTS.EllipticEst.sliceV u θ
        + 2 * Real.cos (2 * θ) * Work.FTS.EllipticEst.LopIter 1 u θ := by
  -- `deriv u` is again smooth at `θ`, since `u` is analytic there.
  have hdu : ContDiffAt ℝ ⊤ (deriv u) θ := ContDiffAt.derivWithin (m := ⊤) hu (by simp)
  have hsin : ContDiffAt ℝ ⊤ (fun θ : ℝ => Real.sin (2 * θ)) θ := by fun_prop
  -- `L² u = L (L u)` and `L u = sin(2·) * deriv u`.
  have hF : Work.FTS.EllipticEst.LopIter 2 u θ
      = Work.FTS.EllipticEst.LopIter 1 ((fun θ : ℝ => Real.sin (2 * θ)) * deriv u) θ := by
    rw [Work.FTS.EllipticEst.LopIter_succ, Work.FTS.EllipticEst.LopIter_succ,
      Work.FTS.EllipticEst.LopIter_zero]
    rfl
  rw [hF, Work.FTS.EllipticEst.Lop_iter_mul hsin hdu]
  -- `deriv (fun s => sin (2s)) t = 2 cos (2t)`.
  have hd : ∀ t : ℝ, deriv (fun s : ℝ => Real.sin (2 * s)) t = 2 * Real.cos (2 * t) := by
    intro t
    simp [mul_comm]
  -- expand the two-term Leibniz sum and compute both derivatives
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, one_mul,
    tsub_zero, tsub_self,
    Work.FTS.EllipticEst.LopIter, Function.iterate_one, Function.iterate_zero_apply,
    Work.Spaces.Lop, Work.FTS.EllipticEst.sliceV, hd]
  ring

end Work.FTS.EllipticEst.Blocks
