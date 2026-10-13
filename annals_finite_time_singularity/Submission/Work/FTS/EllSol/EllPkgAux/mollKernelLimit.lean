/-
# `Work.FTS.EllSol.EllPkgAux.mollKernelLimit`

The two-dimensional kernel-moment limit for the derivative of the normalised smooth bump
`K_t = sKerd t = deriv (sKer t)` (`Submission.Work.FTS.EllSol.PkgK5.K5c.MollDefs`): for a
`C²` function `H` on an open set `U ∋ (x,y)`, the double convolution against `K_t ⊗ K_t`
converges, as `t → 0⁺`, to the mixed second partial derivative `∂₁∂₂H x y` of `H`.

The analytic content (`mollKernel_aux`) is in `Submission.Work.FTS.EllSol.EllPkgAux.mollKernelAux`;
here the integral is rewritten in the uncurried form and the limit value is identified with
`deriv (fun x' => deriv (fun y' => H x' y') y) x` (`mixedPartialEq`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux
import Submission.Work.FTS.EllSol.EllPkgAux.mollKernelAux
import Submission.Work.FTS.EllSol.EllPkgAux.mixedPartialEq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

set_option maxHeartbeats 1000000

/-- **The kernel-moment limit**, for an arbitrary `C²` function `F` on an open set and the
*uncurried* form of the integral. -/
theorem mollKernelLimit {H : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} {x y : ℝ} (hU : IsOpen U)
    (hxy : (x, y) ∈ U) (hH : ContDiffOn ℝ 2 (Function.uncurry H) U) :
    Filter.Tendsto
      (fun t : ℝ => ∫ u : ℝ, ∫ v : ℝ,
        Work.FTS.EllSol.EllPkgAux.sKerd t u * Work.FTS.EllSol.EllPkgAux.sKerd t v *
          H (x - u) (y - v))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (deriv (fun x' => deriv (fun y' => H x' y') y) x)) := by
  have hred : (fun t : ℝ => ∫ u : ℝ, ∫ v : ℝ,
        Work.FTS.EllSol.EllPkgAux.sKerd t u * Work.FTS.EllSol.EllPkgAux.sKerd t v *
          H (x - u) (y - v))
      = fun t : ℝ => ∫ u : ℝ, sKerd t u *
          (∫ v : ℝ, sKerd t v * Function.uncurry H (x - u, y - v)) := by
    funext t
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show (∫ v : ℝ, sKerd t u * sKerd t v * H (x - u) (y - v))
      = sKerd t u * (∫ v : ℝ, sKerd t v * Function.uncurry H (x - u, y - v))
    have hpt : (fun v : ℝ => sKerd t u * sKerd t v * H (x - u) (y - v))
        = fun v : ℝ => sKerd t u * (sKerd t v * Function.uncurry H (x - u, y - v)) := by
      funext v; simp only [Function.uncurry_apply_pair]; ring
    rw [hpt, MeasureTheory.integral_const_mul]
  rw [hred, mixedPartialEq hU hxy hH]
  exact mollKernel_aux hU hxy hH

end Work.FTS.EllSol.EllPkgAux
