/-
# Clairaut / mixed partial derivatives, in Fréchet form

The target lemma `mixedPartialEq` identifies the iterated one-dimensional mixed partial
derivative `∂₁∂₂ H` of a `C²` function `H` on an open set `U ⊆ ℝ²` with the second Fréchet
derivative of `Function.uncurry H` evaluated on the pair of direction vectors `(1,0)`, `(0,1)`.

The proof (below, for a general `F : ℝ × ℝ → ℝ`, then specialised) is:

* the `y`-slice `y' ↦ F (x', y')` is the composition of `F` with the affine map
  `t ↦ (x', t)` whose derivative is `(0,1)`; the chain rule for `HasFDerivAt.comp_hasDerivAt`
  therefore gives `deriv (fun y' => F (x', y')) y = (fderiv ℝ F (x', y)) (0,1)` for every
  `x'` near `x` (all of which lie in `U`, which is open);
* consequently the `x`-derivative of the left-hand side is the `x`-derivative of
  `x' ↦ (fderiv ℝ F (x', y)) (0,1)`, i.e. of `G ∘ (t ↦ (t, y))` where
  `G p = (fderiv ℝ F p) (0,1)`;
* `G = ev_{(0,1)} ∘ (fderiv ℝ F)`, and `fderiv ℝ F` is differentiable at `(x,y)` because `F`
  is `C²`; the chain rule gives `fderiv ℝ G (x,y) = ev_{(0,1)} ∘ (fderiv ℝ (fderiv ℝ F) (x,y))`,
  and the derivative of `t ↦ (t, y)` at `x` is `(1,0)`.

Nothing here is specific to the paper; it is the calculus lemma the elliptic section needs.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology
open Filter

namespace Work.FTS.EllSol.EllPkgAux

/-- **Mixed partial derivative, general form.** For `F : ℝ × ℝ → ℝ` which is `C²` on an open
set `U` and `p = (x,y) ∈ U`, the derivative at `x` of the `y`-slice derivative
`x' ↦ deriv (fun y' => F (x',y')) y` equals the second Fréchet derivative of `F` at `(x,y)`
evaluated on `(1,0)` and then `(0,1)`. -/
theorem mixedPartialEq_uncurry {F : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} {x y : ℝ}
    (hU : IsOpen U) (hxy : (x, y) ∈ U) (hF : ContDiffOn ℝ 2 F U) :
    deriv (fun x' => deriv (fun y' => F (x', y')) y) x
      = (fderiv ℝ (fderiv ℝ F) (x, y) (1, 0)) (0, 1) := by
  have hUnhds : U ∈ 𝓝 (x, y) := hU.mem_nhds hxy
  -- `F` is differentiable on `U`, and the derivative is `C¹` there.
  have hFdiff : DifferentiableOn ℝ F U := hF.differentiableOn (by norm_num)
  have hdfF : ContDiffOn ℝ 1 (fderiv ℝ F) U := hF.fderiv_of_isOpen hU (by norm_num)
  have hdfFdiff : DifferentiableOn ℝ (fderiv ℝ F) U := hdfF.differentiableOn (by norm_num)
  -- the points `(x', y)` with `x'` near `x` all lie in `U`
  have hcont : ContinuousAt (fun x' : ℝ => (x', y)) x := by fun_prop
  have hmem : ∀ᶠ x' in 𝓝 x, (x', y) ∈ U := hcont.preimage_mem_nhds hUnhds
  -- the `y`-slice derivative
  have hslice : ∀ x' : ℝ, (x', y) ∈ U →
      deriv (fun y' => F (x', y')) y = (fderiv ℝ F (x', y)) (0, 1) := by
    intro x' hx'
    have hF' : HasFDerivAt F (fderiv ℝ F (x', y)) (x', y) :=
      DifferentiableOn.hasFDerivAt hFdiff (hU.mem_nhds hx')
    have hφ : HasDerivAt (fun t : ℝ => (x', t)) (0, 1) y :=
      (hasDerivAt_const y x').prodMk (hasDerivAt_id y)
    exact (hF'.comp_hasDerivAt y hφ).deriv
  have hgerm : (fun x' => deriv (fun y' => F (x', y')) y) =ᶠ[𝓝 x]
      (fun x' => (fderiv ℝ F (x', y)) (0, 1)) := by
    filter_upwards [hmem] with x' hx'
    exact hslice x' hx'
  -- the `x`-derivative of `p ↦ (fderiv ℝ F p) (0,1)` at `(x,y)`
  have hG : HasFDerivAt (fun p : ℝ × ℝ => (fderiv ℝ F p) (0, 1))
      ((ContinuousLinearMap.apply ℝ ℝ (0, 1)).comp (fderiv ℝ (fderiv ℝ F) (x, y))) (x, y) := by
    have hdF : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) (x, y)) (x, y) :=
      DifferentiableOn.hasFDerivAt hdfFdiff hUnhds
    have hev : HasFDerivAt (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (0, 1))
        (ContinuousLinearMap.apply ℝ ℝ (0, 1)) (fderiv ℝ F (x, y)) :=
      (ContinuousLinearMap.apply ℝ ℝ (0, 1)).hasFDerivAt
    have h2 := hev.comp (x, y) hdF
    simpa [Function.comp_def] using h2
  have hderiv : deriv (fun x' => (fderiv ℝ F (x', y)) (0, 1)) x
      = (fderiv ℝ (fderiv ℝ F) (x, y) (1, 0)) (0, 1) := by
    have hφ : HasDerivAt (fun t : ℝ => (t, y)) (1, 0) x :=
      (hasDerivAt_id x).prodMk (hasDerivAt_const x y)
    have h4 : HasDerivAt (fun x' => (fderiv ℝ F (x', y)) (0, 1))
        (((ContinuousLinearMap.apply ℝ ℝ (0, 1)).comp
          (fderiv ℝ (fderiv ℝ F) (x, y))) (1, 0)) x := by
      have h5 := hG.comp_hasDerivAt x hφ
      simpa [Function.comp_def] using h5
    rw [h4.deriv]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  rw [Filter.EventuallyEq.deriv_eq hgerm, hderiv]

theorem mixedPartialEq {H : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} {x y : ℝ}
    (hU : IsOpen U) (hxy : (x, y) ∈ U) (hH : ContDiffOn ℝ 2 (Function.uncurry H) U) :
    deriv (fun x' => deriv (fun y' => H x' y') y) x
      = (fderiv ℝ (fderiv ℝ (Function.uncurry H)) (x, y) (1, 0)) (0, 1) :=
  mixedPartialEq_uncurry hU hxy hH

end Work.FTS.EllSol.EllPkgAux
