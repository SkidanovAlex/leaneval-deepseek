import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology

namespace Commons.Analysis.Convex

open Set

/-- **Subgradient inequality for a convex function.** If `f : E → ℝ` is convex on all of `E`
and differentiable at `x`, then `fderiv ℝ f x v ≤ f (x + v) - f x` for every `v`.

Proof: the function `g t = f (x + t • v)` is convex on `ℝ` (precomposition with the affine map
`t ↦ x + t • v`), differentiable at `0` with `deriv g 0 = fderiv ℝ f x v`, and the 1-dimensional
secant bound `ConvexOn.deriv_le_slope` gives `deriv g 0 ≤ slope g 0 1 = g 1 - g 0`. -/
theorem fderiv_le_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (x : E) (hx : DifferentiableAt ℝ f x) (v : E) :
    fderiv ℝ f x v ≤ f (x + v) - f x := by
  -- The restriction of `f` to the affine line `t ↦ x + t • v`.
  let φ : ℝ → E := fun t => x + t • v
  let g : ℝ → ℝ := fun t => f (φ t)
  -- `g` is convex, as the composition of a convex function with an affine map.
  have hgconv : ConvexOn ℝ Set.univ g := by
    have h := hf.comp_affineMap (AffineMap.lineMap x (x + v))
    have heq : (f ∘ ⇑(AffineMap.lineMap x (x + v))) = g := by
      funext s; simp [g, φ, AffineMap.lineMap_apply, add_comm]
    rwa [Set.preimage_univ, heq] at h
  -- The affine line map has derivative `v` at `0`.
  have hφd : HasDerivAt φ v 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t • v) v 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
    simpa [φ] using h1.const_add x
  -- Chain rule: `g` is differentiable at `0` with `deriv g 0 = fderiv ℝ f x v`.
  have hcomp : HasDerivAt (f ∘ φ) (fderiv ℝ f x v) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hx.hasFDerivAt hφd (by simp [φ])
  have hgd : DifferentiableAt ℝ g 0 := hcomp.differentiableAt
  have hderiv : deriv g 0 = fderiv ℝ f x v := hcomp.deriv
  -- One-dimensional secant bound for the convex function `g` on `[0,1]`.
  have h := hgconv.deriv_le_slope (Set.mem_univ 0) (Set.mem_univ 1) (by norm_num) hgd
  rw [slope_def_field] at h
  rw [hderiv] at h
  rw [sub_zero, div_one] at h
  simpa [g, φ] using h

end Commons.Analysis.Convex