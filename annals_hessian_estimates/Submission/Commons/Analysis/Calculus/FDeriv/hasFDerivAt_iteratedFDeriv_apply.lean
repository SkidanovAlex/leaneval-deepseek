import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped Topology

namespace Commons.Analysis.Calculus.FDeriv

/-- The derivative of `y ↦ (iteratedFDeriv ℝ n u y) m` is obtained by currying the
`(n+1)`-st iterated derivative: the first variable is the direction of differentiation and
the remaining `n` variables are the fixed tuple `m`.  Equivalently, for `v : E`,
```
fderiv ℝ (fun y => (iteratedFDeriv ℝ n u y) m) x v = iteratedFDeriv ℝ (n+1) u x (v :: m).
```
-/
theorem hasFDerivAt_iteratedFDeriv_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} {s : Set E} {x : E} (hs : IsOpen s) (hx : x ∈ s) {n : ℕ}
    (hu : ContDiffOn ℝ (n + 1) u s) (m : Fin n → E) :
    HasFDerivAt (fun y => (iteratedFDeriv ℝ n u y) m)
      (((ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) ℝ) m).comp
        (ContinuousMultilinearMap.curryLeft (iteratedFDeriv ℝ (n + 1) u x))) x := by
  have hxmem : s ∈ 𝓝 x := hs.mem_nhds hx
  have huAt : ContDiffAt ℝ (n + 1) u x := hu.contDiffAt hxmem
  -- `iteratedFDeriv ℝ n u` is differentiable at `x`, being `C^1` there.
  have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ n u) x :=
    (huAt.iteratedFDeriv_right (i := n) (m := 1) (by
      exact le_of_eq (add_comm _ _))).differentiableAt one_ne_zero
  -- Applying a family of continuous multilinear maps to a constant.
  have h1 : HasFDerivAt (fun y => (iteratedFDeriv ℝ n u y) m)
      ((fderiv ℝ (iteratedFDeriv ℝ n u) x).flipMultilinear m) x :=
    hdiff.hasFDerivAt.continuousMultilinear_apply_const m
  -- The `n`-th iterated derivative's derivative is the curried `(n+1)`-st iterated derivative.
  have hfderiv : fderiv ℝ (iteratedFDeriv ℝ n u) x
      = ContinuousMultilinearMap.curryLeft (iteratedFDeriv ℝ (n + 1) u x) := by
    rw [fderiv_iteratedFDeriv]; rfl
  -- Flipping a curried map is the same as composing with the evaluation map.
  have hflip : ∀ (g : E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ),
      g.flipMultilinear m
        = ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) ℝ) m).comp g := by
    intro g
    ext v
    simp [ContinuousLinearMap.flipMultilinear_apply_apply]
  rw [hfderiv, hflip] at h1
  exact h1

end Commons.Analysis.Calculus.FDeriv