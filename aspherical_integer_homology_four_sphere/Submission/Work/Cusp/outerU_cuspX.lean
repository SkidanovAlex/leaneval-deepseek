import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

open scoped Real InnerProductSpace

/-- Evaluation of the inner product of two explicit vectors of `E3 = ℝ³` in their coordinates. -/
lemma innerE3 (a b c d e f : ℝ) :
    inner ℝ (!₂[a, b, c] : E3) (!₂[d, e, f] : E3) = a * d + b * e + c * f := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, Fin.sum_univ_three]
  simp
  ring

/-- The squared norm of an explicit vector of `E3 = ℝ³` in its coordinates. -/
lemma normSqE3 (a b c : ℝ) : ‖(!₂[a, b, c] : E3)‖ ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_three]
  simp [Real.norm_eq_abs, sq_abs]

/-- **`outerU` inverts the cusp-coordinate map `cuspX` along the first coordinate.**  Since
`cuspX v s y = s • σ_v + y₂ λ₂ + y₃ λ₃` with `σ_v = κ_{v,1} + b_v κ_{v,2} + c_v κ_{v,3}` and the
`κ_{v,i}` are pairwise orthogonal, the `κ_{v,1}`-coefficient of `cuspX v s y` is exactly `s`. -/
theorem outerU_cuspX (v : Fin 5) (s : ℝ) (y : E2) : outerU v (cuspX v s y) = s := by
  fin_cases v <;>
    simp only [outerU, cuspX, cuspY, kappaCoord, slope, kv, lam2, lam3, kappa, slopeB, slopeC] <;>
    simp [inner_add_left, inner_smul_left] <;>
    simp only [normSqE3, innerE3] <;>
    ring

end Work.Cusp
