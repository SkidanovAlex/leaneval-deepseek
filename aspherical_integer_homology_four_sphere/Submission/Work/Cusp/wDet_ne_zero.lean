import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Non-vanishing of the `w`-determinant `wDet v`

`wDet v` is the determinant of the `2 × 2` matrix `G = (⟪λ_i, e_j⟫)` expressing the two torus
directions `λ₂ = κ_{v,2}`, `λ₃ = κ_{v,3}` in the orthonormal frame `(frame2 v, frame3 v)` of the
plane `σ_v^⊥`.  It is nonzero exactly when `(σ_v, λ₂, λ₃)` is a basis of `ℝ³`, i.e. when the
`w`-coordinates of the cusp coordinate `y = y₂λ₂ + y₃λ₃` determine `y`; this is what makes the
inverse `invY v` well defined.

Everything here is a finite computation from the data tables `Data.kappa`, `Data.slopeB`,
`Data.slopeC`: the identity
`wDet v = ⟪λ₂, e₂⟫ * ⟪λ₃, e₃⟫ - ⟪λ₃, e₂⟫ * ⟪λ₂, e₃⟫`
reduces, using the orthogonality of `κ_{v,1}, κ_{v,2}, κ_{v,3}` and `slopeC v = 0`, to
`wDet v = ‖frame2aux v‖ * ‖λ₃ v‖`, a product of two positive numbers.  We evaluate the finite case
split with `norm_num`.
-/

open scoped Real InnerProductSpace

namespace Work.Cusp

theorem wDet_ne_zero (v : Fin 5) : wDet v ≠ 0 := by
  -- `wDet`, `frame2`, `frame3`, `frame2aux`, `slope` are all explicit from the data tables, so
  -- the whole statement is a finite computation in `ℝ³`.
  fin_cases v <;>
    simp only [wDet, lam2, lam3, frame2, frame3, frame2aux, kv, kappa, slope, slopeB, slopeC,
      PiLp.inner_apply, Fin.sum_univ_three, EuclideanSpace.real_norm_sq_eq,
      Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] <;>
    norm_num <;>
    intro h
  -- What remains is `frame2aux v ≠ 0`; each case is settled by exhibiting a nonzero coordinate.
  all_goals
    have h1 := (WithLp.ext_iff 2).mp h
    simp only [WithLp.ofLp_sub, WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_zero] at h1
    have e0 := congrFun h1 0
    have e1 := congrFun h1 1
    have e2 := congrFun h1 2
    try norm_num at e0
    try norm_num at e1
    try norm_num at e2

end Work.Cusp
