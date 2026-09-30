import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.beta_add_int

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- **`σ_v` is an integer vector**: `σ_v = κ_{v,1} + b_v κ_{v,2} + c_v κ_{v,3}` and both `b_v` and
`c_v` are integers (`slopeB`, `slopeC` are `ℤ`-valued), while the `κ_{v,i}` are integer vectors, so
`σ_v = ofInt3 n` for `n j = κ_{v,1}(j) + b_v κ_{v,2}(j) + c_v κ_{v,3}(j)`. -/
private theorem slope_eq_ofInt3 (v : Fin 5) :
    slope v = ofInt3 (fun j => kappa v 0 j + slopeB v * kappa v 1 j + slopeC v * kappa v 2 j) := by
  apply PiLp.ext
  intro j
  fin_cases j <;> simp [Work.Cusp.slope, kv, ofInt3, PiLp.add_apply, PiLp.smul_apply]

/-- **The slope `σ_v` is a period of the ceiling `β`.**  `σ_v = ofInt3 n` is an integer vector
(`slope_eq_ofInt3`), and `β` is invariant under integer translations (`beta_add_int`), so it is
invariant under any real multiple of `σ_v` as well.  Note that the multiple `m` ranges over the
integers: for non-integral multiples `σ_v` would generally not return to the same cube. -/
theorem beta_add_smul_slope (v : Fin 5) (x : E3) (m : ℤ) : beta (x + (m : ℝ) • slope v) = beta x := by
  have h2 : (m : ℝ) • slope v
      = ofInt3 (fun j => m * (kappa v 0 j + slopeB v * kappa v 1 j + slopeC v * kappa v 2 j)) := by
    rw [slope_eq_ofInt3 v]
    apply PiLp.ext
    intro j
    rw [PiLp.smul_apply, ofInt3_apply, ofInt3_apply]
    push_cast
    ring
  rw [h2]
  exact beta_add_int x _

end Work.Cusp
