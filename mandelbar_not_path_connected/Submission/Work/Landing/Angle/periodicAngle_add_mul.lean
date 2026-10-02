import Mathlib
import Submission.Work.Landing.Angles

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Landing.Angle

open Function

/-- If `x` is fixed by the `n`-fold iterate of `f`, then it is fixed by the `m * n`-fold
iterate, for every `m`. -/
theorem iterate_mul_eq_self {α : Type*} {f : α → α} {x : α} {n : ℕ} (h : f^[n] x = x) (m : ℕ) :
    f^[m * n] x = x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul, Function.iterate_add_apply, h, ih]

/-- The iterates of a periodic angle only depend on the residue of the exponent modulo the
period: if `angDouble^[n] θ = θ` then `angDouble^[m * n + r] θ = angDouble^[r] θ`. -/
theorem periodicAngle_add_mul {θ : ℝ} {n : ℕ} (h : Work.Landing.PeriodicAngle θ n)
    (m r : ℕ) : (Work.Landing.angDouble)^[m * n + r] θ = (Work.Landing.angDouble)^[r] θ := by
  rw [Nat.add_comm (m * n) r, Function.iterate_add_apply, iterate_mul_eq_self h m]

end Work.Landing.Angle
