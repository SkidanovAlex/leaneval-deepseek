import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.ThetaOuter_add_int
import Submission.Work.Cusp.wOf_add

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.Cusp

open scoped Real InnerProductSpace

/-- `cuspY` is additive in its second argument: `cuspY v y = y 0 • λ₂ + y 1 • λ₃`. -/
theorem cuspY_add (v : Fin 5) (y y' : E2) : cuspY v (y + y') = cuspY v y + cuspY v y' := by
  ext i
  fin_cases i <;> simp [cuspY] <;> ring

/-- The radial coordinate `radial v p y` depends on `y` only through the ceiling `β`, which is
invariant under the lattice shift `ofInt2 m`; so it is invariant under `y ↦ y + ofInt2 m`. -/
theorem radial_add_int (v : Fin 5) (p y : E2) (m : Fin 2 → ℤ) :
    radial v p (y + ofInt2 m) = radial v p y := by
  rw [radial, radial, collarS_add_int v p y m]

/-- The angle coordinate of the core chart shifts by the phase
`2π⟪cuspY v (ofInt2 m), σ_v⟫/‖σ_v‖²` under `y ↦ y + ofInt2 m`. -/
theorem thetaAng_add_int (v : Fin 5) (p y : E2) (m : Fin 2 → ℤ) :
    thetaAng v p (y + ofInt2 m) =
      thetaAng v p y + 2 * π * inner ℝ (cuspY v (ofInt2 m)) (slope v) / ‖slope v‖ ^ 2 := by
  rw [thetaAng, thetaAng, cuspY_add, inner_add_left]
  ring

theorem ThetaCore_add_int (v : Fin 5) (p y : E2) (m : Fin 2 → ℤ) :
    ThetaCore v p (y + ofInt2 m) = !₂[
      (ThetaCore v p y) 0 * Real.cos (2 * π * inner ℝ (cuspY v (ofInt2 m)) (slope v) / ‖slope v‖ ^ 2) -
        (ThetaCore v p y) 1 * Real.sin (2 * π * inner ℝ (cuspY v (ofInt2 m)) (slope v) / ‖slope v‖ ^ 2),
      (ThetaCore v p y) 0 * Real.sin (2 * π * inner ℝ (cuspY v (ofInt2 m)) (slope v) / ‖slope v‖ ^ 2) +
        (ThetaCore v p y) 1 * Real.cos (2 * π * inner ℝ (cuspY v (ofInt2 m)) (slope v) / ‖slope v‖ ^ 2),
      (ThetaCore v p y) 2 + (wOf v (ofInt2 m)) 0,
      (ThetaCore v p y) 3 + (wOf v (ofInt2 m)) 1] := by
  have hr := radial_add_int v p y m
  have hθ := thetaAng_add_int v p y m
  have hw := wOf_add v y (ofInt2 m)
  ext i
  fin_cases i <;> simp [ThetaCore, hr, hθ, hw, Real.cos_add, Real.sin_add] <;> ring

end Work.Cusp
