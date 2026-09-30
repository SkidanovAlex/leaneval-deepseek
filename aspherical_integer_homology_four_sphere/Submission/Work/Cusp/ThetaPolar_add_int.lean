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

/-- **The polar chart is equivariant under integer translations of the torus coordinate.**

`ThetaPolar v p y = (r, θ, w₁, w₂)` with `r = radial v p y`, `θ = thetaAng v p y` and
`w = wOf v y`.  Translating `y` by the integer vector `ofInt2 m`:

* leaves `r` unchanged, since the cusp coordinate `x = u(p)σ_v + y₂λ₂ + y₃λ₃` moves by the lattice
  vector `m₀λ₂ + m₁λ₃` and `β` is `ℤ³`-periodic;
* shifts the angle by the phase `2π⟪cuspY_v (ofInt2 m), σ_v⟫/‖σ_v‖²`, by linearity of the inner
  product in the `y`-argument;
* shifts `w` by `wOf v (ofInt2 m)`, since `y ↦ cuspY v y` and the orthogonal projections onto
  `(frame2, frame3)` are additive. -/
theorem ThetaPolar_add_int (v : Fin 5) (p y : E2) (m : Fin 2 → ℤ) :
    ThetaPolar v p (y + ofInt2 m) = !₂[(ThetaPolar v p y) 0,
      (ThetaPolar v p y) 1 + 2 * π * inner ℝ (cuspY v (ofInt2 m)) (slope v) / ‖slope v‖ ^ 2,
      (ThetaPolar v p y) 2 + (wOf v (ofInt2 m)) 0,
      (ThetaPolar v p y) 3 + (wOf v (ofInt2 m)) 1] := by
  -- `cuspY` is additive, so `y ↦ y + ofInt2 m` moves `cuspY` by `cuspY v (ofInt2 m)`.
  have hcusp : cuspY v (y + ofInt2 m) = cuspY v y + cuspY v (ofInt2 m) := by
    ext i
    fin_cases i <;> simp [cuspY, add_smul] <;> ring
  -- the `w`-coordinates are additive
  have hw := wOf_add v y (ofInt2 m)
  -- hence the angle shifts by the phase of the lattice translation
  have hθ : thetaAng v p (y + ofInt2 m) =
      thetaAng v p y + 2 * π * inner ℝ (cuspY v (ofInt2 m)) (slope v) / ‖slope v‖ ^ 2 := by
    rw [thetaAng, thetaAng, hcusp, inner_add_left]
    ring
  -- and the radial coordinate is unchanged (`β` is periodic under the cusp lattice)
  have hr : radial v p (y + ofInt2 m) = radial v p y := by
    simp only [radial, collarS_add_int]
  ext i
  fin_cases i <;> simp [ThetaPolar, hr, hθ, hw]

end Work.Cusp
