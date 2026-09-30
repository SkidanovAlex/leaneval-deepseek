import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.beta_lattice_periodic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.Cusp

open scoped Real InnerProductSpace

/-- `cuspX` is equivariant under an integer translation of the torus coordinates `(y₂,y₃)`:
translating `y` by `ofInt2 m` translates the cusp coordinate `x = u σ_v + y₂λ₂ + y₃λ₃` by
`m₀λ₂ + m₁λ₃ = ofInt3 m'`, an integer vector (hence a period of `β`). -/
theorem cuspX_add_int (v : Fin 5) (up : ℝ) (y : E2) (m : Fin 2 → ℤ) :
    cuspX v up (y + ofInt2 m) = cuspX v up y + ((m 0 : ℝ) • lam2 v + (m 1 : ℝ) • lam3 v) := by
  ext i
  fin_cases i <;> simp [cuspX, cuspY, ofInt2, lam2, lam3, kv] <;> ring

/-- The shift `m₀λ₂ + m₁λ₃` of `cuspX` is the integer vector with coordinates
`m₀ (κ_{v,2})_i + m₁ (κ_{v,3})_i`. -/
theorem cuspX_add_int_ofInt3 (v : Fin 5) (up : ℝ) (y : E2) (m : Fin 2 → ℤ) :
    cuspX v up (y + ofInt2 m) =
      cuspX v up y + ofInt3 (fun i => m 0 * kappa v 1 i + m 1 * kappa v 2 i) := by
  rw [cuspX_add_int]
  congr 1
  ext i
  fin_cases i <;> simp [ofInt3, lam2, lam3, kv]

/-- The height of the collar is invariant under integer translations of the torus coordinates:
`β` is `ℤ³`-periodic and the shift `m₀λ₂ + m₁λ₃` is an integer vector. -/
theorem collarS_add_int (v : Fin 5) (p y : E2) (m : Fin 2 → ℤ) :
    collarS v p (y + ofInt2 m) = collarS v p y := by
  simp only [collarS, cuspX_add_int_ofInt3, beta_add_ofInt3]

theorem ThetaOuter_add_int (v : Fin 5) (p y : E2) (m : Fin 2 → ℤ) :
    ThetaOuter v p (y + ofInt2 m) = ThetaOuter v p y +
      ((m 0 : ℝ) • !₂[(lam2 v) 0, (lam2 v) 1, (lam2 v) 2, 0] +
        (m 1 : ℝ) • !₂[(lam3 v) 0, (lam3 v) 1, (lam3 v) 2, 0]) := by
  have hS := collarS_add_int v p y m
  have hX := cuspX_add_int v (u p) y m
  simp only [ThetaOuter, hS, hX]
  ext i
  fin_cases i <;> simp [lam2, lam3, kv]

end Work.Cusp
