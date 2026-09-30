import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- Every lattice vector `κ_{v,i}` (`i = 1,2,3`) of every cusp `v` is nonzero in `ℝ³`: the
integer triples of `Data.kappa` are all nonzero, and `kv` is their image under the
coordinatewise cast `ℤ → ℝ`.  Since each `κ_{v,i}` is a vector of the orthogonal `ℤ`-basis
`(κ_{v,1}, κ_{v,2}, κ_{v,3})` of the lattice `Λ_v`, this is what shows that the `κ_{v,i}` are
honest basis vectors of the cusp lattice. -/
theorem kv_ne_zero (v : Fin 5) (i : Fin 3) : kv v i ≠ 0 := by
  fin_cases v <;> fin_cases i <;> simp [kv, kappa]

end Work.Cusp
