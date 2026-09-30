/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area RR: the index of speciality vanishes in large degree

If `ω ≠ 0` is a Weil differential vanishing on `K + A(D)` then `deg D ≤ 2g - 2`
(`Duality.deg_le_of_mem_WD`).  Since `WD C D` is the dual of `H1 C D` and hence has dimension
`i C D` (`Duality.finrank_WD`), this forces `WD C D = 0`, i.e. `i D = 0`, as soon as
`deg D ≥ 2g - 1`.  This is the "RR4" vanishing input for the Riemann–Roch equation.
-/
import Submission.Work.RiemannRoch.RRLib
import Submission.Work.RiemannRoch.Duality.finrank_WD
import Submission.Work.RiemannRoch.Duality.deg_le_of_mem_WD

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.RiemannRoch

open Work.CurveBasics

namespace Curve

noncomputable section

variable {k : Type u} [Field k]

/-- **Vanishing of the index of speciality in large degree**: `i D = 0` for
`deg D ≥ 2g - 1`. -/
theorem exists_i_eq_zero (C : Curve k) :
    ∃ N : ℤ, ∀ D : C.Div, N ≤ C.deg D → i C D = 0 := by
  refine ⟨2 * (genus C : ℤ) - 1, fun D hD => ?_⟩
  have hbot : WD C D = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro ω hω
    by_contra hne
    have hle := Duality.deg_le_of_mem_WD C hne hω
    have hg : (0 : ℤ) ≤ (genus C : ℤ) := Int.natCast_nonneg _
    linarith
  rw [← Duality.finrank_WD C D, hbot]
  simp

end

end Curve

end Work.RiemannRoch
