/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area RR: existence of a canonical divisor

Every nonzero Weil differential `ω` has a divisor `W = divW ω`, and duality
(`Duality.isCanonical_divW`) says that `i D = l (W - D)` for all `D`.  Since a nonzero Weil
differential exists (`Duality.exists_ne_zero_mem_Omega`), so does a canonical divisor.
-/
import Submission.Work.RiemannRoch.Canonical
import Submission.Work.RiemannRoch.Canonical.Properties
import Submission.Work.RiemannRoch.Duality.exists_ne_zero_mem_Omega
import Submission.Work.RiemannRoch.Duality.isCanonical_divW

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

/-- **Existence of a canonical divisor**: the divisor of any nonzero Weil differential. -/
theorem exists_isCanonical (C : Curve k) : ∃ W : C.Div, IsCanonical C W := by
  obtain ⟨ω, hω, hω0⟩ := Duality.exists_ne_zero_mem_Omega C
  exact ⟨divW C ω, Duality.isCanonical_divW C hω hω0⟩

/-- A canonical divisor on `C`, chosen once and for all. -/
noncomputable def canonical (C : Curve k) : C.Div := Classical.choose (exists_isCanonical C)

theorem isCanonical_canonical (C : Curve k) : IsCanonical C (canonical C) :=
  Classical.choose_spec (exists_isCanonical C)

end

end Curve

end Work.RiemannRoch
