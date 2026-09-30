/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Powers of a curve

`Work.Normality.Curve.pow C n` is the `n`-fold product `Cⁿ = C ⊗[K] ⋯ ⊗[K] C` of a curve with
itself over `K`, taken in the cartesian monoidal category `Sch K = Over (Spec K)`.

This is the source of the quotient map `Cⁿ ⟶ Symⁿ C`; the naturality statements
(`Sym.quot`, `divOf`) are the business of area SY, which is free to use this definition or its
own.  The two relevant properties of `Cⁿ` — that its structure morphism is smooth and that it is
integral over `K` (so that `Work.Normality.hasIntegrallyClosedStalks_of_smooth` applies to it,
yielding `Work.Normality.isIntegrallyClosed_stalk_pow`) — are proved inside
`Submission/Work/Normality/isIntegrallyClosed_stalk_pow.lean`.
-/
import Mathlib
import Submission.Work.CurveBasics.Basic
import Submission.Work.AbVar.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct MonoidalCategory

universe u

namespace Work.Normality

open Work.CurveBasics

noncomputable section

variable {K : Type u} [Field K]

/-- The `n`-fold product `Cⁿ` of a curve with itself over `K`, as an object of `Sch K`. -/
noncomputable def Curve.pow (C : Curve K) : ℕ → AbVar.Sch K
  | 0 => 𝟙_ (AbVar.Sch K)
  | (n + 1) => (Curve.pow C n) ⊗ C.toOver

@[simp]
theorem Curve.pow_zero (C : Curve K) : Curve.pow C 0 = 𝟙_ (AbVar.Sch K) := rfl

@[simp]
theorem Curve.pow_succ (C : Curve K) (n : ℕ) :
    Curve.pow C (n + 1) = Curve.pow C n ⊗ C.toOver := rfl

end

end Work.Normality
