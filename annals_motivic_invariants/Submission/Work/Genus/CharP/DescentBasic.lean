/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.Genus
-/
import Mathlib
import Submission.Work.Genus.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Bookkeeping for the Frobenius descent of the genus chapter

The file `Submission/Work/Genus/CharP/Defs.lean` defines the `p`-th root twist of a Weierstrass
curve over a perfect field of characteristic `p`.  The proof that every `F(t)`-point of a
non-singular Weierstrass curve is constant is a strong induction on the *size*
(`= deg num + deg denom`) of the abscissa, descending along the Frobenius.  This file collects the
three abbreviations/definitions in which that statement is phrased, so that the pieces of the
descent can be stated and proved separately.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open Polynomial

namespace Work.Genus.CharP

noncomputable section

variable {F : Type*} [Field F]

/-- **The Weierstrass equation over `F(t)`.**  `WEqn E x y` is the statement that `(x, y)` is an
`F(t)`-point of the curve `E`. -/
def WEqn (E : WeierstrassCurve F) (x y : RatFunc F) : Prop :=
  y ^ 2 + algebraMap F (RatFunc F) E.a₁ * x * y + algebraMap F (RatFunc F) E.a₃ * y
    = x ^ 3 + algebraMap F (RatFunc F) E.a₂ * x ^ 2 + algebraMap F (RatFunc F) E.a₄ * x
      + algebraMap F (RatFunc F) E.a₆

/-- **The constants of `F(t)`.**  `IsConst z` says that `z` is the image of an element of `F`. -/
def IsConst (z : RatFunc F) : Prop := ∃ c : F, z = algebraMap F (RatFunc F) c

/-- **The size of a rational function**: the sum of the degrees of its numerator and of its
denominator (in the reduced form of `RatFunc`).  This is the decreasing measure of the Frobenius
descent: `Size (X ^ p) = p * Size X`. -/
def Size (z : RatFunc F) : ℕ := z.num.natDegree + z.denom.natDegree

@[simp]
theorem size_zero : Size (0 : RatFunc F) = 0 := by
  simp [Size]

theorem isConst_zero : IsConst (0 : RatFunc F) := ⟨0, by simp⟩

end

end Work.Genus.CharP
