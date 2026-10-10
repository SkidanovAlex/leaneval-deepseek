/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotV

# Root H1: the point set of `N(E)` and the order sums
-/

import Mathlib
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.Relations
import Submission.Work.MotC2.AffPlace
import Submission.Work.MotV.Defs
import Submission.Work.MotV.PlaceDefs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero

namespace Work.MotV

noncomputable section

variable {N : Type*} [Field N]

/-- The type of rational places of `N(E)/N`. -/
abbrev Place (N : Type*) [Field N] (E : WeierstrassCurve N) :=
  {S : Subalgebra N (MotC2.Func E) // MotC2.IsRatPlace E S}

/-- The order of `f` at the place `Q`. -/
def ordP (E : WeierstrassCurve N) (Q : Place N E) (f : MotC2.Func E) : ℤ :=
  ordOfPlace E Q.1 Q.2 f

/-- The quadratic `Y² + (a₁c+a₃)Y - (c³+a₂c²+a₄c+a₆)`. -/
def quad (E : WeierstrassCurve N) (c : N) : Polynomial N :=
  X ^ 2 + C (E.a₁ * c + E.a₃) * X - C (c ^ 3 + E.a₂ * c ^ 2 + E.a₄ * c + E.a₆)

/-- The affine places of `E` above `x = c`, indexed by the roots of `quad E c`. -/
def fibrePlaces (E : WeierstrassCurve N) [E.IsElliptic] (c : N) : Finset (Place N E) := by
  classical
  refine Finset.biUnion ((quad E c).roots.toFinset) fun d => ?_
  by_cases h : WeierstrassCurve.Affine.Equation E c d
  · have hns : WeierstrassCurve.Affine.Nonsingular E c d :=
      (WeierstrassCurve.Affine.equation_iff_nonsingular (W := E)).mp h
    exact {⟨MotC2.affPlaceAt E c d, (MotC2.AffPlace N E c d hns).1⟩}
  · exact ∅

/-- The set of all places whose `x`-coordinate is a root of `p`, together with the point at
infinity. -/
def ptsOf (E : WeierstrassCurve N) [E.IsElliptic] (hInf : MotC2.IsRatPlace E (MotC2.infPlace E))
    (p : Polynomial N) : Finset (Place N E) := by
  classical
  exact insert ⟨MotC2.infPlace E, hInf⟩
    (Finset.biUnion p.roots.toFinset fun c => fibrePlaces E c)

/-- The sum of the orders of `f` over a finite set of places. -/
def ordSum (E : WeierstrassCurve N) (S : Finset (Place N E)) (f : MotC2.Func E) : ℤ :=
  Finset.sum S fun Q => ordP E Q f

end

end Work.MotV
