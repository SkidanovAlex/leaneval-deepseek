/-
AREA RESOL — the mapping telescope used in B5.

Given a sequence `X : ℕ → Cpx` of cochain complexes and maps `i m : X m ⟶ X (m+1)`, let
`A := ∐ X` and let `s : A ⟶ A` be the map whose restriction to the `m`-th summand is `i m`
followed by the inclusion of the `(m+1)`-st summand.  The *telescope* is
`T := mappingCone (𝟙 A - s)`.  This is the standard `cone(1 - shift)` model of the homotopy
colimit; it is solid-cofibrant whenever all the `X m` and their shifts are (`hC.sigma` on `∐ X`
and `hC.cone` on the triangle of the mapping cone).
-/
import Mathlib
import Submission.Work.RESOL.Basic
import Submission.Work.RESOL.SigmaSetup

open CategoryTheory Limits
open _root_.LightCondensed

noncomputable section

namespace Work.RESOL

/-- The "shift" map `∐ X ⟶ ∐ X` whose restriction to the `m`-th summand is
`i m : X m ⟶ X (m+1)`. -/
def telescopeShift (X : ℕ → Cpx) [HasCoproduct X] (i : ∀ m : ℕ, X m ⟶ X (m + 1)) :
    (∐ X) ⟶ (∐ X) :=
  Sigma.desc (fun m => i m ≫ Sigma.ι X (m + 1))

/-- The telescope `cone(1 - shift)` of a sequence of complexes. -/
def telescope (X : ℕ → Cpx) [HasCoproduct X] (i : ∀ m : ℕ, X m ⟶ X (m + 1)) : Cpx :=
  CochainComplex.mappingCone (𝟙 (∐ X) - telescopeShift X i)

end Work.RESOL
