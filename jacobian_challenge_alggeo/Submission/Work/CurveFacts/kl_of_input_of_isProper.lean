/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area CurveFacts
-/
import Submission.Work.CurveFacts.kl_of_input

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area `CurveFacts`: the key result with properness as an explicit hypothesis

`Work.CurveFacts.kl_of_input` has the shape

`∀ {A : Sch K} [GrpObj A] [IsCommMonObj A] [IsProper A.hom] (f : C.toOver ⟶ A) …,`

i.e. properness of the target is an *instance* argument.  Consumers whose target carries
properness as an ordinary hypothesis rather than as a synthesizable instance -- notably the
generic chart-map lemmas of area `UP`, which are stated for an arbitrary commutative group
object and only specialised to abelian varieties later -- cannot feed it to `kl_of_input`
directly.  This file provides the same statement with properness as an explicit argument, so that
it can be applied with `kl_of_input_of_isProper D hA f …`.

The proof is `Work.CurveFacts.kl_of_input` with `haveI := hA`.
-/
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical MonObj
open scoped Work.GCBasics

universe u

namespace Work.CurveFacts

/-- **Item A6, first half, with properness as an explicit hypothesis.**  Same statement as
`Work.CurveFacts.kl_of_input`, with `[IsProper A.hom]` replaced by an ordinary argument `hA`. -/
theorem kl_of_input_of_isProper {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : 𝟙_ (Work.GCBasics.Sch K) ⟶ C.toOver} [Work.SpecLin.DivBase C]
    (D : Work.GroupChunk.Input C P0) [Work.Universal.SymQuotData C P0 D]
    {A : Work.GCBasics.Sch K} [GrpObj A] [IsCommMonObj A] (hA : IsProper A.hom)
    (f : C.toOver ⟶ A) {F : Type u} [Field F] [Algebra K F]
    (E E' : Work.GCBasics.Dv C F) (hE : E.IsEffective) (hE' : E'.IsEffective) (n : ℕ)
    (hn : Work.GCBasics.Ddeg C F E = (n : ℤ)) (hn' : Work.GCBasics.Ddeg C F E' = (n : ℤ)) :
    Work.GCBasics.LinEquiv C E E' →
      Work.Universal.sumDiv D f E hE n hn = Work.Universal.sumDiv D f E' hE' n hn' := by
  haveI : IsProper A.hom := hA
  exact kl_of_input D f E E' hE hE' n hn hn'

end Work.CurveFacts
