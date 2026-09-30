/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area DescentGeom (geometric half of area DS)
-/
import Submission.Work.DescentGeom.Basic
import Submission.Work.DescentGeom.exists_descentData

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area `DescentGeom` — the descended scheme `J = G'/Γ` and the isomorphism `J_{k'} ≅ G'`

The interface `Input` provides the group chunk `G'` over `k'`, the semilinear Galois action on it
and a `Γ`-stable affine cover.  By `Work.DescentGeom.exists_descentData` (effective Galois descent
of schemes, affine-locally from Speiser's lemma, via the quotient of area `SY`/SY1) there is then a
`k`-scheme `J` with a `Γ`-equivariant isomorphism `J_{k'} ≅ G'`.  This file records that
construction: `Input.J`, `Input.bcIso` and `Input.bcIso_compat`.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonObj MonoidalCategory CategoryTheory CategoryTheory.Obj
open CartesianMonoidalCategory Functor

universe u

namespace Work.DescentGeom

noncomputable section

namespace Input

variable {k : Type u} [Field k] {C : Sch k} {P0 : 𝟙_ (Sch k) ⟶ C}

/-- **Effective Galois descent of the group chunk**: there is a `k`-scheme `J` with a
`Γ`-equivariant isomorphism `J_{k'} ≅ G'`. -/
noncomputable def descentData (D : Input C P0) :
    ∃ (J : Sch k) (e : bc D.k' J ≅ D.G'), ∀ σ : Work.Descent.Gal k D.k',
      Work.Descent.galAct J σ ≫ e.hom.left = e.hom.left ≫ (D.galAct σ).hom :=
  @exists_descentData k D.k' _ _ _ _ _ D.G'
    (by haveI := D.isProper'; infer_instance)
    D.galAct D.galAct_one D.galAct_mul D.galAct_hom D.hcover

/-- The quotient `J = G'/Γ` of the group chunk by the Galois group, as a `k`-scheme. -/
noncomputable def J (D : Input C P0) : Sch k := (descentData D).choose

/-- The descent isomorphism `J_{k'} ≅ G'`. -/
noncomputable def bcIso (D : Input C P0) : bc D.k' (J D) ≅ D.G' :=
  (descentData D).choose_spec.choose

/-- The descent isomorphism is `Γ`-equivariant. -/
theorem bcIso_compat (D : Input C P0) (σ : Work.Descent.Gal k D.k') :
    galActK D.k' (J D) σ ≫ (bcIso D).hom.left =
      (bcIso D).hom.left ≫ (D.galAct σ).hom :=
  (descentData D).choose_spec.choose_spec σ

end Input

end

end Work.DescentGeom
