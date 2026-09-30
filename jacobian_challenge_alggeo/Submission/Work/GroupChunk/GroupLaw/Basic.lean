import Submission.Work.GroupChunk.Assembly
import Submission.Work.GroupChunk.GroupLaw.mul_exists
import Submission.Work.GroupChunk.GroupLaw.inv_exists
import Submission.Work.GroupChunk.GroupLaw.one_exists
import Submission.Work.GroupChunk.GroupLaw.grpObj_exists

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical MonObj AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

universe u

namespace Work.GroupChunk

noncomputable section

open Work.GCBasics

variable {K : Type u} [Field K] {C : CurveBasics.Curve K} {P0 : 𝟙_ (Sch K) ⟶ C.toOver}
  [SpecLin.DivBase C]

namespace Input

variable [D : Input C P0]

/-- **The group law of the group chunk** `G D`. -/
def mul (D : Input C P0) : GSch D ⊗ GSch D ⟶ GSch D :=
  Classical.choose (GroupLaw.mul_exists D)

/-- The group law adds classes. -/
theorem cls_mul (D : Input C P0) {F : Type u} [Field F] [Algebra K F]
    (p q : FPt (GSch D) F) :
    D.cls (CartesianMonoidalCategory.liftEquiv (p, q) ≫ D.mul) = D.cls p + D.cls q :=
  (Classical.choose_spec (GroupLaw.mul_exists D)) p q

/-- **The inverse of the group chunk** `G D`. -/
def inv (D : Input C P0) : GSch D ⟶ GSch D :=
  Classical.choose (GroupLaw.inv_exists D)

/-- The inverse negates classes. -/
theorem cls_inv (D : Input C P0) {F : Type u} [Field F] [Algebra K F]
    (p : FPt (GSch D) F) : D.cls (p ≫ D.inv) = - D.cls p :=
  (Classical.choose_spec (GroupLaw.inv_exists D)) p

/-- **The unit of the group chunk** `G D`. -/
def one (D : Input C P0) : 𝟙_ (Sch K) ⟶ GSch D :=
  Classical.choose (GroupLaw.one_exists D)

/-- The unit of `G D` has class zero. -/
theorem cls_one (D : Input C P0) {F : Type u} [Field F] [Algebra K F] :
    D.cls (toUnit (specOf K F) ≫ D.one) = 0 :=
  (Classical.choose_spec (GroupLaw.one_exists D))

/-- **The group structure of the group chunk `G D`.** -/
instance instGrpObj (D : Input C P0) : GrpObj (GSch D) :=
  Classical.choose (GroupLaw.grpObj_exists D D.mul (cls_mul D) D.inv (cls_inv D) D.one (cls_one D))

/-- The group law of the group structure is `D.mul`. -/
theorem mul_eq_grpObj (D : Input C P0) : μ[GSch D] = D.mul :=
  (Classical.choose_spec (GroupLaw.grpObj_exists D D.mul (cls_mul D)
    D.inv (cls_inv D) D.one (cls_one D))).1

/-- The inverse of the group structure is `D.inv`. -/
theorem inv_eq_grpObj (D : Input C P0) : ι[GSch D] = D.inv :=
  (Classical.choose_spec (GroupLaw.grpObj_exists D D.mul (cls_mul D)
    D.inv (cls_inv D) D.one (cls_one D))).2.1

/-- The unit of the group structure is `D.one`. -/
theorem one_eq_grpObj (D : Input C P0) : η[GSch D] = D.one :=
  (Classical.choose_spec (GroupLaw.grpObj_exists D D.mul (cls_mul D)
    D.inv (cls_inv D) D.one (cls_one D))).2.2

/-- The class map is additive for the group structure of `G D`. -/
theorem cls_mul_grpObj (D : Input C P0) {F : Type u} [Field F] [Algebra K F]
    (p q : FPt (GSch D) F) :
    D.cls (CartesianMonoidalCategory.liftEquiv (p, q) ≫ μ[GSch D]) = D.cls p + D.cls q := by
  rw [D.mul_eq_grpObj]
  exact cls_mul D p q

/-- The class map inverts for the group structure of `G D`. -/
theorem cls_inv_grpObj (D : Input C P0) {F : Type u} [Field F] [Algebra K F]
    (p : FPt (GSch D) F) : D.cls (p ≫ ι[GSch D]) = - D.cls p := by
  rw [D.inv_eq_grpObj]
  exact cls_inv D p

/-- The identity of `G D` has class zero. -/
theorem cls_one_grpObj (D : Input C P0) {F : Type u} [Field F] [Algebra K F] :
    D.cls (toUnit (specOf K F) ≫ η[GSch D]) = 0 := by
  rw [D.one_eq_grpObj]
  exact cls_one D

end Input

end

end Work.GroupChunk
