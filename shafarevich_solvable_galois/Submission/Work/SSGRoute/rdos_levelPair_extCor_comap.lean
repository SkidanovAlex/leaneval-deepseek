import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.E7bDefs
import Submission.Work.SSGRoute.comp_extCor
import Submission.Work.SSGRoute.extCor_yoneda_comp
import Submission.Work.SSGRoute.rdos_mackey_formula
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# X4: the Mackey formula at the level pairing, `⟨cor_S^D z, h⟩_G = cor_{S'}^G ⟨z, res_{S'} h⟩`

Assembled from `Work.SSGRoute.extRes_extCor_comap` (the Mackey formula for `extCor`),
`Work.SSGRoute.extCor_comp_extRes` (the projection formula) and `Work.SSGRoute.comp_extCor` (the
mirror projection formula).
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

/-- **X4 (Mackey + projection formula, abstract).**  For a surjection `f : G ↠ D` of finite groups,
`S ≤ D` and `S' = f⁻¹(S)`: pairing the corestriction `cor_S^D z` with `h ∈ H¹(G, res_f M)` is the
corestriction `cor_{S'}^G` of the pairing of `z` with the restriction of `h` to `S'`. -/
theorem levelPair_extCor_comap_rdos {G D : Type} [Group G] [Group D] [Fintype G] [Fintype D]
    (f : G →* D) (hf : Function.Surjective f) (S : Subgroup D)
    [DecidableRel (QuotientGroup.rightRel S)] [Fintype (D ⧸ S)]
    [DecidableRel (QuotientGroup.rightRel (S.comap f))] [Fintype (G ⧸ S.comap f)]
    {M A : Rep Coeff D} {B : Rep Coeff G} (ι : Rep.res f A ⟶ B)
    (z : Abelian.Ext (Rep.res S.subtype M) (Rep.res S.subtype A) 1)
    (h : extH (Rep.res f M) 1) :
    levelPair f ι (extCor S M A 1 z) h =
      extCor (S.comap f) (unitRep G) B 2
        (levelPair (f.subgroupComap S) (Rep.resMap (S.comap f).subtype ι) z
          (extHRestrict (S.comap f) h)) := by
  have hM1 := MackeyIso.extRes_extCor_comap_rdos f hf S M A 1 z
  have hC := extCor_comp_extRes (S.comap f) (H := Rep.res f M) (Abelian.Ext.mk₀ ι)
    (extRes (f.subgroupComap S) z)
  have hP := comp_extCor (S.comap f) h
    ((extRes (f.subgroupComap S) z).comp (extRes (S.comap f).subtype (Abelian.Ext.mk₀ ι)) rfl)
  simp only [levelPair]
  rw [hM1, ← hC, hP]
  have hR : extHRestrict (S.comap f) h = extRes (S.comap f).subtype h := by
    simp only [extHRestrict, extHMap, show unitRes (S.comap f).subtype = 𝟙 _ from rfl,
      Abelian.Ext.mk₀_id_comp, Abelian.Ext.comp_mk₀_id]
  have hI : extRes (S.comap f).subtype (Abelian.Ext.mk₀ ι) =
      Abelian.Ext.mk₀ (Rep.resMap (S.comap f).subtype ι) := Abelian.Ext.mapExactFunctor_mk₀ _ _
  rw [hR, hI]

end Work.SSGRoute
