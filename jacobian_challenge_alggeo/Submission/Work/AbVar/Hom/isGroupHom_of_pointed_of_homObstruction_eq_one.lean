import Mathlib
import Submission.Work.AbVar.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped MonObj

namespace Work.AbVar.Hom

open CategoryTheory in
theorem isGroupHom_of_pointed_of_homObstruction_eq_one {k : Type*} [Field k]
    {G H : Work.AbVar.Sch k} [GrpObj G] [GrpObj H] [IsCommMonObj H] (g : G ⟶ H)
    (hg : MonObj.one (X := G) ≫ g = MonObj.one (X := H))
    (h : Work.AbVar.homObstruction g =
      SemiCartesianMonoidalCategory.toUnit (MonoidalCategoryStruct.tensorObj G G) ≫
        MonObj.one (X := H)) : IsMonHom g := by
  refine ⟨?_, ?_⟩
  · -- pointedness is exactly the unit compatibility
    simpa using hg
  · -- `homObstruction g = 1` in the (commutative) group `Hom(G ⊗ G, H)`
    have key : (MonObj.mul (X := G) ≫ g) * (fst G G ≫ g)⁻¹ * (snd G G ≫ g)⁻¹ = 1 := by
      rw [← Work.AbVar.homObstruction_eq]
      rw [h, ← Hom.one_def]
    have key' : (MonObj.mul (X := G) ≫ g) * ((fst G G ≫ g)⁻¹ * (snd G G ≫ g)⁻¹) = 1 := by
      rw [← _root_.mul_assoc]; exact key
    -- `μ[G] ≫ g = (snd ≫ g) * (fst ≫ g)`
    have hcb : (MonObj.mul (X := G) ≫ g) = (snd G G ≫ g) * (fst G G ≫ g) := by
      have hh := mul_eq_one_iff_eq_inv.mp key'
      simpa [mul_inv_rev] using hh
    -- `(g ⊗ₘ g) ≫ μ[H] = (fst ≫ g) * (snd ≫ g)`
    have hbc : (g ⊗ₘ g) ≫ MonObj.mul (X := H) = (fst G G ≫ g) * (snd G G ≫ g) := by
      rw [Hom.mul_def, lift_fst_comp_snd_comp]
    rw [hbc, hcb, mul_comm]

end Work.AbVar.Hom
