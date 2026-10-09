import Mathlib
import Submission.Work.SSGRoute.E8Helpers
import Submission.NK.NUV2.LC.RouteB.locUnits_tower_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace Work.SSGRoute

open CategoryTheory
open scoped NumberField

/-- **Restriction–locality square (E8', step P1).** For a tower of finite Galois number-field extensions `k ⊆ M ⊆ E` and any place `ŵ` of `E`, the localisation `locUnits` at the lower level `M` of a class restricted from the level `k` equals the restriction along `Work.SSGRoute.stabIncl` of the localisation at the level `k`. Both sides are "restrict the class to the decomposition group of `ŵ` inside `Gal(E/M) ⊆ Gal(E/k)` and then apply the coefficient map `Eˣ → E_ŵˣ`"; the only content is the bookkeeping of `NK.NUV2.ChebAux.Transfer.resToGal` (restriction to `ker (Gal(E/k) →* Gal(M/k))`) and `Work.SSGRoute.res_stabIncl_localUnitsRep_eq` (`rfl`). Useful helpers: `groupCohomology.resNatTrans_app`, `groupCohomology.map_comp`, `groupCohomology.map_congr`, and the "map functional calculus" lemmas in `Submission/NK/NUV2/LC/RouteB/locUnits_tower_eq_zero.lean` (`map_id_comp_apply`, `map_f_comp_id`, `map_resFunctor_map`, `map_comp_of_res`), whose style (`conv_lhs`/`conv_rhs` followed by `groupCohomology.map_congr`) proves the analogous inflation square `unitsLevelMapTower_comp_locUnits` in that same file. -/
theorem eb_locUnits_resToGal {k M E : Type} [Field k] [NumberField k] [Field M] [NumberField M] [Field E] [NumberField E] [Algebra k M] [Algebra k E] [Algebra M E] [IsScalarTower k M E] [FiniteDimensional k M] [FiniteDimensional k E] [FiniteDimensional M E] [IsGalois k M] [IsGalois k E] [IsGalois M E] (ŵ : NK.GlobalCFT.Place E) : ∀ x : groupCohomology (NK.HassePrinciple.unitsRep k E) 2, (NK.HassePrinciple.locUnits M E ŵ).hom ((NK.NUV2.ChebAux.Transfer.resToGal k M E).hom x) = ((groupCohomology.resNatTrans NK.HassePrinciple.CoeffInt (Work.SSGRoute.stabIncl (k := k) (M := M) ŵ) 2).app (NK.HassePrinciple.localUnitsRep k E ŵ)).hom ((NK.HassePrinciple.locUnits k E ŵ).hom x) := by
  have key : (NK.NUV2.ChebAux.Transfer.resToGal k M E) ≫ (NK.HassePrinciple.locUnits M E ŵ)
      = (NK.HassePrinciple.locUnits k E ŵ) ≫
        ((groupCohomology.resNatTrans NK.HassePrinciple.CoeffInt
          (Work.SSGRoute.stabIncl (k := k) (M := M) ŵ) 2).app
            (NK.HassePrinciple.localUnitsRep k E ŵ)) := by
    simp only [NK.NUV2.ChebAux.Transfer.resToGal, NK.HassePrinciple.locUnits,
      groupCohomology.resNatTrans_app]
    conv_lhs => rw [NK.NUV2.LC.RouteB.map_id_comp_apply, ← groupCohomology.map_comp]
    conv_rhs => rw [Category.assoc]
    conv_rhs => rw [← NK.NUV2.LC.RouteB.map_resFunctor_map]
    conv_rhs => rw [← groupCohomology.map_comp]
    refine (groupCohomology.map_congr ?_ ?_ 2).symm
    · exact MonoidHom.ext fun σ => rfl
    · ext x
      rfl
  intro x
  have h := congrArg (fun m => m.hom x) key
  exact h

end Work.SSGRoute
