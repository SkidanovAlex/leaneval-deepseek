import Mathlib
import Submission.NK.NUV2.ARL.HR.TransferSupport
import Submission.NK.HassePrinciple.LocalUnits
import Submission.NK.NUV2.ChebAux.Transfer.locUnits_res_inflation_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 1600000

open CategoryTheory

namespace NK.HR2

/-- The restriction `Gal(E/K) →* Gal(L/K)` is the composite `rhoRestrict` of the inclusion
`Gal(E/K) ↪ Gal(E/K)` (i.e. of the case `M = K`) with the restriction of scalars: the
"`M = K`" instance of `NK.NUV2.ARL.HR.rhoRestrict` is the plain level restriction. -/
theorem rhoRestrict_self_eq_restrictHom {K L E : Type} [Field K] [Field L] [Field E] [Algebra K L]
    [Algebra K E] [Algebra L E] [IsScalarTower K L E] [IsGalois K L] :
    NK.NUV2.ARL.HR.rhoRestrict (K := K) (L := L) (M := K) (E := E)
      = NK.NUV2.ARL.HR.restrictHom (K := K) (L := L) (E := E) := by
  apply MonoidHom.ext; intro σ; congr 1

/-- **The level inflation is the `M = K` instance of the map `(rhoRestrict, unitsInclRepM)`.**

Concretely: the restriction map of the tower with `M = K` is the plain level restriction
`restrictHom` (`rhoRestrict_self_eq_restrictHom`), and the two coefficient morphisms
`unitsInclRepM (M := K)` and `unitsInclRep` have the same underlying map `Lˣ → Eˣ`; hence the two
induced maps on `H²` agree. -/
theorem map_rhoRestrict_self_unitsInclRepM_eq_inflation {K L E : Type} [Field K] [Field L]
    [Field E] [Algebra K L] [Algebra K E] [Algebra L E] [IsScalarTower K L E] [IsGalois K L] :
    groupCohomology.map (NK.NUV2.ARL.HR.rhoRestrict (K := K) (L := L) (M := K) (E := E))
        (NK.NUV2.ARL.HR.unitsInclRepM (K := K) (L := L) (M := K) (E := E)) 2
      = (NK.NUV2.ARL.HR.inflation (K := K) (L := L) (E := E)) := by
  refine groupCohomology.map_congr
    (f := NK.NUV2.ARL.HR.rhoRestrict (K := K) (L := L) (M := K) (E := E))
    (g := NK.NUV2.ARL.HR.restrictHom (K := K) (L := L) (E := E))
    (φ := NK.NUV2.ARL.HR.unitsInclRepM (K := K) (L := L) (M := K) (E := E))
    (ψ := NK.NUV2.ARL.HR.unitsInclRep (K := K) (L := L) (E := E))
    (rhoRestrict_self_eq_restrictHom (K := K) (L := L) (E := E)) ?_ 2
  ext x
  rfl

/-- **The localisation of the level inflation vanishes if the localisation of the class does.**
`inflation (K := K) (L := L) (E := E) : H²(Gal(L/K), Lˣ) → H²(Gal(E/K), Eˣ)` is the map induced by
the restriction `Gal(E/K) → Gal(L/K)` and the units inclusion `Lˣ → Eˣ`
(`NK.NUV2.ARL.HR.inflation`), and `NK.HassePrinciple.locUnits K E ŵ` is the localisation at a
place `ŵ` of `E`.  If `v'` is a place of `L` lying below `ŵ` and the localisation of `c` at `v'`
vanishes, then the localisation of the inflation of `c` at `ŵ` vanishes.

Proof route: combine the proved identities of
`Submission/Work/NUV2/ChebAux/Transfer/locUnits_res_inflation_eq_zero.lean`
(`resToGal_inflation_eq_map`: `resToGal ≫ inflation = map rhoRestrict unitsInclRepM`, and
`locUnits_rhoRestrict_unitsInclRepM_eq`:
`map rhoRestrict unitsInclRepM ≫ locUnits M E ŵ = locUnits K L v' ≫ localLevelMapRho`) with
`NK.HassePrinciple.locUnits` being `resNatTrans ≫ map 𝟙 unitsToLocalUnits`, and then observe that
`resToGal` is the restriction to the subgroup `Gal(E/M) ⊆ Gal(E/K)`, so that the composite factors
as `locUnits K E ŵ` after `resToGal`.  (The reviewer noted that for `M := L` this is a special
case of `NK.HR2.locUnits_inflation_eq_zero_iff`; either route is acceptable.)

Here we take the specialisation `M := K` of the proved square
`locUnits_rhoRestrict_unitsInclRepM_eq`: at `M = K` the "restriction" `rhoRestrict` is the plain
level restriction and the coefficient morphism `unitsInclRepM` is the units inclusion, so the
square reads
`inflation ≫ locUnits K E ŵ = locUnits K L v' ≫ localLevelMapRho`
(`map_rhoRestrict_self_unitsInclRepM_eq_inflation`).  Applying it to `c` and using
`locUnits K L v' c = 0` gives the claim. -/
theorem locUnits_inflation_eq_zero_of_loc_eq_zero {K L E : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Field E] [NumberField E] [Algebra K L] [Algebra K E]
    [Algebra L E] [IsScalarTower K L E] [FiniteDimensional K L] [FiniteDimensional K E]
    [IsGalois K L] [IsGalois K E]
    (c : groupCohomology (NK.HassePrinciple.unitsRep K L) 2)
    (v' : NK.GlobalCFT.Place L) (ŵ : NK.GlobalCFT.Place E)
    (hv : NK.GlobalCFT.Place.LiesOver ŵ v')
    (hc : (NK.HassePrinciple.locUnits K L v').hom c = 0) :
    (NK.HassePrinciple.locUnits K E ŵ).hom
      ((NK.NUV2.ARL.HR.inflation (K := K) (L := L) (E := E)).hom c) = 0 := by
  have hsq := NK.NUV2.ChebAux.Transfer.locUnits_rhoRestrict_unitsInclRepM_eq
    (K := K) (L := L) (M := K) (E := E) ŵ v' hv
  have h := congrArg (fun f => f.hom c) hsq
  simp only [ConcreteCategory.comp_apply] at h
  rw [map_rhoRestrict_self_unitsInclRepM_eq_inflation (K := K) (L := L) (E := E)] at h
  rw [h, hc]
  exact map_zero _

end NK.HR2
