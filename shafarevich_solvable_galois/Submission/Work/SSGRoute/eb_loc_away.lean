import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Submission.NK.CFTLib.HR.TransferAux.descent
import Submission.NK.HR2.locUnits_inflation_eq_zero_iff
import Submission.NK.HR2.locUnits_inflation_eq_zero_of_loc_eq_zero
import Submission.Work.SSGRoute.eb_locUnits_resToGal
import Submission.Work.SSGRoute.phi1_level_naturality
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- **Localisation away from the special place (E8' helper).** Let `k ⊆ L`, `k ⊆ M`, `k ⊆ E` be a tower of Galois number-field extensions with `E/M` Galois, let `a ∈ H²(Gal(L/k), Lˣ)`, and let `r` be a place of `L` below a place `ŵ` of `E` at which the localisation of `a` vanishes. Then the localisation at `ŵ` of `res_{E/M}(inf_E a)` vanishes. -/
theorem eb_loc_away {k L M E : Type} [Field k] [NumberField k] [Field L] [NumberField L] [Field M] [NumberField M] [Field E] [NumberField E] [Algebra k L] [Algebra k M] [Algebra k E] [Algebra L E] [Algebra M E] [IsScalarTower k L E] [IsScalarTower k M E] [FiniteDimensional k L] [FiniteDimensional k M] [FiniteDimensional k E] [IsGalois k L] [IsGalois k M] [IsGalois k E] [FiniteDimensional M E] [IsGalois M E] (a : groupCohomology (NK.HassePrinciple.unitsRep k L) 2) (ŵ : NK.GlobalCFT.Place E) (r : NK.GlobalCFT.Place L) (hLies : NK.GlobalCFT.Place.LiesOver ŵ r) (ha : (NK.HassePrinciple.locUnits k L r).hom a = 0) : (NK.HassePrinciple.locUnits M E ŵ).hom ((NK.NUV2.ChebAux.Transfer.resToGal k M E).hom ((NK.NUV2.ARL.HR.inflation (K := k) (L := L) (E := E)).hom a)) = 0 := by
  have hE : (NK.HassePrinciple.locUnits k E ŵ).hom
      ((NK.NUV2.ARL.HR.inflation (K := k) (L := L) (E := E)).hom a) = 0 :=
    NK.HR2.locUnits_inflation_eq_zero_of_loc_eq_zero (K := k) (L := L) (E := E) a r ŵ hLies ha
  rw [Work.SSGRoute.eb_locUnits_resToGal (k := k) (M := M) (E := E) ŵ
    ((NK.NUV2.ARL.HR.inflation (K := k) (L := L) (E := E)).hom a)]
  rw [hE]
  exact map_zero _

end Work.SSGRoute
