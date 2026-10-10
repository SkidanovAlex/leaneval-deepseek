import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Submission.Work.SSGRoute.e0b_bridge
import Submission.Work.SSGRoute.hilbert90_localUnitsRep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open CategoryTheory

/-- **Hilbert 90 for the local units at the full decomposition group, read in the `Ext` core.**
For a finite Galois extension `K/k` of number fields and a place `w` of `K`, the first cohomology
of the decomposition group `D_w` with coefficients in the local units `K_wˣ` vanishes:
`H¹(D_w, K_wˣ) = 0`.  (The case `N = ⊤` of `Work.SSGRoute.hilbert90_localUnitsRep`, transported
along the bridge `Hⁿ(G, A) ≃ Extⁿ_G(ℤ, A)`.) -/
theorem subsingleton_extH_localUnitsK_one (k K : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K) :
    Subsingleton (SSGRoute.PTExt.extH (SSGRoute.PTExt.localUnitsK (k := k) w) 1) := by
  -- Hilbert 90 over the top subgroup of `D_w` (which is `D_w` itself).
  have htop : Subsingleton (groupCohomology
      ((Rep.res (⊤ : Subgroup (SSGRoute.PTExt.decompK (k := k) w)).subtype
        (NK.HassePrinciple.localUnitsRep k K w))) 1) :=
    Work.SSGRoute.hilbert90_localUnitsRep (k := k) (L := K) w ⊤
  -- Transport along `⊤ ≃* D_w`: the restricted representation at the top subgroup is the
  -- representation itself.
  have hiso : Subsingleton (groupCohomology (SSGRoute.PTExt.localUnitsK (k := k) w) 1) := by
    have h := groupCohomology.mapIso
      (G := ↥(⊤ : Subgroup (SSGRoute.PTExt.decompK (k := k) w)))
      (H := ↥(SSGRoute.PTExt.decompK (k := k) w))
      (A := SSGRoute.PTExt.localUnitsK (k := k) w)
      (B := Rep.res (⊤ : Subgroup (SSGRoute.PTExt.decompK (k := k) w)).subtype
        (NK.HassePrinciple.localUnitsRep k K w))
      Subgroup.topEquiv
      (LinearEquiv.refl SSGRoute.PTExt.Coeff
        (Additive (NK.GlobalCFT.Place.localField K w)ˣ))
      (fun g => LinearMap.ext (fun x => rfl)) 1
    exact ⟨fun a b => h.toLinearEquiv.symm.injective
      (htop.elim (h.toLinearEquiv.symm a) (h.toLinearEquiv.symm b))⟩
  -- Bridge to the `Ext` core.
  exact Work.SSGRoute.Bridge.subsingleton_extH_of_subsingleton_groupCohomology 1
    (SSGRoute.PTExt.decompK (k := k) w) (SSGRoute.PTExt.localUnitsK (k := k) w) hiso

end Work.SSGRoute
