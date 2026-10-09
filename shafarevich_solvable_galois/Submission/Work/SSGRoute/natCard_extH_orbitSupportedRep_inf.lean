import Mathlib
import Submission.Work.SSGRoute.ec_defs
import Submission.Work.SSGRoute.natCard_extH_orbitSupportedRep
import Submission.Work.SSGRoute.ext_localUnits_pTorsion
import Submission.Work.SSGRoute.e0b_bridge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

set_option maxHeartbeats 3200000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

attribute [local instance 10000] Rep.hV2 Rep.hV1

/-- **The local input at an infinite place, in `groupCohomology` vocabulary.**

`Work.SSGRoute.natCard_extH_localUnits_deep_ofInfinite` gives
`#H²(D_w, L_wˣ) = #D_w` in the `Ext` core; composing with the user-written bridge
`Work.SSGRoute.Bridge.E` (`H²(G,A) ≃+ Ext²_G(ℤ,A)`) and observing that
`NK.GlobalCFTdeep.decompositionSubgroup` is definitionally `MulAction.stabilizer` at the level of
cardinalities (both are `Nat.card` of `{σ // σ • w = w}`) yields the same statement for
`groupCohomology`, matching the form of the finite-place input `eb_loc_card`. -/
theorem natCard_groupCohomology_localUnits_ofInfinite (k L : Type) [Field k] [NumberField k]
    [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (w₀ : NumberField.InfinitePlace L) :
    Nat.card (groupCohomology (NK.HassePrinciple.localUnitsRep k L
      (NK.GlobalCFT.Place.ofInfinite w₀)) 2)
      = Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofInfinite w₀)) := by
  have hbridge : Nat.card (groupCohomology (NK.HassePrinciple.localUnitsRep k L
        (NK.GlobalCFT.Place.ofInfinite w₀)) 2)
      = Nat.card (extH (localUnitsK (k := k) (NK.GlobalCFT.Place.ofInfinite w₀)) 2) :=
    Nat.card_congr (Bridge.E 2 (decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w₀))
      (localUnitsK (k := k) (NK.GlobalCFT.Place.ofInfinite w₀))).toEquiv
  have hdeep := natCard_extH_localUnits_deep_ofInfinite k L w₀
  have hstab : Nat.card ↥(NK.GlobalCFTdeep.decompositionSubgroup (K := k) (L := L)
        (NK.GlobalCFT.Place.ofInfinite w₀))
      = Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofInfinite w₀)) := rfl
  rw [hbridge, hdeep, hstab]

/-- **The second `Ext`-cohomology of the idèles supported on one orbit — at an infinite place.**

`CardOrbitSupportedRep`/`natCard_extH_orbitSupportedRep` handle a *finite* place `ŵ₀`; here `w₀` is
an **infinite** place.  The argument is verbatim the finite-place one — the orbit-supported idèles
`W = orbitSupportedRep k L (Place.ofInfinite w₀)` are the coinduced module
`Coind_D^{Gal(L/k)} L_{w₀}ˣ` for the decomposition group `D = Stab(w₀)`
(`orbitCoindMapA` is an isomorphism, split by `coindSectionHom`), so Shapiro's lemma gives
`H²(Gal(L/k), W) ≅ H²(D, L_{w₀}ˣ)` — only the local input changes: at an infinite place the local
Brauer group `H²(D_w, L_wˣ)` has order `#D_w` by
`Work.SSGRoute.natCard_extH_localUnits_deep_ofInfinite` (here `#D_w ≤ 2`). -/
theorem natCard_extH_orbitSupportedRep_inf (k L : Type) [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (w₀ : NumberField.InfinitePlace L) :
    Nat.card (SSGRoute.PTExt.extH (Work.SSGRoute.orbitSupportedRep k L
      (NK.GlobalCFT.Place.ofInfinite w₀)) 2)
      = Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofInfinite w₀)) := by
  classical
  set w : NK.GlobalCFT.Place L := NK.GlobalCFT.Place.ofInfinite w₀ with hw
  change Nat.card (SSGRoute.PTExt.extH (NK.HassePrinciple.supportedRep k L
      (NK.HassePrinciple.orbitStable k L w)) 2)
    = Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w)
  -- ### Step 1. `W ≅ Coind_D^G L_{w}ˣ`.
  have hhom_inv : NK.HassePrinciple.orbitCoindMapA k L w ≫
      NK.HassePrinciple.coindSectionHom (K := k) (L := L) w =
        𝟙 (NK.HassePrinciple.supportedRep k L (NK.HassePrinciple.orbitStable k L w)) :=
    NK.HassePrinciple.orbitCoindMapA_comp_coindSectionHom w
  have hinv_hom : NK.HassePrinciple.coindSectionHom (K := k) (L := L) w ≫
      NK.HassePrinciple.orbitCoindMapA k L w =
        𝟙 (Rep.coind (MulAction.stabilizer (L ≃ₐ[k] L) w).subtype
          (NK.HassePrinciple.localUnitsRep k L w)) := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro f
    show (NK.HassePrinciple.orbitCoindMapA k L w)
      ((NK.HassePrinciple.coindSectionHom (K := k) (L := L) w) f) = f
    exact NK.HassePrinciple.orbitCoindMapA_comp_coindSection w f
  let eOrb := CategoryTheory.Iso.mk
      (NK.HassePrinciple.orbitCoindMapA k L w)
      (NK.HassePrinciple.coindSectionHom (K := k) (L := L) w)
      hhom_inv hinv_hom
  -- ### Step 2. Transport `groupCohomology` along that isomorphism.
  have hiso : Nat.card (groupCohomology (NK.HassePrinciple.supportedRep k L
        (NK.HassePrinciple.orbitStable k L w)) 2)
      = Nat.card (groupCohomology (Rep.coind
          (MulAction.stabilizer (L ≃ₐ[k] L) w).subtype
          (NK.HassePrinciple.localUnitsRep k L w)) 2) := by
    have h := Nat.card_congr (Iso.toLinearEquiv
      ((groupCohomology.functor Coeff (L ≃ₐ[k] L) 2).mapIso eOrb)).toEquiv
    simpa only [groupCohomology.functor_obj] using h
  -- ### Step 3. Shapiro's lemma for group cohomology.
  have hshapiro : Nat.card (groupCohomology (Rep.coind
        (MulAction.stabilizer (L ≃ₐ[k] L) w).subtype
        (NK.HassePrinciple.localUnitsRep k L w)) 2)
      = Nat.card (groupCohomology (NK.HassePrinciple.localUnitsRep k L w) 2) :=
    Nat.card_congr (Iso.toLinearEquiv (groupCohomology.coindIso
      (k := Coeff) (S := MulAction.stabilizer (L ≃ₐ[k] L) w)
      (NK.HassePrinciple.localUnitsRep k L w) 2)).toEquiv
  -- ### Step 4. The local input at the infinite place `w`.
  have hloc : Nat.card (groupCohomology (NK.HassePrinciple.localUnitsRep k L w) 2)
      = Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w) :=
    natCard_groupCohomology_localUnits_ofInfinite k L w₀
  -- ### Step 5. The `E0b` comparison `extH ≃+ groupCohomology`.
  have hbridge : Nat.card (extH (NK.HassePrinciple.supportedRep k L
        (NK.HassePrinciple.orbitStable k L w)) 2)
      = Nat.card (groupCohomology (NK.HassePrinciple.supportedRep k L
        (NK.HassePrinciple.orbitStable k L w)) 2) :=
    (Nat.card_congr (Bridge.E 2 (L ≃ₐ[k] L)
      (NK.HassePrinciple.supportedRep k L (NK.HassePrinciple.orbitStable k L w))).toEquiv).symm
  rw [hbridge, hiso, hshapiro]
  exact hloc

end Work.SSGRoute
