import Mathlib.Tactic.Have
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.e0b_bridge
import Submission.Work.SSGRoute.eb_loc_card
import Submission.Work.SSGRoute.ec_defs
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


/-- **The second `Ext`-cohomology of the idèles supported on one orbit.**

`CardOrbitSupportedRep k L ŵ₀` (defined in `Submission.Work.SSGRoute.ec_defs`) states
`Nat.card (extH (orbitSupportedRep k L (Place.ofFinite ŵ₀)) 2) = Nat.card (Stab_{Gal(L/k)}(ŵ₀))`,
where `orbitSupportedRep k L w := NK.HassePrinciple.supportedRep k L (orbitStable k L w)` is the
`Gal(L/k)`-module of idèles supported on the orbit of `w` (all components outside the orbit are
`1`).  Here `ŵ₀` is a **finite** place, so that the local input `Work.SSGRoute.eb_loc_card`
(`EB_LocCard`) applies.

Indeed `W := orbitSupportedRep k L (Place.ofFinite ŵ₀)` is the coinduced module
`Coind_D^{Gal(L/k)} L_{w₀}ˣ` for the decomposition group `D = Mulaction.stabilizer (L ≃ₐ[k] L) w₀`
(`NK.HassePrinciple.orbitCoindMapA` is an isomorphism: injective by
`NK.HassePrinciple.orbitCoindMapA_injective` and split by
`NK.HassePrinciple.orbitCoindMapA_comp_coindSectionHom`), so by Shapiro's lemma
`H²(Gal(L/k), W) ≅ H²(D, L_{w₀}ˣ)`, which is cyclic of order `|D|` (`EB_LocCard`).

Route: the `E0b` bridge `Work.SSGRoute.E0bGroupCoeff.eBridge` identifies `extH W 2` with
`groupCohomology W 2`; transport along the isomorphism `W ≅ Coind_D^{Gal(L/k)} L_{w₀}ˣ` and Shapiro
(`groupCohomology.coindIso`); conclude with `Work.SSGRoute.eb_loc_card`
(`NK.HassePrinciple.localUnitsRep k L w₀` is `localUnitsK k L w₀`, and `decompK w₀` is
`MulAction.stabilizer (L ≃ₐ[k] L) w₀`). -/
theorem natCard_extH_orbitSupportedRep (k L : Type) [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (ŵ₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    CardOrbitSupportedRep k L ŵ₀ := by
  classical
  unfold CardOrbitSupportedRep
  set w₀ : NK.GlobalCFT.Place L := NK.GlobalCFT.Place.ofFinite ŵ₀ with hw₀
  -- ### Step 1. `W ≅ Coind_D^G L_{w₀}ˣ`: `orbitCoindMapA` is the Shapiro comparison and
  -- `coindSectionHom` its inverse (both composites are on disk).
  have hhom_inv : NK.HassePrinciple.orbitCoindMapA k L w₀ ≫
      NK.HassePrinciple.coindSectionHom (K := k) (L := L) w₀ =
        𝟙 (NK.HassePrinciple.supportedRep k L (NK.HassePrinciple.orbitStable k L w₀)) :=
    NK.HassePrinciple.orbitCoindMapA_comp_coindSectionHom w₀
  have hinv_hom : NK.HassePrinciple.coindSectionHom (K := k) (L := L) w₀ ≫
      NK.HassePrinciple.orbitCoindMapA k L w₀ =
        𝟙 (Rep.coind (MulAction.stabilizer (L ≃ₐ[k] L) w₀).subtype
          (NK.HassePrinciple.localUnitsRep k L w₀)) := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro f
    show (NK.HassePrinciple.orbitCoindMapA k L w₀)
      ((NK.HassePrinciple.coindSectionHom (K := k) (L := L) w₀) f) = f
    exact NK.HassePrinciple.orbitCoindMapA_comp_coindSection w₀ f
  let eOrb := CategoryTheory.Iso.mk
      (NK.HassePrinciple.orbitCoindMapA k L w₀)
      (NK.HassePrinciple.coindSectionHom (K := k) (L := L) w₀)
      hhom_inv hinv_hom
  -- ### Step 2. Transport `groupCohomology` along that isomorphism.
  have hiso : Nat.card (groupCohomology (NK.HassePrinciple.supportedRep k L
        (NK.HassePrinciple.orbitStable k L w₀)) 2)
      = Nat.card (groupCohomology (Rep.coind
          (MulAction.stabilizer (L ≃ₐ[k] L) w₀).subtype
          (NK.HassePrinciple.localUnitsRep k L w₀)) 2) := by
    have h := Nat.card_congr (Iso.toLinearEquiv
      ((groupCohomology.functor Coeff (L ≃ₐ[k] L) 2).mapIso eOrb)).toEquiv
    simpa only [groupCohomology.functor_obj] using h
  -- ### Step 3. Shapiro's lemma for group cohomology.
  have hshapiro : Nat.card (groupCohomology (Rep.coind
        (MulAction.stabilizer (L ≃ₐ[k] L) w₀).subtype
        (NK.HassePrinciple.localUnitsRep k L w₀)) 2)
      = Nat.card (groupCohomology (NK.HassePrinciple.localUnitsRep k L w₀) 2) :=
    Nat.card_congr (Iso.toLinearEquiv (groupCohomology.coindIso
      (k := Coeff) (S := MulAction.stabilizer (L ≃ₐ[k] L) w₀)
      (NK.HassePrinciple.localUnitsRep k L w₀) 2)).toEquiv
  -- ### Step 4. The local input `EB_LocCard` at the finite place `ŵ₀`.
  have hloc : Nat.card (groupCohomology (NK.HassePrinciple.localUnitsRep k L w₀) 2)
      = Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w₀) := by
    have h := (eb_loc_card k k L ŵ₀).1
    rw [← hw₀] at h
    exact h
  -- ### Step 5. The `E0b` comparison `extH ≃+ groupCohomology`.
  have hbridge : Nat.card (extH (NK.HassePrinciple.supportedRep k L
        (NK.HassePrinciple.orbitStable k L w₀)) 2)
      = Nat.card (groupCohomology (NK.HassePrinciple.supportedRep k L
        (NK.HassePrinciple.orbitStable k L w₀)) 2) :=
    (Nat.card_congr (Bridge.E 2 (L ≃ₐ[k] L)
      (NK.HassePrinciple.supportedRep k L (NK.HassePrinciple.orbitStable k L w₀))).toEquiv).symm
  rw [hbridge, hiso, hshapiro]
  exact hloc

end Work.SSGRoute
