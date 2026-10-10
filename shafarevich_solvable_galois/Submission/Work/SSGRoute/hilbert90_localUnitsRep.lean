import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Submission.NK.GlobalCFTdeep.Herbrand.hOne_fiberIdelesRep_eq_one
import Submission.NK.HassePrinciple.subsingleton_classGroupRep_one
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open CategoryTheory

set_option linter.style.haveILetI false

/-- **Hilbert 90 for the local units at an arbitrary level and an arbitrary subgroup of the
decomposition group.**  For a finite Galois extension `L/k` of number fields, a place `w` of `L`
and a subgroup `N` of the stabiliser `D_w = MulAction.stabilizer (L ≃ₐ[k] L) w`, the first
group cohomology of `N` with coefficients in the local units `L_wˣ` (with the action through
`NK.HassePrinciple.localUnitsRep k L w`, restricted to `N`) vanishes.

Indeed `N` is the Galois group of the finite Galois extension `L_w/(L_w)^N` of local fields
(`localAutHom` and `localAutHom_injective` identify `N` with a group of `k_v`-algebra automorphisms
of `L_w`), so this is the classical Hilbert 90 for the units of a finite Galois extension of
fields, exactly as in `Work.SSGRoute.hilbert90_localUnits_extH` (which is the case
`L = K`, `N = D_w`), via
`NK.GlobalCFTdeep.Herbrand.subsingleton_groupCohomology_one_of_injective_ringAut` and
`NK.HassePrinciple.subsingleton_groupCohomology_one_of_mulCoboundary`. -/
theorem hilbert90_localUnitsRep {k L : Type} [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (w : NK.GlobalCFT.Place L) (N : Subgroup (MulAction.stabilizer (L ≃ₐ[k] L) w)) :
    Subsingleton (groupCohomology
      (Rep.res N.subtype (NK.HassePrinciple.localUnitsRep k L w)) 1) := by
  -- `N` is finite (it is a subgroup of the finite group `D_w`).
  haveI : Fintype N := Fintype.ofFinite _
  -- Hilbert 90 for the action of `N` on `L_wˣ` through the faithful map `localAutHom ∘ N.subtype`.
  have hfaithful : Subsingleton (groupCohomology
      (Rep.ofMulDistribMulAction N ((NK.GlobalCFT.Place.localField L w)ˣ)) 1) :=
    NK.GlobalCFTdeep.Herbrand.subsingleton_groupCohomology_one_of_injective_ringAut
      (G := N) (F := NK.GlobalCFT.Place.localField L w)
      ((NK.HassePrinciple.localAutHom (K := k) (L := L) w).comp N.subtype)
      (fun a b h => Subtype.ext ((NK.HassePrinciple.localAutHom_injective (K := k) (L := L) w) h))
      (fun σ u => rfl)
  have hcob := NK.HassePrinciple.mulCoboundary_of_subsingleton_groupCohomology_one hfaithful
  -- Transfer to the coefficient ring `CoeffInt`.
  haveI hCoeff : Subsingleton (groupCohomology
      (Rep.ofDistribMulAction NK.HassePrinciple.CoeffInt N
        (Additive (NK.GlobalCFT.Place.localField L w)ˣ)) 1) :=
    NK.HassePrinciple.subsingleton_groupCohomology_one_of_mulCoboundary
      NK.HassePrinciple.CoeffInt hcob
  -- The restricted representation `Rep.res N.subtype (localUnitsRep k L w)` and the canonical
  -- `CoeffInt`-linear representation on the same carrier have the same action, pointwise.
  have hρ : ∀ g : N, (Rep.ofDistribMulAction NK.HassePrinciple.CoeffInt N
        (Additive (NK.GlobalCFT.Place.localField L w)ˣ)).ρ g =
      (Rep.res N.subtype (NK.HassePrinciple.localUnitsRep k L w)).ρ g := by
    intro g
    apply LinearMap.ext
    intro a
    obtain ⟨u, rfl⟩ := Additive.ofMul.surjective a
    rfl
  -- Hence the two cohomology modules are isomorphic, and `H¹` transfers.
  have hIso : groupCohomology (Rep.res N.subtype (NK.HassePrinciple.localUnitsRep k L w)) 1 ≅
      groupCohomology (Rep.ofDistribMulAction NK.HassePrinciple.CoeffInt N
        (Additive (NK.GlobalCFT.Place.localField L w)ˣ)) 1 :=
    groupCohomology.mapIso (MulEquiv.refl N)
      (LinearEquiv.refl NK.HassePrinciple.CoeffInt
        (Additive (NK.GlobalCFT.Place.localField L w)ˣ))
      (fun g => (hρ g).symm) 1
  exact ⟨fun a b => (hIso.toLinearEquiv).injective (Subsingleton.elim _ _)⟩

end Work.SSGRoute
