import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.NK.GlobalCFTdeep.Herbrand.hOne_localUnitSubRep_of_ramificationIdx_eq_one
import Submission.NK.GlobalCFTdeep.Herbrand.localUnitsUnitsEquiv
import Submission.Work.SSGRoute.H2_coeff_transfer
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.e0b_bridge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 2000000

namespace Work.SSGRoute

open CategoryTheory

noncomputable section

/-- `Subsingleton` transfers along an isomorphism of `k`-modules, stated on the carriers with the
`Subsingleton` hypothesis *explicit*: the objects at hand appear in two definitionally equal ways
(`groupCohomology A n` and `(groupCohomology.functor k G n).obj A`) and the elaborator has to
check a definitional equality rather than run instance search. -/
theorem subsingleton_carrier_of_moduleCat_iso {k : Type*} [Ring k] {X Y : ModuleCat k}
    (e : X ≅ Y) (h : Subsingleton (↑X)) : Subsingleton (↑Y) :=
  ⟨fun y₁ y₂ => e.toLinearEquiv.symm.injective (h.allEq _ _)⟩

/-- `Subsingleton` transfers backwards along an equivalence, with the hypothesis explicit
(see `subsingleton_carrier_of_moduleCat_iso`). -/
theorem subsingleton_carrier_of_equiv {X Y : Type*} (e : X ≃ Y) (h : Subsingleton X) :
    Subsingleton Y :=
  ⟨fun y₁ y₂ => e.symm.injective (h.allEq (e.symm y₁) (e.symm y₂))⟩

/-- `NK.HassePrinciple.localUnitsSubRep` with its coefficient universe pinned to `0`
(`PTExt.Coeff = NK.HassePrinciple.CoeffInt.{0} = ULift.{0} ℤ`); without the pin the universe of
`CoeffInt` floats in the statements below. -/
abbrev hasseLocalUnitsSubRep (k L : Type) [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L] (w : NK.GlobalCFT.Place L) :
    Rep.{0} SSGRoute.PTExt.Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w) :=
  NK.HassePrinciple.localUnitsSubRep k L w

/-- **The two `𝒪_wˣ`-representations of the decomposition group have the same underlying
action.**  `NK.GlobalCFTdeep.localUnitSubRep` (`Rep ℤ`) and `NK.HassePrinciple.localUnitsSubRep`
(`Rep CoeffInt`, `CoeffInt = ULift ℤ`) have the same carrier `Additive ↥(Place.localUnits L w)`
and their actions agree pointwise, both being given on the underlying element of `L_wˣ` by the
local action of `σ` (`NK.GlobalCFTdeep.localUnitsEquiv_apply_eq`). -/
theorem localUnitSubRep_rho_eq_localUnitsSubRep {k L : Type} [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (w : NK.GlobalCFT.Place L) (σ : MulAction.stabilizer (L ≃ₐ[k] L) w)
    (a : (hasseLocalUnitsSubRep k L w).V) :
    (NK.GlobalCFTdeep.localUnitSubRep (K := k) (L := L) w).ρ σ a =
      (hasseLocalUnitsSubRep k L w).ρ σ a := by
  have hkey : ∀ u : ↥(NK.GlobalCFT.Place.localUnits L w),
      (NK.GlobalCFTdeep.instMulDistribMulActionLocalUnitsSubtype (K := k) (L := L) w).smul σ u
        = (NK.HassePrinciple.instMulDistribMulActionLocalUnitsSub
            (K := k) (L := L) w).smul σ u := by
    intro u
    apply Subtype.ext
    rw [show ((NK.GlobalCFTdeep.instMulDistribMulActionLocalUnitsSubtype
          (K := k) (L := L) w).smul σ u : (NK.GlobalCFT.Place.localField L w)ˣ)
        = Units.map (NK.GlobalCFT.Inclusion.Place.localAction σ.1 w
            (MulAction.mem_stabilizer_iff.mp σ.2)).toMonoidHom
            (u : (NK.GlobalCFT.Place.localField L w)ˣ) from rfl,
      show ((NK.HassePrinciple.instMulDistribMulActionLocalUnitsSub
          (K := k) (L := L) w).smul σ u : (NK.GlobalCFT.Place.localField L w)ˣ)
        = NK.HassePrinciple.localUnitsEquiv (K := k) w σ
            (u : (NK.GlobalCFT.Place.localField L w)ˣ) from rfl]
    exact (NK.GlobalCFTdeep.localUnitsEquiv_apply_eq (K := k) w σ _).symm
  obtain ⟨u, rfl⟩ := Additive.ofMul.surjective a
  exact congrArg Additive.ofMul (hkey u)

/-- **`H²(Γ_q, 𝒪_qˣ) = 0` for an unramified finite place**, in the normalisation
`NK.HassePrinciple.localUnitsSubRep` (`CoeffInt`-coefficients, group
`MulAction.stabilizer (L ≃ₐ[k] L) (Place.ofFinite q)`) used by the `Ext` core of `PTDefs`.

This is the local input of `eq_zero_of_isUnramifiedExt_of_unramified`: the theorem
`Commons.NumberTheory.NumberField.Completion.subsingleton_groupCohomology_two_adicIntegersUnits_of_ramificationIdx_eq_one`
computes the cohomology over `ℤ` of the local Galois representation on `𝒪_qˣ`, and it is
transported first to `NK.GlobalCFTdeep.localUnitSubRep` (along
`decompositionSubgroupIsoLocalGalois` and `localUnitSubRepIsoGeIntegersUnitsRep`) and then to
`NK.HassePrinciple.localUnitsSubRep` (change of coefficient ring `ℤ → ULift ℤ` with the same
carrier and the same action, `H2CoeffTransfer.H2_coeff_transfer`). -/
theorem subsingleton_groupCohomology_localUnitsSubRep_of_unramified
    (k L : Type) [Field k] [NumberField k] [Field L] [NumberField L] [Algebra k L]
    [FiniteDimensional k L] [IsGalois k L]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hunr : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1) :
    Subsingleton (groupCohomology
      (hasseLocalUnitsSubRep k L (NK.GlobalCFT.Place.ofFinite q)) 2) := by
  -- the local computation over `ℤ`, for the local Galois group `Gal(L_q / k_Q)`
  have h2 : Subsingleton (groupCohomology (Rep.of
      (Commons.NumberTheory.NumberField.Completion.adicIntegersUnitsRep Q q hq)) 2) :=
    Commons.NumberTheory.NumberField.Completion.subsingleton_groupCohomology_two_adicIntegersUnits_of_ramificationIdx_eq_one
      Q q hq hunr
  -- transport to the decomposition group `D_q` and the Hasse–Brauer–Noether local units
  have hgeo : Subsingleton (groupCohomology (NK.GlobalCFTdeep.localUnitSubRep
      (K := k) (L := L) (NK.GlobalCFT.Place.ofFinite q)) 2) := by
    let e := NK.GlobalCFTdeep.decompositionSubgroupIsoLocalGalois Q q hq
    let B : Rep ℤ (q.adicCompletion L ≃ₐ[Q.adicCompletion k] q.adicCompletion L) :=
      Rep.of (Commons.NumberTheory.NumberField.Completion.geIntegersUnitsRep Q q hq)
    have hB : Subsingleton (groupCohomology B 2) := h2
    haveI : Subsingleton (groupCohomology B 2) := hB
    have hres : Subsingleton (groupCohomology (Rep.res e.toMonoidHom B) 2) :=
      subsingleton_carrier_of_moduleCat_iso
        ((groupCohomology.mapIso (A := B) (B := Rep.res e.toMonoidHom B) e
          (LinearEquiv.refl ℤ B.V) (by intro g; rfl) 2).symm) hB
    haveI : Subsingleton (groupCohomology (Rep.res e.toMonoidHom B) 2) := hres
    exact subsingleton_carrier_of_moduleCat_iso
      ((groupCohomology.functor ℤ (NK.GlobalCFTdeep.decompositionSubgroup
        (NK.GlobalCFT.Place.ofFinite q)) 2).mapIso
        (NK.GlobalCFTdeep.Herbrand.localUnitSubRepIsoGeIntegersUnitsRep Q q hq)).symm hres
  haveI : Subsingleton (groupCohomology (NK.GlobalCFTdeep.localUnitSubRep
      (K := k) (L := L) (NK.GlobalCFT.Place.ofFinite q)) 2) := hgeo
  -- change of coefficient ring: same carrier, same action
  obtain ⟨E, -⟩ := H2_coeff_transfer
    (G := MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite q))
    (NK.GlobalCFTdeep.localUnitSubRep (K := k) (L := L) (NK.GlobalCFT.Place.ofFinite q))
    (hasseLocalUnitsSubRep k L (NK.GlobalCFT.Place.ofFinite q))
    (AddEquiv.refl _)
    (fun σ a => localUnitSubRep_rho_eq_localUnitsSubRep (k := k) (L := L)
      (NK.GlobalCFT.Place.ofFinite q) σ a)
  exact subsingleton_carrier_of_equiv E hgeo

/-- **`IsUnramifiedExt` classes vanish at unramified finite places.**  For a finite place `q` of `L` lying over the finite place `Q` of `k` with ramification index one (i.e. the local extension `L_q / k_Q` is unramified), any class of `H²(D_q, L_qˣ)` (with trivial coefficients) that is `IsUnramifiedExt` (i.e. comes from the local integral units `𝒪_qˣ` via `NK.HassePrinciple.localUnitsIncl`) is zero.  Local input: `H²(Γ, 𝒪_qˣ) = 0` for the unramified local extension (`Commons…subsingleton_groupCohomology_two_adicIntegersUnits_of_ramificationIdx_eq_one`, together with the identification of `NK.HassePrinciple.localUnitsSubRep` with the local `𝒪_qˣ`-representation `NK.GlobalCFTdeep.localUnitSubRep` along `decompositionSubgroupIsoLocalGalois`; note `(NK.HassePrinciple.localUnitsSubRep k L w).V = (NK.GlobalCFTdeep.localUnitSubRep k L w).V` is `rfl`), transported to `Abelian.Ext` by the bridge `Work.SSGRoute.Bridge.subsingleton_extH_of_subsingleton_groupCohomology` (`e0b_bridge.lean`) — cf. `Work.SSGRoute.E4Aux.ext_brauer_single_place` for the same style of groupCohomology-to-Ext transport. -/
theorem eq_zero_of_isUnramifiedExt_of_unramified
    (k L : Type) [Field k] [NumberField k] [Field L] [NumberField L] [Algebra k L]
    [FiniteDimensional k L] [IsGalois k L]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hunr : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1)
    (z : CategoryTheory.Abelian.Ext (SSGRoute.PTExt.unitRep
        (SSGRoute.PTExt.decompK (k := k) (K := L) (NK.GlobalCFT.Place.ofFinite q)))
      (SSGRoute.PTExt.localUnitsK (k := k) (K := L) (NK.GlobalCFT.Place.ofFinite q)) 2)
    (hz : SSGRoute.PTExt.IsUnramifiedExt (k := k) (K := L)
      (NK.GlobalCFT.Place.ofFinite q) z) : z = 0 := by
  have hloc : Subsingleton (groupCohomology
      (NK.HassePrinciple.localUnitsSubRep k L (NK.GlobalCFT.Place.ofFinite q)) 2) :=
    subsingleton_groupCohomology_localUnitsSubRep_of_unramified k L q Q hq hunr
  haveI : Subsingleton (SSGRoute.PTExt.extH
      (NK.HassePrinciple.localUnitsSubRep k L (NK.GlobalCFT.Place.ofFinite q)) 2) :=
    Bridge.subsingleton_extH_of_subsingleton_groupCohomology 2 _
      (NK.HassePrinciple.localUnitsSubRep k L (NK.GlobalCFT.Place.ofFinite q)) hloc
  obtain ⟨z', hz'⟩ := hz
  have hz'0 : z' = 0 := Subsingleton.elim z' 0
  rw [hz', hz'0]
  simp

end

end Work.SSGRoute
