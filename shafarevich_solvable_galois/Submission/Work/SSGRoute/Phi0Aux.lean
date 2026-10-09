import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.e0b_bridge
import Submission.Work.SSGRoute.E0bBarChange
import Submission.Work.SSGRoute.ExtH1Iso
import Submission.NK.GlobalCFTdeep.HasseNormTheorem
import Submission.NK.HassePrinciple.subsingleton_classGroupRep_one
import Submission.NK.HassePrinciple.subsingleton_groupCohomology_one_unitsRep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliary vocabulary for E4Ω-R1 (`phi0_family_vanish_of_local`)

The lemma `Work.SSGRoute.phi0_family_vanish_of_local` needs the two CFT inputs of global class
field theory that NK proves in the `groupCohomology` world, read in the `Ext` core of `PTDefs`:

* the relative Hasse–Brauer–Noether theorem (`NK.GlobalCFTdeep.hbnUnits`), transferred along the
  comparison `bridgeE : Hⁿ(G, A) ≃+ Extⁿ_G(ℤ, A)`;
* the injectivity of the inflation `H²(Gal(L/k), C_L) → H²(Gal(L'/k), C_{L'})`
  (`Commons…H2_inflation_injective_of_subsingleton_H1` + `H¹(Γ, C_L) = 0`), likewise transferred.

This file sets up the comparison `bridgeE` (together with its computation rule on the class of a
cocycle, which is what any transfer of a *named* map along it needs) and records the degree-one
vanishing that transfers for free (an isomorphism transports `Subsingleton`).
-/

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory
open scoped Classical

noncomputable section

/-- **The comparison `Hⁿ(G, A) ≅ Hⁿ(Hom(barComplex, A))`** obtained from the identification of
the complex of inhomogeneous cochains with the complex of morphisms out of the bar resolution
(Mathlib's `groupCohomology.inhomogeneousCochainsIso`).  Written this way (rather than through
`groupCohomologyIso`) so that the value on the class of a cocycle can be computed. -/
def thetaHom (G : Type) [Group G] (A : Rep.{0, 0, 0} Coeff G) (n : ℕ) :
    groupCohomology A n ≃+ ((Rep.barComplex Coeff G).linearYonedaObj Coeff A).homology n :=
  ((HomologicalComplex.homologyMapIso (groupCohomology.inhomogeneousCochainsIso A) n).toLinearEquiv).toAddEquiv

/-- **The bridge `Hⁿ(G, A) ≃+ Extⁿ_G(ℤ, A)`** of node E0b, in a form whose computation rule on
the class of a cocycle is available (`thetaHom_spec`, `Bridge.Psi_spec`). -/
def bridgeE (G : Type) [Group G] (A : Rep.{0, 0, 0} Coeff G) (n : ℕ) :
    groupCohomology A n ≃+ extH A n :=
  (thetaHom G A n).trans (Bridge.Psi n G A)

/-- **`H¹(Gal(L/k), Lˣ) = 0` read in the `Ext` core** (Noether's generalisation of Hilbert 90,
`NK.HassePrinciple.subsingleton_groupCohomology_one_unitsRep`, transported along the bridge). -/
theorem subsingleton_extH_unitsK_one (k L : Type) [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [IsGalois k L] :
    Subsingleton (extH (unitsK k L) 1) :=
  Bridge.subsingleton_extH_of_subsingleton_groupCohomology 1 (L ≃ₐ[k] L) (unitsK k L)
    (NK.HassePrinciple.subsingleton_groupCohomology_one_unitsRep (K := k) (L := L))

/-- **`H¹(Gal(L/k), C_L) = 0` read in the `Ext` core**
(`NK.HassePrinciple.subsingleton_classGroupRep_one`, transported along the bridge). -/
theorem subsingleton_extH_classesK_one (k L : Type) [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L] :
    Subsingleton (extH (classesK k L) 1) :=
  Bridge.subsingleton_extH_of_subsingleton_groupCohomology 1 (L ≃ₐ[k] L) (classesK k L)
    (NK.HassePrinciple.subsingleton_classGroupRep_one NK.GlobalCFTdeep.cyclicHasseInput)

end

end Work.SSGRoute
