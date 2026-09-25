import Mathlib
import Submission.NK.CFTLib.RouteB.plan
import Submission.NK.CFTLib.fundamentalClassInputs
import Submission.NK.CFTLib.RouteB.exists_iso_rep_res_autCongr
import Submission.NK.HassePrinciple.repIso_quotientToInvariants_fixedField
import Submission.NK.GlobalCFTdeep.H1All
import Submission.Commons.RepresentationTheory.GroupCohomology.natCard_nsmul_H2_eq_zero
import Submission.Commons.RepresentationTheory.GroupCohomology.exists_addOrderOf_eq_of_inf_range_le_ker_res

/-!
# The transfer of the fundamental class along the auxiliary tower (Route B, lemma 3)

This is the last assembly step of the reduction recorded in `RouteB/plan.lean`.  Given the
auxiliary tower (a normal subgroup `Nsub ≤ Gal(Ω/K)` whose fixed field is `K`-isomorphic to `L`, and
a normal subgroup `Msub`), an element `x` of order `n = [L:K]` in `H²(Gal(Ω/K) ⧸ Msub, C_Ω^{Msub})`,
together with the comparison `range(inf_{Msub}) ≤ ker(res_{Nsub})`, the abstract twist lemma

`Commons.RepresentationTheory.GroupCohomology.exists_addOrderOf_eq_of_inf_range_le_ker_res`

produces an element `y` of order `n` in `H²(Gal(Ω/K) ⧸ Nsub, C_Ω^{Nsub})`; the conclusion then
transports `y` to

`H²(Gal(L/K), C_L)`

along

* `NK.HassePrinciple.repIso_quotientToInvariants_fixedField Nsub` (`C_Ω^{Nsub} ≅ C_{Ω^{Nsub}}`
  equivariantly) together with `IsGalois.normalAutEquivQuotient Nsub`
  (`Gal(Ω/K) ⧸ Nsub ≅ Gal(Ω^{Nsub}/K)`), and
* `NK.CFTLib.RouteB.exists_iso_rep_res_autCongr e` (transport of `C_•` along `e`).

Every map in the chain is an isomorphism of `ℤ`-modules, hence preserves `addOrderOf`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped NumberField
open CategoryTheory

namespace NK.CFTLib.GFC

theorem exists_addOrderOf_eq_card_of_auxiliary {K L Ω : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Field Ω]
    [NumberField Ω] [Algebra K Ω] [FiniteDimensional K Ω] [IsGalois K Ω]
    (Msub Nsub : Subgroup Gal(Ω/K)) [Msub.Normal] [Nsub.Normal]
    (e : ↥(IntermediateField.fixedField Nsub) ≃ₐ[K] L)
    (hcardN : Nat.card (Gal(Ω/K) ⧸ Nsub) = Nat.card Gal(L/K))
    (x : groupCohomology ((NK.GlobalCFT.IdeleClassGroup.rep K Ω).quotientToInvariants Msub) 2)
    (hx : addOrderOf x = Nat.card Gal(L/K))
    (hle : LinearMap.range
        ((groupCohomology.infNatTrans ℤ Msub 2).app (NK.GlobalCFT.IdeleClassGroup.rep K Ω)).hom ≤
      LinearMap.ker
        ((groupCohomology.resNatTrans ℤ (G := Nsub) (H := Gal(Ω/K)) Nsub.subtype 2).app
          (NK.GlobalCFT.IdeleClassGroup.rep K Ω)).hom) :
    ∃ α : groupCohomology (NK.GlobalCFT.IdeleClassGroup.rep K L) 2,
      addOrderOf α = Nat.card Gal(L/K) := by
  classical
  -- `H¹` vanishes for every subgroup of `Gal(Ω/K)`.
  have h1M : Subsingleton (groupCohomology
      (Rep.res Msub.subtype (NK.GlobalCFT.IdeleClassGroup.rep K Ω)) 1) :=
    NK.GlobalCFTdeep.subsingleton_groupCohomology_one_res_ideleClassGroup (K := K) (L := Ω) Msub
  have h1N : Subsingleton (groupCohomology
      (Rep.res Nsub.subtype (NK.GlobalCFT.IdeleClassGroup.rep K Ω)) 1) :=
    NK.GlobalCFTdeep.subsingleton_groupCohomology_one_res_ideleClassGroup (K := K) (L := Ω) Nsub
  -- The exponent of `H²(Gal(Ω/K) ⧸ Nsub, C_Ω^{Nsub})` divides the order of the group.
  have hkill : ∀ y : groupCohomology
      ((NK.GlobalCFT.IdeleClassGroup.rep K Ω).quotientToInvariants Nsub) 2,
      addOrderOf y ∣ Nat.card Gal(L/K) := by
    intro y
    haveI : Fintype (Gal(Ω/K) ⧸ Nsub) := Fintype.ofFinite _
    have h1 := Commons.RepresentationTheory.GroupCohomology.natCard_nsmul_H2_eq_zero
      ((NK.GlobalCFT.IdeleClassGroup.rep K Ω).quotientToInvariants Nsub) y
    rw [addOrderOf_dvd_iff_nsmul_eq_zero, ← hcardN]
    exact h1
  -- The abstract twist.
  obtain ⟨y, hy⟩ :=
    Commons.RepresentationTheory.GroupCohomology.exists_addOrderOf_eq_of_inf_range_le_ker_res
      Msub Nsub (NK.GlobalCFT.IdeleClassGroup.rep K Ω) h1M h1N hle (Nat.card Gal(L/K)) hkill x hx
  -- The transport of `y` to `H²(Gal(L/K), C_L)`.
  let F := ↥(IntermediateField.fixedField Nsub)
  haveI : NumberField F := inferInstance
  let φ : Gal(Ω/K) ⧸ Nsub ≃* Gal(F/K) := IsGalois.normalAutEquivQuotient Nsub
  let ψ : Gal(F/K) ≃* Gal(L/K) := AlgEquiv.autCongr e
  obtain ⟨hiso1⟩ :=
    NK.HassePrinciple.repIso_quotientToInvariants_fixedField (K := K) (L := Ω) Nsub
  obtain ⟨hiso3⟩ := NK.CFTLib.RouteB.exists_iso_rep_res_autCongr e
  have e1 : groupCohomology
        ((NK.GlobalCFT.IdeleClassGroup.rep K Ω).quotientToInvariants Nsub) 2 ≅
      groupCohomology (Rep.res φ.toMonoidHom (NK.GlobalCFT.IdeleClassGroup.rep K F)) 2 :=
    (groupCohomology.functor ℤ (Gal(Ω/K) ⧸ Nsub) 2).mapIso hiso1
  have e2 : groupCohomology (Rep.res φ.toMonoidHom (NK.GlobalCFT.IdeleClassGroup.rep K F)) 2 ≅
      groupCohomology (NK.GlobalCFT.IdeleClassGroup.rep K F) 2 :=
    groupCohomology.mapIso φ (LinearEquiv.refl ℤ _) (by intro g; rfl) 2
  have e3 : groupCohomology (Rep.res ψ.toMonoidHom (NK.GlobalCFT.IdeleClassGroup.rep K L)) 2 ≅
      groupCohomology (NK.GlobalCFT.IdeleClassGroup.rep K F) 2 :=
    (groupCohomology.functor ℤ (Gal(F/K)) 2).mapIso hiso3
  have e4 : groupCohomology (Rep.res ψ.toMonoidHom (NK.GlobalCFT.IdeleClassGroup.rep K L)) 2 ≅
      groupCohomology (NK.GlobalCFT.IdeleClassGroup.rep K L) 2 :=
    groupCohomology.mapIso ψ (LinearEquiv.refl ℤ _) (by intro g; rfl) 2
  refine ⟨(e1 ≪≫ e2 ≪≫ e3.symm ≪≫ e4).toLinearEquiv y, ?_⟩
  exact (AddEquiv.addOrderOf_eq (e1 ≪≫ e2 ≪≫ e3.symm ≪≫ e4).toLinearEquiv.toAddEquiv y).trans hy

end NK.CFTLib.GFC
