import Mathlib
import Submission.NK.CFTLib.RouteB.plan
import Submission.NK.CFTLib.fundamentalClassInputs
import Submission.NK.HassePrinciple.repIso_quotientToInvariants_fixedField

/-!
# The M-level fundamental class of the auxiliary tower (Route B, lemma 2)

`NK.CFTLib.RouteB.exists_element_of_order_card_of_auxiliary`: given the auxiliary tower
(`Msub`, `Nsub ≤ Gal(Ω/K)` with `Gal(Ω/K) ⧸ Msub` cyclic of order `Nat.card Gal(L/K)` and the
fixed fields of `Msub`, `Nsub` complementary), the arithmetic input `hpp` produces an element of
order `Nat.card Gal(L/K)` in `H²(Gal(Ω/K) ⧸ Msub, C_Ω^{Msub})`.

The fixed field `M = Ω^{Msub}` is cyclic over `K` of degree `n = Nat.card Gal(L/K)`, and
`C_Ω^{Msub} ≅ C_M` equivariantly (`repIso_quotientToInvariants_fixedField`); the cyclic case of the
fundamental class (`exists_fundamentalClass_of_isCyclic`) therefore applies at the level `M/K`, and
we transport the resulting class back along
`Gal(Ω/K) ⧸ Msub ≅ Gal(M/K)`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped NumberField
open CategoryTheory

namespace NK.CFTLib.GFC

theorem exists_element_of_order_card_of_auxiliary (hpp : NK.CFTLib.PrimePowerReciprocity)
    {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Field Ω] [NumberField Ω] [Algebra K Ω]
    [FiniteDimensional K Ω] [IsGalois K Ω] (Msub Nsub : Subgroup Gal(Ω/K)) [Msub.Normal]
    [Nsub.Normal] (hcyc : IsCyclic (Gal(Ω/K) ⧸ Msub))
    (hcardM : Nat.card (Gal(Ω/K) ⧸ Msub) = Nat.card Gal(L/K))
    (hdisj : IntermediateField.fixedField Msub ⊓ IntermediateField.fixedField Nsub = ⊥)
    (hsup : IntermediateField.fixedField Msub ⊔ IntermediateField.fixedField Nsub = ⊤) :
    ∃ x : groupCohomology ((NK.GlobalCFT.IdeleClassGroup.rep K Ω).quotientToInvariants Msub) 2,
      addOrderOf x = Nat.card Gal(L/K) := by
  classical
  let F := ↥(IntermediateField.fixedField Msub)
  haveI : NumberField F := inferInstance
  haveI : IsGalois K F := inferInstance
  haveI hcycF : IsCyclic (F ≃ₐ[K] F) :=
    (MulEquiv.isCyclic (IsGalois.normalAutEquivQuotient (K := K) (L := Ω) Msub)).mp hcyc
  let φ : Gal(Ω/K) ⧸ Msub ≃* Gal(F/K) := IsGalois.normalAutEquivQuotient Msub
  have hcardF : Nat.card (F ≃ₐ[K] F) = Nat.card Gal(L/K) := by
    rw [← hcardM]
    exact (Nat.card_congr φ.toEquiv).symm
  obtain ⟨α, hα⟩ := NK.CFTLib.exists_fundamentalClass_of_isCyclic hpp (K := K) (L := F)
  obtain ⟨hiso⟩ := NK.HassePrinciple.repIso_quotientToInvariants_fixedField (K := K) (L := Ω) Msub
  have e1 : groupCohomology
        ((NK.GlobalCFT.IdeleClassGroup.rep K Ω).quotientToInvariants Msub) 2 ≅
      groupCohomology (Rep.res φ.toMonoidHom (NK.GlobalCFT.IdeleClassGroup.rep K F)) 2 :=
    (groupCohomology.functor ℤ (Gal(Ω/K) ⧸ Msub) 2).mapIso hiso
  have e2 : groupCohomology (Rep.res φ.toMonoidHom (NK.GlobalCFT.IdeleClassGroup.rep K F)) 2 ≅
      groupCohomology (NK.GlobalCFT.IdeleClassGroup.rep K F) 2 :=
    groupCohomology.mapIso φ (LinearEquiv.refl ℤ _) (by intro g; rfl) 2
  refine ⟨(e2.symm ≪≫ e1.symm).toLinearEquiv α, ?_⟩
  exact (AddEquiv.addOrderOf_eq (e2.symm ≪≫ e1.symm).toLinearEquiv.toAddEquiv α).trans
    (hα.trans hcardF)

end NK.CFTLib.GFC
