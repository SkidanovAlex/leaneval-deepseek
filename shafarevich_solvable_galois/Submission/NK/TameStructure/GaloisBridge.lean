import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Submission.NK.TameStructure.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open IntermediateField

namespace NK.TameStructure

universe u

noncomputable section

variable {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K']

/-- The restriction map `Gal(K'/κ) →* Gal(F/κ)` for an intermediate field `F`, when `F/κ` is
normal. -/
def galRestrict (F : IntermediateField κ K') [Normal κ F] : Gal(K'/κ) →* Gal(↥F/κ) :=
  AlgEquiv.restrictNormalHom (F := κ) (K₁ := K') ↥F

@[simp]
theorem galRestrict_apply (F : IntermediateField κ K') [Normal κ F] (σ : Gal(K'/κ))
    (x : ↥F) : ↑(galRestrict F σ x) = σ ↑x :=
  AlgEquiv.restrictNormalHom_apply (F := κ) (K₁ := K') F σ x

/-- The kernel of the restriction is the fixing subgroup. -/
theorem galRestrict_ker (F : IntermediateField κ K') [Normal κ F] :
    (galRestrict (κ := κ) (K' := K') F).ker = F.fixingSubgroup :=
  IntermediateField.restrictNormalHom_ker (K := κ) F

/-- **The Galois correspondence for an intermediate Galois subextension.**  If `K'/κ` is Galois
and `F` is a Galois intermediate field, then restriction induces an isomorphism
`Gal(K'/κ) ⧸ F.fixingSubgroup ≃* Gal(F/κ)`. -/
theorem quotient_fixingSubgroup_mulEquiv_gal [IsGalois κ K']
    (F : IntermediateField κ K') [IsGalois κ ↥F] :
    Nonempty (Gal(K'/κ) ⧸ F.fixingSubgroup ≃* Gal(↥F/κ)) := by
  haveI : Normal κ F := IsGalois.to_normal
  refine ⟨(QuotientGroup.quotientMulEquivOfEq (galRestrict_ker (κ := κ) (K' := K') F).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (galRestrict (κ := κ) (K' := K') F)
      (AlgEquiv.restrictNormalHom_surjective (F := κ) (K₁ := ↥F) K'))⟩

/-- **The Galois-correspondence bridge for the inertia subgroup.**  For `K'/κ` Galois,

  `Gal(K'/κ) ⧸ I_κ ≅ Gal(κ(μ_{p'})/κ)`,

where `I_κ = NK.LocalAnabelian.inertiaSubgroup p` is the fixing subgroup of
`κ(μ_{p'}) = NK.LocalAnabelian.unramifiedClosure p`. -/
theorem quotient_inertiaSubgroup_mulEquiv_unramifiedClosure [IsGalois κ K'] (p : ℕ) :
    Nonempty (Gal(K'/κ) ⧸ NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p ≃*
      Gal(↥(NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') p) / κ)) := by
  haveI : IsGalois κ ↥(NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') p) :=
    NK.LocalAnabelian.ResidueField.isGalois_unramifiedClosure (κ := κ) (K' := K') p
  refine ⟨(QuotientGroup.quotientMulEquivOfEq (by
      rw [NK.LocalAnabelian.ResidueField.inertiaSubgroup_eq_fixingSubgroup_unramifiedClosure])).trans
    ?_⟩
  exact (quotient_fixingSubgroup_mulEquiv_gal (κ := κ) (K' := K')
    (NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') p)).some

end

end NK.TameStructure
