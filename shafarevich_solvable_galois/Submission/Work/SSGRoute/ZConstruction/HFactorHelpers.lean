import Mathlib
import Submission.Work.SSGRoute.ZDataMup.LTRecFamHonest.TowerTransport
import Submission.Work.SSGRoute.ZDataMup.ArtinUniqueness.artinMap_restrictNormalHom_eq_abelian
import Submission.NK.NUV2.ARL.transferSelfContained
import Submission.NK.Chebotarev.IsFrobAtPrimeAlgEquivSameBase
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField
import Submission.NK.CFTLib.Arl.eq_top_of_forall_isFrobAtPrime_of_notMem
import Submission.NK.CFTLib.exists_congruenceSubgroup_le_normImage
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.surjective_of_frobAtPrime_unramified
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Transport of a subfield `L ≤ M` of `Ω` and restriction through `Ω`

This file collects the elementary (field-theoretic, no ramification) facts about the transport of a
subfield `L ≤ M` of an ambient field `Ω` to an intermediate field of `↥M`
(`Work.SSGRoute.ZDataMup.LTRecFamHonest.hRestrict`), and the relation between the "restriction
through `Ω`" homomorphism `restrictMol` of `LTRecFamHonest.TowerTransport` and the usual
`AlgEquiv.restrictNormalHom` at the transported level.

Everything is at universe `0`, matching the ambient setting `(k Ω : Type)`, `K : IntermediateField k
Ω`, `L M : IntermediateField ↥K Ω` of the application.
-/

namespace Work.SSGRoute.ZConstruction

open Work.SSGRoute.ZDataMup.LTRecFamHonest

noncomputable section

variable {K : Type} {Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  {L M : IntermediateField K Ω}

/-- The transported subfield is finite dimensional over the base field. -/
theorem finiteDimensional_hRestrict [FiniteDimensional K M] (hLM : L ≤ M) :
    FiniteDimensional K ↥(hRestrict (K := K) L M hLM) :=
  inferInstance

/-- The transported subfield is Galois over the base field. -/
theorem isGalois_hRestrict (hLM : L ≤ M) [IsGalois K L] :
    IsGalois K ↥(hRestrict (K := K) L M hLM) :=
  IsGalois.of_algEquiv (hRestrictEquiv (K := K) L M hLM).symm

/-- The transported subfield is a number field. -/
theorem numberField_hRestrict (hLM : L ≤ M) [NumberField K] [NumberField ↥M] :
    NumberField ↥(hRestrict (K := K) L M hLM) :=
  Commons.NumberTheory.NumberField.numberField_of_intermediateField
    (K := K) (K' := ↥M) (hRestrict (K := K) L M hLM)

/-- The inverse of `hRestrictEquiv` sends an element of `↥L` to itself, viewed in `↥M`. -/
theorem hRestrictEquiv_symm_apply_coe (hLM : L ≤ M) (y : ↥L) :
    ((hRestrictEquiv (K := K) L M hLM).symm y : ↥M) = ⟨(y : Ω), hLM y.2⟩ := by
  refine Subtype.ext ?_
  have h1 := hRestrictEquiv_apply (K := K) (L := L) (M := M) (hLM := hLM)
    ((hRestrictEquiv (K := K) L M hLM).symm y)
  rw [AlgEquiv.apply_symm_apply] at h1
  rw [h1]

/-- **The action of `restrictMol` on points.**  The automorphism of `↥L` obtained from `σ` by
restriction through `Ω` acts on `Ω` as `σ` does. -/
theorem restrictMol_apply (hLM : L ≤ M) [Normal K L] [Normal K M] [Normal K Ω]
    (σ : ↥M ≃ₐ[K] ↥M) (x : ↥L) :
    ((restrictMol L M hLM σ) x : Ω) = (σ ⟨(x : Ω), hLM x.2⟩ : Ω) := by
  rw [show restrictMol L M hLM σ
      = AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) ↥L (σ.liftNormal Ω) from rfl]
  rw [AlgEquiv.restrictNormalHom_apply]
  exact AlgEquiv.liftNormal_commutes σ Ω ⟨(x : Ω), hLM x.2⟩

/-- **Restricting along the transported field and transporting back.**  The action of the
transported restriction of `σ` on `Ω` is the action of `σ`. -/
theorem hRestrictEquiv_restrictNormalHom_apply (hLM : L ≤ M) [Normal K L] [Normal K M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K ↥(hRestrict (K := K) L M hLM)]
    (σ : ↥M ≃ₐ[K] ↥M) (z : ↥(hRestrict (K := K) L M hLM)) :
    ((hRestrictEquiv (K := K) L M hLM)
        ((AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥M)
          ↥(hRestrict (K := K) L M hLM) σ) z) : Ω)
      = (σ (z : ↥M) : Ω) := by
  rw [hRestrictEquiv_apply]
  rw [AlgEquiv.restrictNormalHom_apply]

/-- **The bridge, pointwise form.**  Conjugating the restriction of `σ` to the transported field
`L' ≤ ↥M` along `hRestrictEquiv` gives the restriction of `σ` to `L` through `Ω`; here this is
stated as an equality of the two actions on `Ω`. -/
theorem conjHom_hRestrictEquiv_restrictMol_apply (hLM : L ≤ M) [Normal K L] [Normal K M]
    [Normal K Ω] [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K ↥(hRestrict (K := K) L M hLM)]
    (σ : ↥M ≃ₐ[K] ↥M) (y : ↥L) :
    ((NK.NUV2.ARL.SC.conjHom (hRestrictEquiv (K := K) L M hLM)
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥M)
          ↥(hRestrict (K := K) L M hLM) σ)) y : Ω)
      = ((restrictMol L M hLM σ) y : Ω) := by
  rw [NK.NUV2.ARL.SC.conjHom_apply]
  rw [hRestrictEquiv_restrictNormalHom_apply (K := K) (L := L) (M := M) hLM σ
    ((hRestrictEquiv (K := K) L M hLM).symm y)]
  rw [hRestrictEquiv_symm_apply_coe (K := K) (L := L) (M := M) hLM y]
  exact (restrictMol_apply (K := K) (L := L) (M := M) hLM σ y).symm

/-- **The bridge between `restrictMol` and `restrictNormalHom`.** -/
theorem conjHom_hRestrictEquiv_restrictMol (hLM : L ≤ M) [Normal K L] [Normal K M]
    [Normal K Ω] [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K ↥(hRestrict (K := K) L M hLM)] (σ : ↥M ≃ₐ[K] ↥M) :
    NK.NUV2.ARL.SC.conjHom (hRestrictEquiv (K := K) L M hLM)
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥M)
          ↥(hRestrict (K := K) L M hLM) σ)
      = restrictMol L M hLM σ := by
  ext y
  exact conjHom_hRestrictEquiv_restrictMol_apply (K := K) (L := L) (M := M) hLM σ y

/-- The other orientation of the bridge. -/
theorem restrictMol_eq_conjHom_hRestrictEquiv (hLM : L ≤ M) [Normal K L] [Normal K M]
    [Normal K Ω] [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K ↥(hRestrict (K := K) L M hLM)] (σ : ↥M ≃ₐ[K] ↥M) :
    restrictMol L M hLM σ
      = NK.NUV2.ARL.SC.conjHom (hRestrictEquiv (K := K) L M hLM)
          (AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥M)
            ↥(hRestrict (K := K) L M hLM) σ) :=
  (conjHom_hRestrictEquiv_restrictMol (K := K) (L := L) (M := M) hLM σ).symm

/-- The conjugation homomorphism `hRestrictGalHom` is `NK.NUV2.ARL.SC.conjHom` along
`hRestrictEquiv`; recorded for convenience. -/
theorem hRestrictGalHom_eq_conjHom (hLM : L ≤ M) (τ : ↥L ≃ₐ[K] ↥L) :
    hRestrictGalHom (K := K) L M hLM τ
      = NK.NUV2.ARL.SC.conjHom (hRestrictEquiv (K := K) L M hLM).symm τ := rfl

end

end Work.SSGRoute.ZConstruction
