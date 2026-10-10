import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.Work.SSGRoute.myv2.Hdiag
import Submission.Work.SSGRoute.myv2.kummerSubfield_data_correction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The small-field data of the corrected diagonal, from the level-`E` Artin map

`Work.SSGRoute.N2v2.hdiag_E` consumes, for every `c` with `KummerField c ≤ E`, a subfield
`F ≤ E`, an Artin map of `F/↥K` compatible with that of `E`, a `p`-th root `γ` of `c` in `F`, and
the *corrected* local-norm membership at `𝔭`.  This file assembles that data from
`kummerSubfield_data_correction` (small field and membership) and
`ZConstruction.exists_abelianArtin_localFactors` + Artin uniqueness (the compatible Artin map).
-/

open scoped NumberField
open NumberField IsDedekindDomain
open NK.GlobalCFT

namespace Work.SSGRoute.N2v2

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  [IsAlgClosed Ω]

/-- The `hdata` of `hdiag_E`, assembled from the level-`E` Artin map. -/
theorem hdata_of_kummerField_le
    (p : ℕ) [Fact p.Prime]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (E : IntermediateField ↥K Ω) [FiniteDimensional ↥K E] [IsGalois ↥K E]
    [IsMulCommutative (↥E ≃ₐ[↥K] ↥E)]
    (artE : Idele ↥K →* (↥E ≃ₐ[↥K] ↥E))
    (hkerE : artE.ker = Idele.normImage ↥K ↥E ⊔ Idele.principalSubgroup ↥K)
    (hfrobE : ∀ Q : NK.Chebotarev.PrimeIdeal ↥K,
      NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥E) Q →
      artE (NK.HeckeL.ideleOfPrime ↥K Q) = NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥E) Q)
    (𝔭 : NK.Chebotarev.PrimeIdeal ↥K)
    (c : (↥K)ˣ) (hcE : NK.LocalAnabelian.kummerField (K' := Ω) p c ≤ E) :
    ∃ (F : IntermediateField ↥K ↥E) (_ : FiniteDimensional ↥K F) (_ : Normal ↥K F)
      (_ : NumberField ↥F)
      (artF : Idele ↥K →* (↥F ≃ₐ[↥K] ↥F)) (γ : (↥E)ˣ),
      (∀ x : Idele ↥K,
        AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := ↥E) F (artE x) = artF x) ∧
      (∀ y : Idele ↥F, artF (Idele.normIdeleHom ↥K ↥F y) = 1) ∧
      γ ^ p = Units.map (algebraMap ↥K ↥E) c ∧ (γ : ↥E) ∈ F ∧
      NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭)
        (Units.mk0 (ζ ^ (p * (p - 1) / 2))
          (pow_ne_zero _ (hζ.ne_zero (Fact.out : p.Prime).ne_zero)) * c) ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥F)
          (NK.GlobalCFT.Place.ofFinite 𝔭) := by
  classical
  haveI hNumK : NumberField ↥K := NumberField.of_module_finite k ↥K
  haveI hNumE : NumberField ↥E := NumberField.of_module_finite ↥K ↥E
  obtain ⟨F, hFfd, hFn, hFnf, hFcomm, γ, hγ, hγF, hcloc⟩ :=
    Work.SSGRoute.myv2.kummerSubfield_data_correction p K ζ hζ E 𝔭 c hcE
  haveI : FiniteDimensional ↥K F := hFfd
  haveI : Normal ↥K F := hFn
  haveI : NumberField ↥F := hFnf
  haveI : IsMulCommutative (↥F ≃ₐ[↥K] ↥F) := hFcomm
  -- the Artin map of the small level `F/↥K`
  have hcommE : ∀ a b : (↥E ≃ₐ[↥K] ↥E), a * b = b * a :=
    fun a b => IsMulCommutative.is_comm.comm a b
  haveI hFgal : IsGalois ↥K ↥F :=
    isGalois_iff.mpr ⟨inferInstance, IsGalois.to_normal⟩
  have hcommF : ∀ a b : (↥F ≃ₐ[↥K] ↥F), a * b = b * a :=
    fun a b => IsMulCommutative.is_comm.comm a b
  obtain ⟨artF, hkerF, hnormF, _hprinF, _hlocF, hfrobF, _hprodF⟩ :=
    Work.SSGRoute.ZConstruction.exists_abelianArtin_localFactors (K := ↥K) (L := ↥F) hcommF
  have hcompat : (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := ↥E) F).comp artE = artF :=
    Work.SSGRoute.ZDataMup.ArtinUniqueness.artinMap_restrictNormalHom_eq_abelian hcommE F artE
      hkerE hfrobE artF hkerF hfrobF
  refine ⟨F, hFfd, hFn, hFnf, artF, γ, fun x => DFunLike.congr_fun hcompat x, ?_, hγ, hγF, hcloc⟩
  intro y
  rw [← MonoidHom.mem_ker, hkerF]
  exact Subgroup.mem_sup_left
    (Idele.mem_normImage.mpr ⟨y, fun v => by rw [Idele.normIdeleHom_apply]⟩)

end Work.SSGRoute.N2v2
