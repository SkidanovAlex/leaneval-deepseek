import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.GrunwaldEscapeCore.Vocab
import Submission.Work.SSGRoute.step4_y_escape_v2.localFactor_productFormula_clean
import Submission.Work.SSGRoute.ZDataMup.localGlobalArtinMap_exists_comm
import Submission.Work.SSGRoute.ZDataMup.AbelianOnePlaceAux4
import Submission.Work.SSGRoute.N2v2.isUnramifiedIn_of_notMem_Tprime
import Submission.Work.SSGRoute.ZDataMup.ArtinUniqueness.artinMap_restrictNormalHom_eq_abelian
import Submission.Work.SSGRoute.ZConstruction.exists_abelianArtin_localFactors
import Submission.Work.SSGRoute.ZDataMup.isUnramifiedIn_of_inertia_subset_fixingSubgroup
import Submission.Work.SSGRoute.ZDataMup.LocalUnramified.kummerChar_zero_on_inertia_imp_mem_unramified
import Submission.Work.SSGRoute.ZDataMup.normImage_topIntermediateField
import Submission.Work.SSGRoute.Sha2Lib.ideleClassEquiv_refl
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.N2v2

open NumberField IsDedekindDomain

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Auxiliary lemmas (copies in the `ZDataMup` import lane)

Two ingredients of the proof of the inertia clause (S2):

* `normImage_eq_of_algEquiv_zdata` — the idèlic norm image is invariant under a `K`-algebra isomorphism of
  the extension;
* `isUnramifiedIn_of_isInertia_le_fixingSubgroup_zdata` — the fixed field of the inertia of a place is
  unramified at the prime below that place.

The last ingredient is the level compatibility of the Artin map,
`Work.SSGRoute.ZDataMup.ArtinUniqueness.artinMap_restrictNormalHom_eq_abelian`, which is imported
above.  The route of the proof is then: the fixed field `L` of the inertia image is unramified at
`𝔭`, so the local units at `𝔭` are local norms for `L/↥K`, so the Artin map of `L/↥K` kills the
one-place idèle of a local unit; level compatibility therefore puts the local factor of the Artin
map of `↥E/↥K` inside `Gal(↥E/↥L)`, which is exactly the image of the place inertia. -/

/-- **The idèlic norm image is invariant under a `K`-algebra isomorphism of the extension.** -/
theorem normImage_eq_of_algEquiv_zdata {K L₁ L₂ : Type} [Field K] [NumberField K] [Field L₁]
    [NumberField L₁] [Field L₂] [NumberField L₂] [Algebra K L₁] [Algebra K L₂]
    (e : L₁ ≃ₐ[K] L₂) :
    NK.GlobalCFT.Idele.normImage K L₂ = NK.GlobalCFT.Idele.normImage K L₁ := by
  have h := Work.SSGRoute.ZDataMup.normImage_map_ideleEquiv (K := K) (L := L₁) (K' := K)
    (L' := L₂) (RingEquiv.refl K) e.toRingEquiv (fun x => by simp)
  have hid : (NK.GlobalCFT.Idele.normImage K L₁).map
      (NK.GlobalCFTdeep.Transport.ideleEquiv (RingEquiv.refl K)).toMonoidHom =
      NK.GlobalCFT.Idele.normImage K L₁ := by
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      change (NK.GlobalCFTdeep.Transport.ideleEquiv (RingEquiv.refl K)) y ∈
        NK.GlobalCFT.Idele.normImage K L₁
      rwa [Work.SSGRoute.Sha2Lib.ssgr_ideleEquiv_refl_apply y]
    · intro x hx
      refine Subgroup.mem_map.mpr ⟨x, hx, ?_⟩
      exact Work.SSGRoute.Sha2Lib.ssgr_ideleEquiv_refl_apply x
  rw [← h, hid]

/-- **The fixed field of the place inertia at `A` is unramified at the prime below `A`.**

For `L : IntermediateField ↥K Ω` (finite over `↥K` and Galois) every element of which is fixed by
the inertia subgroup of the finite place `A`, the prime `𝔭` of `↥K` below `A` is unramified in
`L/↥K`.  This is the standard "the fixed field of the inertia is the maximal subextension unramified
at the place", proved here via the generic criterion
`Work.SSGRoute.ZDataMup.isUnramifiedIn_of_inertia_subset_fixingSubgroup`, which requires the
inertia of *every* place over `𝔭` to fix `L`: two places over the same prime of `↥K` are conjugate
by `Gal(Ω/↥K)` and their inertia subgroups are conjugate, and `L.fixingSubgroup` is normal in
`Gal(Ω/↥K)` because `L/↥K` is Galois. -/
theorem isUnramifiedIn_of_isInertia_le_fixingSubgroup_zdata {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (L : IntermediateField ↥K Ω) [FiniteDimensional ↥K L] [IsGalois ↥K L]
    (hfix : ∀ σ : Ω ≃ₐ[↥K] Ω, SSGRoute.IsInertia ↥K A σ → σ ∈ L.fixingSubgroup) :
    NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥L) 𝔭 := by
  haveI hAlgK : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
  haveI hSepK : IsSepClosure ↥K Ω := IsSepClosure.of_isAlgClosure_of_perfectField ↥K Ω
  refine Work.SSGRoute.ZDataMup.isUnramifiedIn_of_inertia_subset_fixingSubgroup (K := ↥K)
    (Ω := Ω) L 𝔭 ?_
  intro B _hB hBc σ hσ
  -- two places over the same prime of `↥K` are conjugate
  obtain ⟨g, hg⟩ :=
    Commons.RingTheory.Valuation.exists_smul_eq_of_comap_eq (F := ↥K) (E := Ω) A B
      (h𝔭.trans hBc.symm)
  -- conjugation of the inertia
  have hI : SSGRoute.IsInertia ↥K A (g⁻¹ * σ * g) := by
    have hconj := Work.SSGRoute.isInertia_conj (k := ↥K) (Ω := Ω) A g (g⁻¹ * σ * g)
    rw [hg, show g * (g⁻¹ * σ * g) * g⁻¹ = σ from by group] at hconj
    exact hconj.mp hσ
  have hmem : g⁻¹ * σ * g ∈ L.fixingSubgroup := hfix _ hI
  -- `L.fixingSubgroup` is the kernel of the restriction to `L`, hence normal
  have hconj : g * (g⁻¹ * σ * g) * g⁻¹ ∈ L.fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker L, MonoidHom.mem_ker, map_mul, map_mul, map_inv]
    have h1 : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) ↥L (g⁻¹ * σ * g) = 1 := by
      have h2 := hmem
      rw [← IntermediateField.restrictNormalHom_ker L, MonoidHom.mem_ker] at h2
      exact h2
    rw [h1]
    group
  rwa [show g * (g⁻¹ * σ * g) * g⁻¹ = σ from by group] at hconj

/-- **The inertia clause (S2) for the local factors of an idèlic Artin map.**

Companion of `Work.SSGRoute.N2v2.exists_artinMap_with_decompLift` (which produces the same `Φ` with
the decomposition-group clause (S1) instead of the inertia clause below).  `Φ` is pinned by the
kernel clause together with the Frobenius normalisation, both by
`Work.SSGRoute.ZDataMup.ArtinUniqueness.artinMap_restrictNormalHom_eq_abelian` (the reviewers of the
version *without* the Frobenius clause pointed out that without it the kernel clause only pins `Φ`
up to `Aut(Gal(↥E/↥K))`, which need not preserve inertia images — hence the clause is included
here, so that the two statements can be combined).

For `E/↥K` finite abelian inside `Ω`, a homomorphism `Φ : 𝕀_↥K →* Gal(↥E/↥K)` with kernel
`N 𝕀_E ⊔ ↥Kˣ` and Frobenius normalisation sends the local factor of a **local unit** at a prime `𝔭`
of `↥K` into the *inertia* subgroup of a place `A` of `Ω` over `𝔭`, i.e. the local factor is the
restriction to `E` of some `σ : Ω ≃ₐ[↥K] Ω` with `SSGRoute.IsInertia k A (σ.restrictScalars k)`
(equivalently `SSGRoute.IsInertia ↥K A σ`, cf. the on-disk iff in
`Work.SSGRoute.ZDataMup.LocalUnramified`).  This is what allows the third disjuncts of
`horth₁`/`horth₂` (which only kill the inertia of a place) to be evaluated at local factors.

Route (any correct one is fine): let `J ≤ Gal(↥E/↥K)` be the image of the inertia group of `A` and
`E^J ≤ E` its fixed field; `E^J/↥K` is unramified at `A` by construction, so the local units are
local norms there (`NK.CFTLib.IdeleHasse.localUnits_le_localNormSubgroup_of_unramified`), whence the
local factor of a unit is trivial in `Gal(E^J/↥K)` (its kernel is the norm class subgroup, by
Artin uniqueness), so the local factor in `Gal(E/↥K)` lies in `J ≤` the image of the inertia. -/
theorem inertiaLift_of_artinMap_zdata {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (E : IntermediateField ↥K Ω) [FiniteDimensional ↥K E] [IsGalois ↥K E]
    [IsMulCommutative (↥E ≃ₐ[↥K] ↥E)]
    (Φ : NK.GlobalCFT.Idele ↥K →* (↥E ≃ₐ[↥K] ↥E))
    (hker : Φ.ker = NK.GlobalCFT.Idele.normImage ↥K ↥E ⊔
      NK.GlobalCFT.Idele.principalSubgroup ↥K)
    (hfrob : ∀ Q : NK.Chebotarev.PrimeIdeal ↥K,
      NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥E) Q →
      Φ (NK.HeckeL.ideleOfPrime ↥K Q) = NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥E) Q) :
    ∀ (A : ValuationSubring Ω) (_hA : SSGRoute.IsFinPlace k A)
      (𝔭 : NK.Chebotarev.PrimeIdeal ↥K),
      A.comap (algebraMap ↥K Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 →
      ∀ u : (NK.GlobalCFT.Place.localField ↥K (NK.GlobalCFT.Place.ofFinite 𝔭))ˣ,
        u ∈ NK.GlobalCFT.Place.localUnits ↥K (NK.GlobalCFT.Place.ofFinite 𝔭) →
      ∃ σ : Ω ≃ₐ[↥K] Ω, SSGRoute.IsInertia k A (σ.restrictScalars k) ∧
        AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E σ =
          Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭) u) := by
  classical
  haveI hNK : NumberField ↥K :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField K
  haveI hNE : NumberField ↥E :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField E
  have hcomm : ∀ a b : (↥E ≃ₐ[↥K] ↥E), a * b = b * a :=
    fun a b => IsMulCommutative.is_comm.comm a b
  intro A hA 𝔭 h𝔭 u hu
  haveI hAlgK : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
  haveI hAlgClosedK : IsAlgClosed Ω := (inferInstance : IsAlgClosure k Ω).isAlgClosed
  -- the image `J` of the place inertia in `Gal(↥E/↥K)` and its fixed field `L ≤ E`
  set J : Subgroup (↥E ≃ₐ[↥K] ↥E) :=
    (Work.SSGRoute.inertiaSub ↥K Ω A).map
      (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E) with hJ
  set L : IntermediateField ↥K (↥E) := IntermediateField.fixedField J with hL
  have hLfix : L.fixingSubgroup = J := IntermediateField.fixingSubgroup_fixedField J
  haveI hGalL : IsGalois ↥K L := by rw [hL]; infer_instance
  -- the inertia image fixes `L` pointwise
  have hfixL : ∀ σ : Ω ≃ₐ[↥K] Ω, SSGRoute.IsInertia ↥K A σ →
      AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E σ ∈ L.fixingSubgroup := by
    intro σ hσ
    rw [hLfix]
    exact Subgroup.mem_map.mpr
      ⟨σ, (Work.SSGRoute.mem_inertiaSub ↥K Ω A σ).mpr hσ, rfl⟩
  -- the image `LΩ ≤ E` of `L` in `Ω`, and its identification with `L`
  set LΩ : IntermediateField ↥K Ω :=
    L.map (IsScalarTower.toAlgHom ↥K ↥E Ω) with hLΩ
  let e : ↥L ≃ₐ[↥K] ↥LΩ := IntermediateField.equivMap L (IsScalarTower.toAlgHom ↥K ↥E Ω)
  haveI hFDΩ : FiniteDimensional ↥K ↥LΩ :=
    FiniteDimensional.of_surjective (e.toLinearEquiv.toLinearMap) e.toLinearEquiv.surjective
  haveI hGalΩ : IsGalois ↥K ↥LΩ := IsGalois.of_algEquiv e
  -- the inertia fixes `LΩ` pointwise
  have hfixΩ : ∀ σ : Ω ≃ₐ[↥K] Ω, SSGRoute.IsInertia ↥K A σ → σ ∈ LΩ.fixingSubgroup := by
    intro σ hσ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    rw [hLΩ, IntermediateField.mem_map] at hy
    obtain ⟨x, hxL, rfl⟩ := hy
    have hxfix : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E σ x = x :=
      (IntermediateField.mem_fixingSubgroup_iff L _).mp (hfixL σ hσ) x hxL
    calc σ ((IsScalarTower.toAlgHom ↥K ↥E Ω) x)
        = (IsScalarTower.toAlgHom ↥K ↥E Ω)
            (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E σ x) :=
          (AlgEquiv.restrictNormal_commutes (χ := σ) (E := ↥E) x).symm
      _ = (IsScalarTower.toAlgHom ↥K ↥E Ω) x := by rw [hxfix]
  -- `LΩ/↥K` is unramified at `𝔭`
  have hunr : NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥LΩ) 𝔭 :=
    isUnramifiedIn_of_isInertia_le_fixingSubgroup_zdata K A hA 𝔭 h𝔭 LΩ hfixΩ
  -- an Artin map of `L/↥K`, with its kernel and Frobenius normalisation
  have hcommL : ∀ a b : (↥L ≃ₐ[↥K] ↥L), a * b = b * a := by
    intro a b
    have hsurj : Function.Surjective (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := ↥E) ↥L) :=
      AlgEquiv.restrictNormalHom_surjective (F := ↥K) (E := ↥E) (K₁ := ↥L)
    obtain ⟨a', rfl⟩ := hsurj a
    obtain ⟨b', rfl⟩ := hsurj b
    rw [← map_mul, ← map_mul, hcomm a' b']
  obtain ⟨Ψ, hΨker, _hΨnorm, _hΨprin, _hΨloc, hΨfrob, _hΨprod⟩ :=
    Work.SSGRoute.ZConstruction.exists_abelianArtin_localFactors (K := ↥K) (L := ↥L) hcommL
  -- the local units at `𝔭` are local norms for `L/↥K`
  have hlocΩ : u ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥LΩ)
      (NK.GlobalCFT.Place.ofFinite 𝔭) :=
    NK.CFTLib.IdeleHasse.localUnits_le_localNormSubgroup_of_unramified
      (K := ↥K) (L := ↥LΩ) 𝔭 hunr hu
  have hnormeq : NK.GlobalCFT.Idele.normImage ↥K ↥LΩ = NK.GlobalCFT.Idele.normImage ↥K ↥L :=
    normImage_eq_of_algEquiv_zdata e
  have hmemΩ : NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭) u ∈
      NK.GlobalCFT.Idele.normImage ↥K ↥LΩ :=
    (NK.CFTLib.IdeleHasse.onePlace_mem_normImage_iff (K := ↥K) (L := ↥LΩ)
      (NK.GlobalCFT.Place.ofFinite 𝔭) u).mpr hlocΩ
  have hlocL : u ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥L)
      (NK.GlobalCFT.Place.ofFinite 𝔭) :=
    (NK.CFTLib.IdeleHasse.onePlace_mem_normImage_iff (K := ↥K) (L := ↥L)
      (NK.GlobalCFT.Place.ofFinite 𝔭) u).mp (by rwa [← hnormeq])
  have hΨu : Ψ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭) u) = 1 := by
    rw [← MonoidHom.mem_ker, hΨker]
    exact Subgroup.mem_sup_left
      ((NK.CFTLib.IdeleHasse.onePlace_mem_normImage_iff (K := ↥K) (L := ↥L)
        (NK.GlobalCFT.Place.ofFinite 𝔭) u).mpr hlocL)
  -- level compatibility of the Artin maps of `↥E/↥K` and `↥L/↥K`
  have hcomp : (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := ↥E) ↥L).comp Φ = Ψ :=
    Work.SSGRoute.ZDataMup.ArtinUniqueness.artinMap_restrictNormalHom_eq_abelian
      (K := ↥K) (M := ↥E) hcomm L Φ hker hfrob Ψ hΨker hΨfrob
  -- hence the local factor of a local unit lies in `Gal(↥E/↥L) = J`
  have hmem : Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭) u) ∈ J := by
    have h1 : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := ↥E) ↥L
        (Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭) u)) = 1 := by
      rw [← MonoidHom.comp_apply, hcomp, hΨu]
    have h2 : Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭) u) ∈
        L.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker L, MonoidHom.mem_ker]
      exact h1
    rwa [hLfix] at h2
  -- lift along the inertia image
  obtain ⟨σ, hσIK, hσeq⟩ := Subgroup.mem_map.mp hmem
  refine ⟨σ, ?_, ?_⟩
  · exact (Work.SSGRoute.ZDataMup.LocalUnramified.isInertia_restrictScalars_iff K A σ).mpr
      ((Work.SSGRoute.mem_inertiaSub ↥K Ω A σ).mp hσIK)
  · rw [hσeq]

/-- **The inertia clause (S2) for the canonical Artin map of `↥E/↥K`.** -/
theorem exists_artinMap_with_inertiaLift_zdata {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (E : IntermediateField ↥K Ω) [FiniteDimensional ↥K E] [IsGalois ↥K E]
    [IsMulCommutative (↥E ≃ₐ[↥K] ↥E)] :
    ∃ Φ : NK.GlobalCFT.Idele ↥K →* (↥E ≃ₐ[↥K] ↥E),
      Φ.ker = NK.GlobalCFT.Idele.normImage ↥K ↥E ⊔ NK.GlobalCFT.Idele.principalSubgroup ↥K ∧
      (∀ Q : NK.Chebotarev.PrimeIdeal ↥K, NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥E) Q →
        Φ (NK.HeckeL.ideleOfPrime ↥K Q) = NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥E) Q) ∧
      (∀ (A : ValuationSubring Ω) (_hA : SSGRoute.IsFinPlace k A)
        (𝔭 : NK.Chebotarev.PrimeIdeal ↥K),
        A.comap (algebraMap ↥K Ω) =
          IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 →
        ∀ u : (NK.GlobalCFT.Place.localField ↥K (NK.GlobalCFT.Place.ofFinite 𝔭))ˣ,
          u ∈ NK.GlobalCFT.Place.localUnits ↥K (NK.GlobalCFT.Place.ofFinite 𝔭) →
        ∃ σ : Ω ≃ₐ[↥K] Ω, SSGRoute.IsInertia k A (σ.restrictScalars k) ∧
          AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E σ =
            Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭) u)) := by
  haveI hNE : NumberField ↥E :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField E
  have hcomm : ∀ a b : (↥E ≃ₐ[↥K] ↥E), a * b = b * a :=
    fun a b => IsMulCommutative.is_comm.comm a b
  obtain ⟨Φ, hker, _hnorm, _hprin, _hloc, hfrob, _hprod⟩ :=
    Work.SSGRoute.ZConstruction.exists_abelianArtin_localFactors (K := ↥K) (L := ↥E) hcomm
  exact ⟨Φ, hker, hfrob, inertiaLift_of_artinMap_zdata (K := K) E Φ hker hfrob⟩

end Work.SSGRoute.N2v2
