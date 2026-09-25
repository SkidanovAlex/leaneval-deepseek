import Mathlib
import Submission.Work.CFTLib.splitSet_eq_imp_proportional
import Submission.Work.CFTLib.ClassGroupTransport.exists_classGroup_mulEquiv

/-!
# The conjugate field of a subfield under an automorphism

Let `K/F` and `K'/F` be finite Galois extensions of number fields with `K ⊆ K'` (a scalar tower),
`M : IntermediateField K K'` and `g : K' ≃ₐ[F] K'`.  Since `g(K) = K`, the image `g(M)` is again a
`K`-subfield of `K'`; it is represented here as `conjField g M`.

This file also contains

* `conjGal`/`conjHom`: conjugation by `g` as a group homomorphism `Gal(K'/K) →* Gal(K'/K)`;
* `fixedField_conjHom_eq_conjField`: `conjField g M` is the fixed field of the conjugate of
  `Gal(K'/M)`, whence `isGalois_conjField`: `conjField g M / K` is Galois;
* `mapPrime`: the image of a prime of `𝓞 K` under a ring equivalence of `𝓞 K`, and
  `primeCls_mapPrime`: the effect on ideal classes;
* `conjAlgEquiv`/`conjRingAlgEquiv`: the `F`-algebra isomorphism `↥M ≃ₐ[F] ↥(conjField g M)` and
  its restriction `𝓞 ↥M ≃ₐ[𝓞 F] 𝓞 ↥(conjField g M)` to the rings of integers.
-/

open NumberField
open scoped Classical Pointwise

set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

namespace Work.CFTLib.InvCharCrux

variable {F K K' : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field K']
  [NumberField K'] [Algebra F K] [Algebra F K'] [Algebra K K'] [IsScalarTower F K K']
  [FiniteDimensional F K] [FiniteDimensional F K'] [IsGalois F K] [IsGalois F K']

/-! ## The conjugate field -/

/-- **The conjugate field.**  For `g : K' ≃ₐ[F] K'` and a `K`-intermediate field `M`, the image
`g(M)` is again a `K`-subfield of `K'` (because `g(K) = K`).  It is represented here as an
`IntermediateField K K'` whose underlying set is `M.map g`. -/
noncomputable def conjField (g : K' ≃ₐ[F] K') (M : IntermediateField K K') :
    IntermediateField K K' :=
  { ((IntermediateField.restrictScalars F M).map g.toAlgHom).toSubfield with
    algebraMap_mem' := fun k =>
      ⟨algebraMap K K' ((g.restrictNormal K).symm k), M.algebraMap_mem _,
        (by
          simpa using
            (AlgEquiv.restrictNormal_commutes g K ((g.restrictNormal K).symm k)).symm)⟩ }

/-- Membership in the conjugate field: `x ∈ conjField g M ↔ g⁻¹ x ∈ M`. -/
theorem mem_conjField (g : K' ≃ₐ[F] K') (M : IntermediateField K K') (x : K') :
    x ∈ conjField g M ↔ g⁻¹ x ∈ M := by
  constructor
  · intro h
    have h1 : x ∈ (IntermediateField.restrictScalars F M).map g.toAlgHom := h
    obtain ⟨y, hy, hyx⟩ :=
      (IntermediateField.mem_map (S := IntermediateField.restrictScalars F M)
        (f := g.toAlgHom)).mp h1
    have h2 : (g⁻¹ : K' ≃ₐ[F] K') x = y := by
      rw [← hyx]
      simp
    rwa [h2]
  · intro h
    have : x ∈ (IntermediateField.restrictScalars F M).map g.toAlgHom :=
      (IntermediateField.mem_map (S := IntermediateField.restrictScalars F M)
        (f := g.toAlgHom)).mpr
        ⟨g⁻¹ x, h, by simp⟩
    exact this

/-- The conjugate field, restricted to `F`, is the image of `M` under `g`. -/
theorem restrictScalars_conjField (g : K' ≃ₐ[F] K') (M : IntermediateField K K') :
    IntermediateField.restrictScalars F (conjField g M) =
      (IntermediateField.restrictScalars F M).map g.toAlgHom := by
  ext x
  change x ∈ conjField g M ↔ x ∈ (IntermediateField.restrictScalars F M).map g.toAlgHom
  rw [mem_conjField]
  constructor
  · intro h
    exact (IntermediateField.mem_map (S := IntermediateField.restrictScalars F M)
      (f := g.toAlgHom)).mpr ⟨g⁻¹ x, h, by simp⟩
  · intro h
    obtain ⟨y, hy, hyx⟩ := (IntermediateField.mem_map
      (S := IntermediateField.restrictScalars F M) (f := g.toAlgHom)).mp h
    rw [← hyx]
    simpa using hy

/-! ## Conjugation on `Gal(K'/K)` by an element of `Gal(K'/F)` -/

/-- Conjugation by `g : K' ≃ₐ[F] K'` maps `Gal(K'/K)` to itself: the conjugation of a
`K`-automorphism of `K'` by `g` is again a `K`-automorphism (`g` normalises `K`). -/
noncomputable def conjGal (g : K' ≃ₐ[F] K') (σ : K' ≃ₐ[K] K') : K' ≃ₐ[K] K' :=
  { (g⁻¹.trans (σ.restrictScalars F)).trans g with
    commutes' := fun k => by
      have h2 : (g : K' ≃ₐ[F] K') (algebraMap K K' ((g.restrictNormal K).symm k)) =
          algebraMap K K' k := by
        simpa using
          (AlgEquiv.restrictNormal_commutes g K ((g.restrictNormal K).symm k)).symm
      have h3 : (g⁻¹ : K' ≃ₐ[F] K') (algebraMap K K' k) =
          algebraMap K K' ((g.restrictNormal K).symm k) := by
        rw [← h2]
        simp
      have h4 : ((σ.restrictScalars F : K' ≃ₐ[F] K') : K' → K')
          (algebraMap K K' ((g.restrictNormal K).symm k)) =
          algebraMap K K' ((g.restrictNormal K).symm k) := σ.commutes _
      change g (((σ.restrictScalars F : K' ≃ₐ[F] K') : K' → K')
        ((g⁻¹ : K' ≃ₐ[F] K') (algebraMap K K' k))) = algebraMap K K' k
      rw [h3, h4]
      exact h2 }

@[simp]
theorem conjGal_apply (g : K' ≃ₐ[F] K') (σ : K' ≃ₐ[K] K') (x : K') :
    conjGal g σ x = g (σ (g⁻¹ x)) := by
  simp [conjGal]

/-- Conjugation by `g` as a group homomorphism `Gal(K'/K) →* Gal(K'/K)`. -/
noncomputable def conjHom (g : K' ≃ₐ[F] K') : Gal(K'/K) →* Gal(K'/K) where
  toFun := conjGal g
  map_one' := by
    ext x
    simp [conjGal]
  map_mul' := by
    intro a b
    ext x
    simp [conjGal]

@[simp]
theorem conjHom_apply (g : K' ≃ₐ[F] K') (σ : K' ≃ₐ[K] K') (x : K') :
    conjHom g σ x = g (σ (g⁻¹ x)) := conjGal_apply g σ x

theorem conjHom_conjHom (g : K' ≃ₐ[F] K') (σ : K' ≃ₐ[K] K') :
    conjHom g (conjHom g⁻¹ σ) = σ := by
  ext x
  simp [conjHom_apply]

theorem conjHom_surjective (g : K' ≃ₐ[F] K') :
    Function.Surjective (conjHom (K := K) g) :=
  fun σ => ⟨conjHom (K := K) g⁻¹ σ, conjHom_conjHom g σ⟩

/-! ## The conjugate field is finite and Galois over `K` -/

/-- The fixed field of the conjugate of `Gal(K'/M)` is the conjugate field. -/
theorem fixedField_conjHom_eq_conjField (g : K' ≃ₐ[F] K') (M : IntermediateField K K')
    [FiniteDimensional K M] [IsGalois K M] :
    IntermediateField.fixedField (M.fixingSubgroup.map (conjHom (K := K) g)) =
      conjField g M := by
  haveI hgal : IsGalois K K' := IsGalois.tower_top_of_isGalois F K K'
  have hfix : IntermediateField.fixedField (M.fixingSubgroup) = M :=
    IsGalois.fixedField_fixingSubgroup M
  ext x
  rw [IntermediateField.mem_fixedField_iff, mem_conjField]
  constructor
  · intro h
    have h1 : g⁻¹ x ∈ IntermediateField.fixedField (M.fixingSubgroup) := by
      rw [IntermediateField.mem_fixedField_iff]
      intro σ hσ
      have hmem : conjHom (K := K) g σ ∈ M.fixingSubgroup.map (conjHom (K := K) g) :=
        Subgroup.mem_map.mpr ⟨σ, hσ, rfl⟩
      have h2' : g (σ (g⁻¹ x)) = x := by
        have h5 : conjHom (K := K) g σ x = x := h _ hmem
        rwa [conjHom_apply] at h5
      exact g.injective (h2'.trans (by simp))
    rwa [hfix] at h1
  · intro h τ hτ
    obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hτ
    have hσx : σ (g⁻¹ x) = g⁻¹ x := by
      rw [← hfix, IntermediateField.mem_fixedField_iff] at h
      exact h σ hσ
    rw [conjHom_apply, hσx]
    simp

/-- **The conjugate field is Galois over `K`**: `Gal(K'/(conjField g M))` is the conjugate of
`Gal(K'/M)`, which is normal in `Gal(K'/K)`. -/
theorem isGalois_conjField (g : K' ≃ₐ[F] K') (M : IntermediateField K K')
    [FiniteDimensional K M] [IsGalois K M] :
    IsGalois K ↥(conjField g M) := by
  haveI hgal : IsGalois K K' := IsGalois.tower_top_of_isGalois F K K'
  haveI hN : (M.fixingSubgroup.map (conjHom (K := K) g)).Normal :=
    (IsGalois.fixingSubgroup_normal_of_isGalois M).map (conjHom (K := K) g)
      (conjHom_surjective g)
  have h := IsGalois.of_fixedField_normal_subgroup (M.fixingSubgroup.map (conjHom (K := K) g))
  rwa [fixedField_conjHom_eq_conjField g M] at h

/-- The conjugate field is finite dimensional over `K`. -/
theorem finiteDimensional_conjField (g : K' ≃ₐ[F] K') (M : IntermediateField K K')
    [FiniteDimensional K M] [IsGalois K M] : FiniteDimensional K ↥(conjField g M) := by
  haveI hgal : IsGalois K K' := IsGalois.tower_top_of_isGalois F K K'
  exact (fixedField_conjHom_eq_conjField g M).symm ▸
    (inferInstance : FiniteDimensional K
      ↥(IntermediateField.fixedField (M.fixingSubgroup.map (conjHom (K := K) g))))

/-! ## Transport of primes along a ring equivalence of `𝓞 K` -/

/-- The image of a prime of `𝓞 K` under a ring equivalence. -/
noncomputable def mapPrime (e : 𝓞 K ≃+* 𝓞 K)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    IsDedekindDomain.HeightOneSpectrum (𝓞 K) where
  asIdeal := v.asIdeal.map e
  isPrime := Ideal.map_isPrime_of_equiv e
  ne_bot := fun h => v.ne_bot ((Ideal.map_eq_bot_iff_of_injective e.injective).mp h)

@[simp]
theorem mapPrime_asIdeal (e : 𝓞 K ≃+* 𝓞 K) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    (mapPrime e v).asIdeal = v.asIdeal.map e := rfl

/-- The ideal class of the image prime is the image of the ideal class. -/
theorem primeCls_mapPrime (e : 𝓞 K ≃+* 𝓞 K) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Work.CFTLib.primeCls (mapPrime e v) =
      ClassGroup.mulEquiv e (Work.CFTLib.primeCls v) := by
  rw [Work.CFTLib.primeCls, Work.CFTLib.primeCls,
    Work.CFTLib.ClassGroupTransport.mk0_mulEquiv]
  congr 1

theorem mapPrime_id (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    mapPrime (1 : 𝓞 K ≃+* 𝓞 K) v = v := by
  refine IsDedekindDomain.HeightOneSpectrum.ext ?_
  rw [mapPrime_asIdeal]
  exact Ideal.map_id v.asIdeal

theorem mapPrime_comp (e e' : 𝓞 K ≃+* 𝓞 K)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    mapPrime (e' * e) v = mapPrime e' (mapPrime e v) := by
  have h : Ideal.map ((e' * e : 𝓞 K ≃+* 𝓞 K) : 𝓞 K →+* 𝓞 K) v.asIdeal =
      Ideal.map (e' : 𝓞 K →+* 𝓞 K)
        (Ideal.map (e : 𝓞 K →+* 𝓞 K) v.asIdeal) := by
    rw [Ideal.map_map]
    congr 1
  exact IsDedekindDomain.HeightOneSpectrum.ext h

theorem mapPrime_inv_mapPrime (e : 𝓞 K ≃+* 𝓞 K)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    mapPrime e⁻¹ (mapPrime e v) = v := by
  rw [← mapPrime_comp, inv_mul_cancel, mapPrime_id]

/-- The `F`-algebra isomorphism `M ≃ₐ[F] conjField g M` given by `g`. -/
noncomputable def conjAlgEquiv (g : K' ≃ₐ[F] K') (M : IntermediateField K K') :
    ↥M ≃ₐ[F] ↥(conjField g M) :=
  IntermediateField.equivMap (IntermediateField.restrictScalars F M) g.toAlgHom

@[simp]
theorem conjAlgEquiv_apply (g : K' ≃ₐ[F] K') (M : IntermediateField K K') (x : ↥M) :
    ((conjAlgEquiv g M x : ↥(conjField g M)) : K') = g x := rfl

/-- The induced isomorphism `𝓞 M ≃ₐ[𝓞 F] 𝓞 (conjField g M)` of rings of integers. -/
noncomputable def conjRingAlgEquiv (g : K' ≃ₐ[F] K') (M : IntermediateField K K') :
    𝓞 ↥M ≃ₐ[𝓞 F] 𝓞 ↥(conjField g M) :=
  NumberField.RingOfIntegers.mapAlgEquiv (conjAlgEquiv g M)

@[simp]
theorem conjRingAlgEquiv_apply (g : K' ≃ₐ[F] K') (M : IntermediateField K K')
    (x : 𝓞 ↥M) :
    ((conjRingAlgEquiv g M x : 𝓞 ↥(conjField g M)) : K') = g x := rfl

end Work.CFTLib.InvCharCrux
