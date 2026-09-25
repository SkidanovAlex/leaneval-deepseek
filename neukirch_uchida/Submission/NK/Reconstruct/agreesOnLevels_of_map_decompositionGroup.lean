import Mathlib
import Submission.NeukirchUchida.FieldTransport
import Submission.NK.Reconstruct.PlaceCorrespondence
import Submission.NK.Reconstruct.comap_placeMap_eq_of_realizesPlaceMap
import Submission.NK.Reconstruct.finiteDimensional_sigmaLevel
import Submission.NK.Reconstruct.normal_sigmaLevel
import Submission.NeukirchUchida.Local.PlaceFromValuation
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_primes_splitsCompletely
import Submission.Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely
import Submission.Commons.NumberTheory.NumberField.Completion.decompositionSubgroup_eq_bot_iff_ramificationIdx_eq_one_and_inertiaDeg_eq_one
import Submission.Commons.RingTheory.Valuation.exists_mem_stabilizer_restrictNormalHom_eq_of_isGalois

namespace NK.Reconstruct

open scoped Pointwise

set_option linter.unusedVariables false

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-! ## Group-theoretic bookkeeping for subgroups -/

/-- Mapping a subgroup along a multiplicative equivalence and then back along its inverse is the
identity. -/
theorem subgroup_map_map_symm {G H : Type*} [Group G] [Group H] (e : G ≃* H) (X : Subgroup G) :
    (X.map (e : G →* H)).map (e.symm : H →* G) = X := by
  rw [Subgroup.map_map]
  have hcomp : (e.symm : H →* G).comp (e : G →* H) = MonoidHom.id G := by
    ext x
    simp
  rw [hcomp, Subgroup.map_id]

/-- Mapping a subgroup along the inverse of a multiplicative equivalence and then back is the
identity. -/
theorem subgroup_map_symm_map {G H : Type*} [Group G] [Group H] (e : G ≃* H) (X : Subgroup H) :
    (X.map (e.symm : H →* G)).map (e : G →* H) = X := by
  rw [Subgroup.map_map]
  have hcomp : (e : G →* H).comp (e.symm : H →* G) = MonoidHom.id H := by
    ext x
    simp
  rw [hcomp, Subgroup.map_id]

/-- A subgroup is contained in the image of another along a multiplicative equivalence exactly when
its image along the inverse is contained in the other. -/
theorem subgroup_le_map_iff_map_le {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    {X : Subgroup H} {Y : Subgroup G} :
    X ≤ Y.map (e : G →* H) ↔ X.map (e.symm : H →* G) ≤ Y := by
  constructor
  · intro h
    calc X.map (e.symm : H →* G) ≤ (Y.map (e : G →* H)).map (e.symm : H →* G) :=
          Subgroup.map_mono h
      _ = Y := subgroup_map_map_symm e Y
  · intro h
    calc X = (X.map (e.symm : H →* G)).map (e : G →* H) := (subgroup_map_symm_map e X).symm
      _ ≤ Y.map (e : G →* H) := Subgroup.map_mono h

/-- Containment of images along an injective homomorphism is containment. -/
theorem subgroup_map_le_map_iff_of_injective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) {X Y : Subgroup G} : X.map f ≤ Y.map f ↔ X ≤ Y := by
  refine ⟨fun h x hx => ?_, fun h => Subgroup.map_mono h⟩
  rcases Subgroup.mem_map.mp (h (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)) with ⟨y, hy, hyx⟩
  rwa [hf hyx] at hy

/-! ## Transport of the properness of a place along `σ` -/

/-- The trace of a place of `K₁'` on `K₁` is proper exactly when the trace of its transport along
`σ` on `K₂` is proper. -/
theorem comap_sigma_ne_top_iff {σ : K₂' ≃+* K₁'}
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    (A : ValuationSubring K₁') :
    A.comap (algebraMap K₁ K₁') ≠ ⊤ ↔
      (A.comap (σ : K₂' →+* K₁')).comap (algebraMap K₂ K₂') ≠ ⊤ := by
  haveI : IsGalois K₁ K₁' := IsSepClosure.isGalois
  haveI : IsGalois K₂ K₂' := IsSepClosure.isGalois
  have htop₁ : A.comap (algebraMap K₁ K₁') = ⊤ ↔ A = ⊤ :=
    ⟨fun h => Commons.RingTheory.Valuation.ValuationSubring.eq_top_of_comap_algebraMap_eq_top
        A inferInstance h,
      fun h => by rw [h]; ext x; simp [ValuationSubring.mem_comap]⟩
  have htop₂ : (A.comap (σ : K₂' →+* K₁')).comap (algebraMap K₂ K₂') = ⊤ ↔ A = ⊤ := by
    refine ⟨fun h => ?_, fun h => by rw [h]; ext x; simp [ValuationSubring.mem_comap]⟩
    have h1 : A.comap (σ : K₂' →+* K₁') = ⊤ :=
      Commons.RingTheory.Valuation.ValuationSubring.eq_top_of_comap_algebraMap_eq_top
        (A.comap (σ : K₂' →+* K₁')) inferInstance h
    rw [eq_top_iff]
    intro x _
    have hmem : σ.symm x ∈ A.comap (σ : K₂' →+* K₁') := by rw [h1]; trivial
    rw [ValuationSubring.mem_comap] at hmem
    simpa using hmem
  have heq : (A.comap (algebraMap K₁ K₁') = ⊤) ↔
      ((A.comap (σ : K₂' →+* K₁')).comap (algebraMap K₂ K₂') = ⊤) := by
    rw [htop₁, htop₂]
  exact not_congr heq

/-! ## The place-wise form of the hypothesis -/

/-- **The hypothesis `hpres` in place-wise form**: `ϕ` maps the decomposition group of a place of
`K₁'` onto the decomposition group of its transport along `σ`. -/
theorem map_decompositionGroup_eq {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} {σ : K₂' ≃+* K₁'}
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    (hpres : ∀ (A : ValuationSubring K₁') (hA : A.comap (algebraMap K₁ K₁') ≠ ⊤),
      ((Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') A).map
          (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂))).map
        ((Submission.NeukirchUchida.conjHomEquiv hσ).symm : Gal(K₂'/K₂) →* Gal(K₁'/K₁)) =
        Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') A)
    (A : ValuationSubring K₁') (hA : A.comap (algebraMap K₁ K₁') ≠ ⊤) :
    (Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') A).map
        (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) =
      Submission.NeukirchUchida.decompositionGroup (K₁ := K₂) (K₁' := K₂')
        (A.comap (σ : K₂' →+* K₁')) := by
  have h1 := congrArg (fun (H : Subgroup Gal(K₁'/K₁)) =>
      H.map ((Submission.NeukirchUchida.conjHomEquiv hσ) : Gal(K₁'/K₁) →* Gal(K₂'/K₂)))
    (hpres A hA)
  have hcancel : (((Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') A).map
        (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂))).map
      ((Submission.NeukirchUchida.conjHomEquiv hσ).symm : Gal(K₂'/K₂) →* Gal(K₁'/K₁))).map
      ((Submission.NeukirchUchida.conjHomEquiv hσ) : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) =
      (Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') A).map
        (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) :=
    subgroup_map_symm_map ((Submission.NeukirchUchida.conjHomEquiv hσ) : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
      ((Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') A).map
        (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)))
  rw [hcancel] at h1
  rw [h1, map_conjHomEquiv_decompositionGroup hσ A]

/-! ## The image of a level under `σ` -/

/-- The transported level `sigmaLevel σ hσ L` is the image of `L` under `σ`. -/
theorem image_sigmaLevel (σ : K₂' ≃+* K₁')
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    (L : IntermediateField K₂ K₂') :
    σ '' (L : Set K₂') = (sigmaLevel σ hσ L : Set K₁') := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact mem_sigmaLevel.mpr (by simpa using hy)
  · intro hx
    exact ⟨σ.symm x, mem_sigmaLevel.mp hx, σ.apply_symm_apply x⟩

/-! ## The dictionary: decomposition groups versus completely split primes -/

/-- **The dictionary.**  For a place `B` of `K'` over the finite prime `p` of the number field `K`
and a finite Galois level `N ⊆ K'`, the decomposition group of `B` is contained in the fixing
subgroup of `N` exactly when `p` splits completely in `N`. -/
theorem dictionary_stabilizer_le_fixingSubgroup_iff_splitCompletely {K K' : Type*} [Field K]
    [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    {N : IntermediateField K K'} [FiniteDimensional K N] [Normal K N] [NumberField ↥N]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (B : ValuationSubring K') (hB : B.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p) :
    MulAction.stabilizer Gal(K'/K) B ≤ N.fixingSubgroup ↔
      (p.asIdeal.primesOver (NumberField.RingOfIntegers ↥N)).ncard = Module.finrank K ↥N := by
  haveI : IsGalois K K' := IsSepClosure.isGalois
  haveI : IsGalois K ↥N := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  set w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥N) :=
    Submission.NeukirchUchida.Local.placeOf p B hB N with hw
  have hwcomap : B.comap (algebraMap ↥N K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥N w :=
    Submission.NeukirchUchida.Local.comap_eq_valuationSubringAtPrime_placeOf p B hB N
  have hwlies : w.asIdeal.LiesOver p.asIdeal :=
    Submission.NeukirchUchida.Local.placeOf_liesOver p B hB N
  have hsplit : (p.asIdeal.primesOver (NumberField.RingOfIntegers ↥N)).ncard =
        Module.finrank K ↥N ↔
      p.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers ↥N) = 1 ∧
        p.asIdeal.inertiaDegIn (NumberField.RingOfIntegers ↥N) = 1 :=
    Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely
      (K := K) (L := ↥N) p
  have hker : N.fixingSubgroup = (AlgEquiv.restrictNormalHom (F := K) (K₁ := K') N).ker :=
    (IntermediateField.restrictNormalHom_ker N).symm
  constructor
  · intro h
    have hbot : Submission.NeukirchUchida.Local.decompositionSubgroup (K := K) w = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro τ hτ
      have hτ' : τ ∈ MulAction.stabilizer (↥N ≃ₐ[K] ↥N) (B.comap (algebraMap ↥N K')) := by
        rw [hwcomap]
        exact (Submission.NeukirchUchida.Local.mem_stabilizer_valuationSubringAtPrime_iff_mem_decompositionSubgroup
          w τ).mpr hτ
      have hBne : B.comap (algebraMap K K') ≠ ⊤ := by
        rw [hB]
        exact Submission.NeukirchUchida.Local.valuationSubringAtPrime_ne_top p
      obtain ⟨σ, hσB, hστ⟩ :=
        Commons.RingTheory.Valuation.exists_mem_stabilizer_restrictNormalHom_eq_of_isGalois
          (F := K) (E := K') B hBne N τ hτ'
      have hσfix : σ ∈ N.fixingSubgroup := h ((MulAction.mem_stabilizer_iff).mpr hσB)
      rw [hker, MonoidHom.mem_ker] at hσfix
      rw [← hστ, hσfix]
    rw [hsplit]
    exact (Commons.NumberTheory.NumberField.Completion.decompositionSubgroup_eq_bot_iff_ramificationIdx_eq_one_and_inertiaDeg_eq_one
      (K := K) (L := ↥N) p w hwlies).mp hbot
  · intro h
    have hbot : Submission.NeukirchUchida.Local.decompositionSubgroup (K := K) w = ⊥ :=
      (Commons.NumberTheory.NumberField.Completion.decompositionSubgroup_eq_bot_iff_ramificationIdx_eq_one_and_inertiaDeg_eq_one
        (K := K) (L := ↥N) p w hwlies).mpr (hsplit.mp h)
    intro σ hσ
    rw [hker, MonoidHom.mem_ker]
    have h1 : AlgEquiv.restrictNormalHom (F := K) (K₁ := K') N σ ∈
        Submission.NeukirchUchida.Local.decompositionSubgroup (K := K) w :=
      (Submission.NeukirchUchida.Local.mem_stabilizer_iff_forall_mem_decompositionSubgroup
        p B hB σ).mp hσ N
    rw [hw] at h1
    rw [hbot] at h1
    simpa using h1

/-! ## The footprint of a level determines it -/

/-- **The footprint determines the level.**  If two finite Galois levels of `K'/K` are contained in
the decomposition group of the same set of places of `K'` (equivalently: if they have the same
completely split primes), then they are equal. -/
theorem footprint_eq_of_stabilizer_le_fixingSubgroup {K K' : Type*} [Field K] [NumberField K]
    [Field K'] [Algebra K K'] [IsSepClosure K K']
    {N N' : IntermediateField K K'} [FiniteDimensional K N] [Normal K N] [NumberField ↥N]
    [FiniteDimensional K N'] [Normal K N'] [NumberField ↥N']
    (h : ∀ (B : ValuationSubring K'), B.comap (algebraMap K K') ≠ ⊤ →
      (MulAction.stabilizer Gal(K'/K) B ≤ N.fixingSubgroup ↔
        MulAction.stabilizer Gal(K'/K) B ≤ N'.fixingSubgroup)) :
    N = N' := by
  haveI : IsGalois K K' := IsSepClosure.isGalois
  -- the dictionary at the standard place above each prime
  have hdict : ∀ (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L]
      [NumberField ↥L] (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ((p.asIdeal.primesOver (NumberField.RingOfIntegers ↥L)).ncard = Module.finrank K ↥L) ↔
        MulAction.stabilizer Gal(K'/K)
          (Submission.NeukirchUchida.placeOver (K₁ := K) (K₁' := K') p).1 ≤ L.fixingSubgroup :=
    fun L _ _ _ p =>
      (dictionary_stabilizer_le_fixingSubgroup_iff_splitCompletely (K := K) (K' := K') p
        (Submission.NeukirchUchida.placeOver (K₁ := K) (K₁' := K') p).1
        (Submission.NeukirchUchida.placeOver_spec p)).symm
  -- the completely split primes of `N` and of `N'` agree
  have hsplit : ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      ((p.asIdeal.primesOver (NumberField.RingOfIntegers ↥N)).ncard = Module.finrank K ↥N) ↔
        ((p.asIdeal.primesOver (NumberField.RingOfIntegers ↥N')).ncard = Module.finrank K ↥N') := by
    intro p
    rw [hdict N p, hdict N' p]
    exact h (Submission.NeukirchUchida.placeOver (K₁ := K) (K₁' := K') p).1
      (Submission.NeukirchUchida.placeOver (K₁ := K) (K₁' := K') p).2
  -- the compositum of the two levels
  set M : IntermediateField K K' := N ⊔ N' with hM
  haveI hMfd : FiniteDimensional K M := by rw [hM]; infer_instance
  haveI hMnorm : Normal K M := by rw [hM]; infer_instance
  haveI hMnf : NumberField ↥M := by
    rw [hM]
    exact Commons.NumberTheory.NumberField.numberField_of_intermediateField (N ⊔ N')
  -- the split primes of the compositum
  have hSM : {p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) |
        (p.asIdeal.primesOver (NumberField.RingOfIntegers ↥M)).ncard = Module.finrank K ↥M} =
      {p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) |
        (p.asIdeal.primesOver (NumberField.RingOfIntegers ↥N)).ncard = Module.finrank K ↥N} := by
    ext p
    show ((p.asIdeal.primesOver (NumberField.RingOfIntegers ↥M)).ncard = Module.finrank K ↥M) ↔
      ((p.asIdeal.primesOver (NumberField.RingOfIntegers ↥N)).ncard = Module.finrank K ↥N)
    rw [hdict M p, hdict N p, hM, IntermediateField.fixingSubgroup_sup]
    exact ⟨fun hL => le_trans hL inf_le_left,
      fun h1 => le_inf h1 ((hdict N' p).mp ((hsplit p).mp ((hdict N p).mpr h1)))⟩
  have hSM' : {p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) |
        (p.asIdeal.primesOver (NumberField.RingOfIntegers ↥M)).ncard = Module.finrank K ↥M} =
      {p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) |
        (p.asIdeal.primesOver (NumberField.RingOfIntegers ↥N')).ncard = Module.finrank K ↥N'} := by
    rw [hSM]
    refine Set.ext fun p => ?_
    show ((p.asIdeal.primesOver (NumberField.RingOfIntegers ↥N)).ncard = Module.finrank K ↥N) ↔
      ((p.asIdeal.primesOver (NumberField.RingOfIntegers ↥N')).ncard = Module.finrank K ↥N')
    exact hsplit p
  -- the density argument
  have hmain : ∀ (P : IntermediateField K K') [FiniteDimensional K P] [Normal K P]
      [NumberField ↥P], P ≤ M →
      {p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) |
          (p.asIdeal.primesOver (NumberField.RingOfIntegers ↥M)).ncard = Module.finrank K ↥M} =
        {p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) |
          (p.asIdeal.primesOver (NumberField.RingOfIntegers ↥P)).ncard = Module.finrank K ↥P} →
      P = M := by
    intro P _ _ _ hPM hsets
    haveI hgalP : IsGalois K ↥P :=
      Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
    haveI hgalM : IsGalois K ↥M :=
      Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
    have hdP := Commons.NumberTheory.NumberField.Set.hasDirichletDensity_primes_splitsCompletely
      (K := K) (L := ↥P)
    have hdM := Commons.NumberTheory.NumberField.Set.hasDirichletDensity_primes_splitsCompletely
      (K := K) (L := ↥M)
    rw [hsets] at hdM
    have hδ : (1 : ℝ) / (Module.finrank K ↥P : ℝ) =
        (1 : ℝ) / (Module.finrank K ↥M : ℝ) := tendsto_nhds_unique hdP hdM
    have hfr : Module.finrank K ↥P = Module.finrank K ↥M := by
      have h2 : ((1 : ℝ) / (Module.finrank K ↥P : ℝ))⁻¹ =
          ((1 : ℝ) / (Module.finrank K ↥M : ℝ))⁻¹ := by rw [hδ]
      simpa [one_div] using h2
    exact IntermediateField.eq_of_le_of_finrank_eq hPM hfr
  rw [hM] at hmain
  exact (hmain N le_sup_left hSM).trans (hmain N' le_sup_right hSM').symm

/-! ## The main theorem -/

theorem agreesOnLevels_of_map_decompositionGroup {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂]
    [Field K₁'] [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)}
    (hϕ : IsHomeomorph ϕ) (σ : K₂' ≃+* K₁')
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    (hpres : ∀ (A : ValuationSubring K₁') (hA : A.comap (algebraMap K₁ K₁') ≠ ⊤),
      ((Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') A).map
          (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂))).map
        ((Submission.NeukirchUchida.conjHomEquiv hσ).symm : Gal(K₂'/K₂) →* Gal(K₁'/K₁)) =
        Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') A) :
    NK.Reconstruct.AgreesOnLevels ϕ hϕ σ hσ := by
  intro L hLfd hLnorm hLnf
  haveI : FiniteDimensional K₂ L := hLfd
  haveI : Normal K₂ L := hLnorm
  haveI : NumberField ↥L := hLnf
  set M : IntermediateField K₁ K₁' := sigmaLevel σ hσ L with hM
  haveI hMfd : FiniteDimensional K₁ M := finiteDimensional_sigmaLevel σ hσ L
  haveI hMnorm : Normal K₁ M := normal_sigmaLevel σ hσ L
  -- the fixing subgroup of `L` is the image of that of `M` under conjugation by `σ`
  have hconjfix : (M.fixingSubgroup).map
      ((Submission.NeukirchUchida.conjHomEquiv hσ) : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) =
      L.fixingSubgroup := by
    rw [hM]
    exact Submission.NeukirchUchida.map_fixingSubgroup_conjHomEquiv hσ (image_sigmaLevel σ hσ L)
  haveI hLpfd : FiniteDimensional K₂ (levelMap ϕ M) := finiteDimensional_levelMap hϕ M
  haveI hLpnorm : Normal K₂ (levelMap ϕ M) := normal_levelMap hϕ M
  haveI hLpnf : NumberField ↥(levelMap ϕ M) := numberField_levelMap hϕ M
  refine footprint_eq_of_stabilizer_le_fixingSubgroup (K := K₂) (K' := K₂') ?_
  intro B hB
  change Submission.NeukirchUchida.decompositionGroup (K₁ := K₂) (K₁' := K₂') B ≤
      (levelMap ϕ M).fixingSubgroup ↔
    Submission.NeukirchUchida.decompositionGroup (K₁ := K₂) (K₁' := K₂') B ≤ L.fixingSubgroup
  -- the place of `K₁'` transporting to `B`
  set A : ValuationSubring K₁' := B.comap (σ.symm : K₁' →+* K₂') with hAdef
  have hAcomap : A.comap (σ : K₂' →+* K₁') = B := by
    rw [hAdef, ValuationSubring.comap_comap]
    ext x
    simp
  have hAne : A.comap (algebraMap K₁ K₁') ≠ ⊤ :=
    (comap_sigma_ne_top_iff hσ A).mpr (by rw [hAcomap]; exact hB)
  have hDϕ : (Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') A).map
      (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) =
      Submission.NeukirchUchida.decompositionGroup (K₁ := K₂) (K₁' := K₂') B := by
    rw [← hAcomap]
    exact map_decompositionGroup_eq hσ hpres A hAne
  have hDconj : (Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') A).map
      ((Submission.NeukirchUchida.conjHomEquiv hσ) : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) =
      Submission.NeukirchUchida.decompositionGroup (K₁ := K₂) (K₁' := K₂') B := by
    rw [← hAcomap]
    exact map_conjHomEquiv_decompositionGroup hσ A
  have hfix : (levelMap ϕ M).fixingSubgroup = M.fixingSubgroup.map
      (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) := fixingSubgroup_levelMap hϕ M
  -- both sides reduce to `D_A ≤ Gal(K₁'/M)`
  have key : Submission.NeukirchUchida.decompositionGroup (K₁ := K₂) (K₁' := K₂') B ≤
      (M.fixingSubgroup).map (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) ↔
      Submission.NeukirchUchida.decompositionGroup (K₁ := K₂) (K₁' := K₂') B ≤
        (M.fixingSubgroup).map
          ((Submission.NeukirchUchida.conjHomEquiv hσ) : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) := by
    have hmapϕ : Submission.NeukirchUchida.decompositionGroup (K₁ := K₂) (K₁' := K₂') B =
        (Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') A).map
          (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) := hDϕ.symm
    have hmapconj : Submission.NeukirchUchida.decompositionGroup (K₁ := K₂) (K₁' := K₂') B =
        (Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') A).map
          ((Submission.NeukirchUchida.conjHomEquiv hσ) : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) :=
      hDconj.symm
    constructor
    · intro h
      rw [hmapϕ] at h
      have h1 := (subgroup_map_le_map_iff_of_injective (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂))
        ϕ.injective).mp h
      rw [hmapconj]
      exact Subgroup.map_mono h1
    · intro h
      rw [hmapconj] at h
      have h1 := (subgroup_map_le_map_iff_of_injective
        ((Submission.NeukirchUchida.conjHomEquiv hσ) : Gal(K₁'/K₁) →* Gal(K₂'/K₂))
        (Submission.NeukirchUchida.conjHomEquiv hσ).injective).mp h
      rw [hmapϕ]
      exact Subgroup.map_mono h1
  rw [hfix, ← hconjfix]
  exact key

end NK.Reconstruct
