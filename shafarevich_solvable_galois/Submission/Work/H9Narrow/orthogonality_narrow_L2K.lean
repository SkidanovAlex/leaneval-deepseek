import Mathlib
import Submission.Work.SSGRoute.GrunwaldEscapeCore.escape_vocab
import Submission.Work.SSGRoute.GrunwaldEscapeCore.OrthL2KImports
import Submission.Work.SSGRoute.GrunwaldEscapeCore.CommonsValuationImports
import Submission.Work.SSGRoute.H9.NarrowMu2
import Submission.Work.SSGRoute.H9.two_core
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.H9Narrow

open _root_.SSGRoute
open scoped Pointwise
open NumberField IsDedekindDomain
open NK.GlobalCFT

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

/-! ## The narrow one-place idèles

A one-place idèle at a *finite* place has archimedean component `1`, hence lies in the narrow
`E_{T,unr}` as soon as it lies in the wide one.  This is the only new input the narrow orthogonality
needs in place of its wide twin. -/

/-- **A one-place idèle at a local unit outside `T'` lies in the narrow `E_{T,unr}`.** -/
theorem onePlace_mem_narrowPowTIdeles_of_mem_localUnits {κ : Type} [Field κ] [NumberField κ]
    (p : ℕ) (T' : Finset (NK.Chebotarev.PrimeIdeal κ)) (𝔮 : NK.Chebotarev.PrimeIdeal κ)
    (h𝔮T : 𝔮 ∉ T')
    (u : (NK.GlobalCFT.Place.localField κ (NK.GlobalCFT.Place.ofFinite 𝔮))ˣ)
    (hu : u ∈ NK.GlobalCFT.Place.localUnits κ (NK.GlobalCFT.Place.ofFinite 𝔮)) :
    NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔮) u ∈
      Work.SSGRoute.H9.narrowPowTIdeles κ p T' := by
  rw [Work.SSGRoute.H9.mem_narrowPowTIdeles]
  refine ⟨Work.GrunwaldEscapeCore.onePlace_mem_powTIdeles_of_mem_localUnits p T' 𝔮 h𝔮T u hu,
    fun w => ?_⟩
  rw [NK.HassePrinciple.onePlace_apply_ne (Place.ofInfinite_ne_ofFinite w 𝔮)]
  exact Work.SSGRoute.H9.isPosInf_one κ w

/-- **A one-place idèle over a prime with `p ∣ v_𝔮(b)` lies in the narrow `U' ⊔ C^p`.** -/
theorem onePlace_mem_narrowGesU_sup_pPow_of_dvd_log {κ : Type} [Field κ] [NumberField κ]
    (p : ℕ) [Fact p.Prime]
    (T' : Finset (NK.Chebotarev.PrimeIdeal κ)) (𝔮 : NK.Chebotarev.PrimeIdeal κ)
    (h𝔮T : 𝔮 ∉ T') (b : κˣ)
    (hdvd : (p : ℤ) ∣ (𝔮.valuation κ (b : κ)).log) :
    NK.GlobalCFT.IdeleClassGroup.mk κ
        (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔮)
          (NK.CFTLib.IdeleHasse.localImageAt (K := κ) (NK.GlobalCFT.Place.ofFinite 𝔮) b)) ∈
      Work.SSGRoute.H9.narrowGesU κ p T' ⊔
        Work.SSGRoute.EscapeCoreLib.pPowSubgroup p (NK.GlobalCFT.IdeleClassGroup κ) := by
  classical
  obtain ⟨γ, u, hu, hγu⟩ :=
    Work.SSGRoute.ZDataMup.LocalUnramified.exists_pow_mul_mem_localUnits_of_dvd_log
      𝔮 p Fact.out b hdvd
  have hl : NK.CFTLib.IdeleHasse.localImageAt (K := κ) (NK.GlobalCFT.Place.ofFinite 𝔮) b =
      γ ^ p * u := hγu
  have hsplit : NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔮)
      (NK.CFTLib.IdeleHasse.localImageAt (K := κ) (NK.GlobalCFT.Place.ofFinite 𝔮) b) =
      (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔮) γ) ^ p *
        NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔮) u := by
    rw [hl, NK.CFTLib.IdeleHasse.onePlace_mul, Work.GrunwaldEscapeCore.onePlace_pow_local]
  rw [hsplit, map_mul, map_pow]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_right
    (Work.SSGRoute.EscapeCoreLib.pow_mem_pPowSubgroup _)) (Subgroup.mem_sup_left ?_)
  refine Subgroup.mem_map.mpr ⟨_, Subgroup.mem_sup_right ?_, rfl⟩
  exact onePlace_mem_narrowPowTIdeles_of_mem_localUnits p T' 𝔮 h𝔮T u hu

/-- **The narrow one-place membership from the Kummer-inertia criterion.** -/
theorem onePlace_mem_narrowGesU_of_kummerChar_eq_zero_on_inertia {κ Ω : Type} [Field κ]
    [NumberField κ] [Field Ω] [Algebra κ Ω] [IsAlgClosure κ Ω] [IsAlgClosed Ω]
    (p : ℕ) [Fact p.Prime]
    (ζ : κ) (hζ : IsPrimitiveRoot ζ p)
    (T' : Finset (NK.Chebotarev.PrimeIdeal κ))
    (B : ValuationSubring Ω) (hB : SSGRoute.IsFinPlace κ B)
    (𝔮 : NK.Chebotarev.PrimeIdeal κ)
    (h𝔮 : B.comap (algebraMap κ Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime κ 𝔮)
    (h𝔮T : 𝔮 ∉ T')
    (hp : ¬ B.valuation (p : Ω) < 1)
    (b : κˣ)
    (hb : ∀ σ : Ω ≃ₐ[κ] Ω, SSGRoute.IsInertia (k := κ) B σ →
      Work.SSGRoute.kummerCharZMod (K := κ) (Ω := Ω) p (ζ := ζ) hζ b σ = 0) :
    NK.GlobalCFT.IdeleClassGroup.mk κ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔮)
        (NK.CFTLib.IdeleHasse.localImageAt (K := κ) (NK.GlobalCFT.Place.ofFinite 𝔮) b)) ∈
      Work.SSGRoute.H9.narrowGesU κ p T' ⊔
        Work.SSGRoute.EscapeCoreLib.pPowSubgroup p (NK.GlobalCFT.IdeleClassGroup κ) :=
  onePlace_mem_narrowGesU_sup_pPow_of_dvd_log p T' 𝔮 h𝔮T b
    (Work.GrunwaldEscapeCore.dvd_log_of_kummerChar_eq_zero_on_inertia_aux p ζ hζ B hB 𝔮 h𝔮 b hb)

/-- **Unramifiedness outside `T'` from the narrow unit idèles.** -/
theorem isUnramifiedIn_of_narrowUnitIdeles_le_normClassSubgroup (p : ℕ) [Fact p.Prime]
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (T' : Finset (NK.Chebotarev.PrimeIdeal ↥K))
    (M : IntermediateField ↥K Ω) [FiniteDimensional ↥K M] [IsGalois ↥K M] [NumberField ↥M]
    [IsMulCommutative (↥M ≃ₐ[↥K] ↥M)]
    (hM : Work.SSGRoute.H9.narrowGesU ↥K p T' ≤ NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥M)
    (𝔮 : NK.Chebotarev.PrimeIdeal ↥K) (h𝔮 : 𝔮 ∉ T') :
    NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥M) 𝔮 := by
  have hloc : NK.GlobalCFT.Place.localUnits ↥K (NK.GlobalCFT.Place.ofFinite 𝔮) ≤
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥M)
        (NK.GlobalCFT.Place.ofFinite 𝔮) := by
    intro u hu
    have hz : NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔮) u ∈
        Work.SSGRoute.H9.narrowPowTIdeles ↥K p T' :=
      onePlace_mem_narrowPowTIdeles_of_mem_localUnits p T' 𝔮 h𝔮 u hu
    have hz' : (NK.GlobalCFT.IdeleClassGroup.mk ↥K)
        (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔮) u) ∈
        Work.SSGRoute.H9.narrowGesU ↥K p T' :=
      Subgroup.mem_map.mpr ⟨_, Subgroup.mem_sup_right hz, rfl⟩
    exact Work.SSGRoute.N2v2.onePlace_mem_localNormSubgroup_of_mem_normClassSubgroup 𝔮 u (hM hz')
  exact Work.SSGRoute.N2v2.ramificationIdx_eq_one_of_localUnits_le_localNormSubgroup 𝔮 hloc

/-! ## The narrow level field

`narrow_levelField`: the narrow twin of `Work.SSGRoute.N2v2.exists_levelField_of_gesUPow_subfield_N`
— the level field `F ≤ N` whose norm class subgroup is the *narrow* modulus `U' ⊔ N_{N/↥K}C_N`.  The
proof is that of the wide theorem verbatim: it never uses any property of `U'` beyond `U' ⊔ W ⊇ W`,
and the existence theorem it invokes needs no openness or finite-index hypothesis. -/

theorem narrow_levelField (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (L₁ L₂ : IntermediateField k Ω) [FiniteDimensional k L₁] [IsGalois k L₁]
    [FiniteDimensional k L₂] [IsGalois k L₂] (hKL₁ : K ≤ L₁) (hKL₂ : K ≤ L₂)
    (T' : Finset (NK.Chebotarev.PrimeIdeal ↥K))
    (N : IntermediateField ↥K Ω) [FiniteDimensional ↥K N] [IsGalois ↥K N] [NumberField ↥N]
    (hN : (N : Set Ω) = ((L₁ ⊔ L₂ : IntermediateField k Ω) : Set Ω)) :
    ∃ (F : IntermediateField ↥K Ω) (_ : FiniteDimensional ↥K F) (_ : IsGalois ↥K F)
      (_ : NumberField ↥F) (_ : IsMulCommutative (↥F ≃ₐ[↥K] ↥F)),
      F ≤ N ∧
      NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥F =
        (Work.SSGRoute.H9.narrowGesU ↥K p T' ⊔
          Work.SSGRoute.EscapeCoreLib.pPowSubgroup p (NK.GlobalCFT.IdeleClassGroup ↥K))
        ⊔ NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥N := by
  classical
  haveI hNumK : NumberField ↥K := NumberField.of_module_finite k ↥K
  set U' : Subgroup (IdeleClassGroup ↥K) :=
    Work.SSGRoute.H9.narrowGesU ↥K p T' ⊔
      Work.SSGRoute.EscapeCoreLib.pPowSubgroup p (IdeleClassGroup ↥K) with hU'
  set W : Subgroup (IdeleClassGroup ↥K) := Idele.normClassSubgroup ↥K ↥N with hW
  -- ## (i) the norm-limitation theorem inside `N`
  obtain ⟨A, hAgal, hAcomm, hAle⟩ :=
    Work.SSGRoute.CFTSide.exists_abelian_subextension_normClassSubgroup_le
      NK.CFTLib.fundamentalClassElement (K := ↥K) (L := ↥N) W le_rfl
  haveI : IsGalois ↥K ↥A := hAgal
  haveI : IsMulCommutative (↥A ≃ₐ[↥K] ↥A) := hAcomm
  have hAeq : Idele.normClassSubgroup ↥K ↥A = W := by
    refine le_antisymm hAle ?_
    rw [hW]
    exact Idele.normClassSubgroup_le_of_tower (K := ↥K) (L := ↥A) (M := ↥N)
  -- ## (ii) the norm-group correspondence inside the abelian extension `A/↥K`
  obtain ⟨E, hEgal, hEnorm, hEdeg⟩ :=
    NK.CFTLib.Existence.exists_intermediateField_normClassSubgroup_eq_of_index
      NK.CFTLib.artinReciprocityIdeal_proved NK.CFTLib.fundamentalClassElement
      (K := ↥K) (L := ↥A) (U' ⊔ W) (by rw [hAeq]; exact le_sup_right)
  haveI : IsGalois ↥K ↥E := hEgal
  -- ## (iii) transport `E ⊆ A ⊆ N` into `Ω`
  let f : ↥A →ₐ[↥K] Ω := (IntermediateField.val N).comp (IntermediateField.val A)
  let F : IntermediateField ↥K Ω := E.map f
  have hFN : F ≤ N := by
    intro x hx
    rw [IntermediateField.mem_map] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact (IntermediateField.val A y).2
  haveI hFfd : FiniteDimensional ↥K ↥F :=
    FiniteDimensional.of_injective
      (IntermediateField.equivMap E f).symm.toLinearEquiv.toLinearMap
      (IntermediateField.equivMap E f).symm.injective
  haveI hFgal : IsGalois ↥K ↥F := IsGalois.of_algEquiv (IntermediateField.equivMap E f)
  haveI hFnf : NumberField ↥F := NumberField.of_module_finite ↥K ↥F
  haveI hEcomm : IsMulCommutative (↥E ≃ₐ[↥K] ↥E) := by
    refine IsMulCommutative.of_comm fun a b => ?_
    obtain ⟨a', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := ↥K) (K₁ := ↥E) (E := ↥A) a
    obtain ⟨b', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := ↥K) (K₁ := ↥E) (E := ↥A) b
    rw [← map_mul, ← map_mul, mul_comm']
  haveI hFcomm : IsMulCommutative (↥F ≃ₐ[↥K] ↥F) := by
    refine IsMulCommutative.of_comm fun a b => ?_
    let e := AlgEquiv.autCongr (IntermediateField.equivMap E f)
    have h := mul_comm' (e.symm a) (e.symm b)
    exact e.symm.injective (by rw [map_mul, map_mul, h])
  have hFnorm : Idele.normClassSubgroup ↥K ↥F = U' ⊔ W := by
    rw [← hEnorm]
    exact SetLike.ext fun x =>
      (Work.SSGRoute.Sha2Lib.mem_normClassSubgroup_iff_of_algEquiv
        (IntermediateField.equivMap E f) x).symm
  exact ⟨F, hFfd, hFgal, hFnf, hFcomm, hFN, hFnorm⟩

/-! ## The narrow `g`-sum

The `p = 2` `g`-sum of the orthogonality, with the hypothesis `χ` kills the *narrow* modulus.  It is
a verbatim copy of `Work.SSGRoute.ZDataTwo.gsum_trichotomy_two` with the one use of the wide
membership `onePlace_mem_gesU_of_kummerChar_eq_zero_on_inertia` replaced by its narrow twin
`onePlace_mem_narrowGesU_of_kummerChar_eq_zero_on_inertia`. -/

theorem gsum_trichotomy_two_narrow
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2)
    (N : IntermediateField k Ω) [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, Work.SSGRoute.gesKConj K A B → A = B)
    (hTcov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (B.valuation (2 : Ω) < 1 ∨
        (∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ N.fixingSubgroup)) →
      ∃ A ∈ T, Work.SSGRoute.gesKConj K A B)
    (g : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hgram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) → ¬ SSGRoute.IsSplitIn k N B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → g σ = 0)
    (T' : Finset (NK.Chebotarev.PrimeIdeal ↥K))
    (hTbelow : ∀ A ∈ T, ∃ 𝔭 ∈ T', A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (N' : IntermediateField ↥K Ω) [FiniteDimensional ↥K N'] [IsGalois ↥K N'] [NumberField ↥N']
    (hNN' : (N' : Set Ω) = (N : Set Ω))
    (χ : NK.GlobalCFT.IdeleClassGroup ↥K →* Multiplicative (ZMod 2))
    (hχU : Work.SSGRoute.H9.narrowGesU ↥K 2 T' ⊔
      Work.SSGRoute.EscapeCoreLib.pPowSubgroup 2 (NK.GlobalCFT.IdeleClassGroup ↥K) ≤ χ.ker)
    (hχW : NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥N' ≤ χ.ker)
    (bg : (↥K)ˣ)
    (hbg : ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup),
      g σ = Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ bg
        (Work.SSGRoute.gesGalKOfFixing K σ hσ))
    (harch : ∀ w : NumberField.InfinitePlace ↥K,
      NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofInfinite w) bg ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥N') (Place.ofInfinite w)) :
    (∏ 𝔭 ∈ T', χ (IdeleClassGroup.mk ↥K
        (NK.HassePrinciple.onePlace (Place.ofFinite 𝔭)
          (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔭) bg)))) = 1 := by
  classical
  haveI hNumK : NumberField ↥K := NumberField.of_module_finite k ↥K
  haveI hAlgCl : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
  let Ψ : Idele ↥K →* Multiplicative (ZMod 2) := χ.comp (IdeleClassGroup.mk ↥K)
  have hprin : ∀ y : (↥K)ˣ, Ψ (Idele.principalIdele ↥K y) = 1 := by
    intro y
    show χ (IdeleClassGroup.mk ↥K (Idele.principalIdele ↥K y)) = 1
    rw [show IdeleClassGroup.mk ↥K (Idele.principalIdele ↥K y) = 1 from by
      rw [← MonoidHom.mem_ker, Work.SSGRoute.ker_mk_eq_principal]
      exact Idele.mem_principalSubgroup.mpr ⟨y, rfl⟩]
    exact map_one χ
  have hnorm : ∀ y : Idele ↥N', Ψ (Idele.normIdeleHom ↥K ↥N' y) = 1 := by
    intro y
    refine hχW ?_
    exact Subgroup.mem_map.mpr ⟨_, Idele.mem_normImage.mpr ⟨y, fun v => rfl⟩, rfl⟩
  have hs : ∀ v : Place ↥K, v ∉ T'.image Place.ofFinite →
      Ψ (NK.HassePrinciple.onePlace v
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) v bg)) = 1 := by
    intro v hv
    rcases v with w | 𝔮
    · -- an archimedean place: the local image is a local norm by `harch`
      have hmem : NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofInfinite w) bg ∈
          NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥N')
            (Place.ofInfinite w) := harch w
      have hnormimg : NK.HassePrinciple.onePlace (Place.ofInfinite w)
          (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofInfinite w) bg) ∈
          Idele.normImage ↥K ↥N' :=
        (NK.CFTLib.IdeleHasse.onePlace_ofInfinite_mem_normImage_iff (K := ↥K) (L := ↥N')
          w _).mpr hmem
      obtain ⟨y, hy⟩ := Idele.mem_normImage.mp hnormimg
      rw [show NK.HassePrinciple.onePlace (Place.ofInfinite w)
            (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofInfinite w) bg) =
          Idele.normIdeleHom ↥K ↥N' y from Idele.ext (fun v => hy v)]
      exact hnorm y
    · -- a finite place `𝔮 ∉ T'`
      have h𝔮T : 𝔮 ∉ T' := fun h => hv (Finset.mem_image_of_mem _ h)
      obtain ⟨B, hBcomap⟩ := Commons.RingTheory.Valuation.exists_valuationSubring_comap_eq
        (K := ↥K) (L := Ω) (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔮)
      have hBK : SSGRoute.IsFinPlace ↥K B := by
        rw [SSGRoute.IsFinPlace, hBcomap]
        exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top 𝔮
      have hBfin : SSGRoute.IsFinPlace k B :=
        (Work.SSGRoute.isFinPlace_baseChange k Ω K B).mp hBK
      -- `2` is a unit at `B`, since the places over `2` lie in the classes of `T`
      have h2val : ¬ B.valuation (2 : Ω) < 1 := by
        intro hlt
        obtain ⟨A, hA, hconj⟩ := hTcov B hBfin (Or.inl hlt)
        obtain ⟨τ, hτ, hτA⟩ := hconj
        obtain ⟨𝔭, h𝔭T', h𝔭A⟩ := hTbelow A hA
        have hB𝔭 : B.comap (algebraMap ↥K Ω) =
            IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 := by
          rw [← hτA, ← h𝔭A]
          have hcoe : ⇑((IntermediateField.fixingSubgroupEquiv K) ⟨τ, hτ⟩) = ⇑τ :=
            funext fun _ => rfl
          rw [(Work.SSGRoute.GrunwaldEscapeCore.gesSmulEqOfCoeEq K hcoe A).symm]
          exact Commons.NumberTheory.NumberField.Valuation.comap_smul_algebraMap A _
        rw [hBcomap] at hB𝔭
        exact h𝔮T (Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := ↥K)
          hB𝔭 ▸ h𝔭T')
      by_cases hsplit : SSGRoute.IsSplitIn k N B
      · have hmem : IdeleClassGroup.mk ↥K (NK.HassePrinciple.onePlace (Place.ofFinite 𝔮)
            (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔮) bg)) ∈
            NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥N' :=
          Work.GrunwaldEscapeCore.mk_onePlace_mem_normClassSubgroup_of_isSplitIn 2 K B hBfin
            𝔮 hBcomap N N' hNN' hsplit bg
        simpa [Ψ] using hχW hmem
      · -- the inertia criterion: `2 ∣ v_𝔮(bg)`, so the term lies in the **narrow** `U'`
        have hnotT : ∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B := by
          intro A hA hconj
          obtain ⟨τ, hτ, hτA⟩ := hconj
          obtain ⟨𝔭, h𝔭T', h𝔭A⟩ := hTbelow A hA
          have hB𝔭 : B.comap (algebraMap ↥K Ω) =
              IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 := by
            rw [← hτA, ← h𝔭A]
            have hcoe : ⇑((IntermediateField.fixingSubgroupEquiv K) ⟨τ, hτ⟩) = ⇑τ :=
              funext fun _ => rfl
            rw [(Work.SSGRoute.GrunwaldEscapeCore.gesSmulEqOfCoeEq K hcoe A).symm]
            exact Commons.NumberTheory.NumberField.Valuation.comap_smul_algebraMap A _
          rw [hBcomap] at hB𝔭
          exact h𝔮T (Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := ↥K)
            hB𝔭 ▸ h𝔭T')
        have hb0 : ∀ σ : Ω ≃ₐ[↥K] Ω, SSGRoute.IsInertia (k := ↥K) B σ →
            Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ bg σ = 0 := by
          intro σ hσ
          let τu : ↥(K.fixingSubgroup) := (IntermediateField.fixingSubgroupEquiv K).symm σ
          have hfix : (IntermediateField.fixingSubgroupEquiv K) τu = σ :=
            (IntermediateField.fixingSubgroupEquiv K).apply_symm_apply σ
          have hτI : SSGRoute.IsInertia k B (τu : Ω ≃ₐ[k] Ω) :=
            (Work.SSGRoute.isInertia_baseChange k Ω K B (τu : Ω ≃ₐ[k] Ω) τu.2).mp
              (by rw [hfix]; exact hσ)
          have hg0 : g (τu : Ω ≃ₐ[k] Ω) = 0 := hgram B hBfin hnotT hsplit _ τu.2 hτI
          have hbτ := hbg (τu : Ω ≃ₐ[k] Ω) τu.2
          rw [show Work.SSGRoute.gesGalKOfFixing K (τu : Ω ≃ₐ[k] Ω) τu.2 = σ from by
            rw [Work.SSGRoute.gesGalKOfFixing]
            rw [show (⟨(τu : Ω ≃ₐ[k] Ω), τu.2⟩ : ↥(K.fixingSubgroup)) = τu from rfl, hfix]] at hbτ
          rw [← hbτ, hg0]
        have hmem : IdeleClassGroup.mk ↥K (NK.HassePrinciple.onePlace (Place.ofFinite 𝔮)
            (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔮) bg)) ∈
            Work.SSGRoute.H9.narrowGesU ↥K 2 T' ⊔
              Work.SSGRoute.EscapeCoreLib.pPowSubgroup 2 (IdeleClassGroup ↥K) :=
          onePlace_mem_narrowGesU_of_kummerChar_eq_zero_on_inertia 2 (ζ := ζ) hζ
            T' B hBK 𝔮 hBcomap h𝔮T h2val bg hb0
        simpa [Ψ] using hχU hmem
  have hmain :=
    Work.GrunwaldEscapeCore.prod_localFactor_eq_one_of_comm (p := 2) (K := ↥K) (L := ↥N')
      Ψ hprin hnorm bg (T'.image Place.ofFinite) hs
  rwa [Finset.prod_image (f := fun v : Place ↥K => Ψ (NK.HassePrinciple.onePlace v
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) v bg)))
      (s := T') (g := Place.ofFinite)
      (fun x _ y _ hxy => Place.ofFinite_inj.mp hxy)] at hmain

/-! ## The narrow per-character orthogonality

`orth_two_chi_narrow`: the narrow twin of `Work.SSGRoute.H9.orth_two_chi`.  Every character of
`C_↥K` with values in `μ₂` that kills `narrowGesU ↥K 2 T' ⊔ C_↥K²` and the norm class subgroup of
`N'` kills the class of the `T'`-free part of the divisor of `a`.  The proof is a verbatim copy of
`orth_two_chi` with the wide inputs (the level field, its unramifiedness outside `T'`, the `g`-sum)
replaced by their narrow twins. -/
theorem orth_two_chi_narrow
    (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2)
    (N : IntermediateField k Ω) [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, Work.SSGRoute.gesKConj K A B → A = B)
    (hTcov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (B.valuation (2 : Ω) < 1 ∨
        (∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ N.fixingSubgroup)) →
      ∃ A ∈ T, Work.SSGRoute.gesKConj K A B)
    (g : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hg : ∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, g (x * y) = g x + g y)
    (hgc : SSGRoute.IsLocConstOn K.fixingSubgroup g)
    (hgram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) → ¬ SSGRoute.IsSplitIn k N B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → g σ = 0)
    (hginf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → g c = 0)
    (h : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hh : ∀ A ∈ T, ∀ x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      ∀ y ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A (x * y) = h A x + h A y)
    (hhc : ∀ A ∈ T, ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      ∀ x ∈ U, x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup → h A x = 0)
    (horth₁ : ∀ A ∈ T,
      (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A σ = 0) ∨
      (∀ χ : (Ω ≃ₐ[k] Ω) → ZMod 2,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
        (∀ σ ∈ N.fixingSubgroup, χ σ = 0) →
        ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, χ σ = 0) ∨
      ((∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → h A σ = 0) ∧
        ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod 2,
          (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
          (∀ σ ∈ N.fixingSubgroup, χ σ = 0) →
          ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → χ σ = 0))
    (hinertia : ∀ A ∈ T, ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ →
      g σ + h A σ = 0)
    (T' : Finset (NK.Chebotarev.PrimeIdeal ↥K))
    (hTbelow : ∀ A ∈ T, ∃ 𝔭 ∈ T', A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (hT'above : ∀ 𝔭 ∈ T', ∃ A ∈ T, A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (N' : IntermediateField ↥K Ω) [FiniteDimensional ↥K N'] [IsGalois ↥K N'] [NumberField ↥N']
    (hNN' : (N' : Set Ω) = (N : Set Ω))
    (a : (↥K)ˣ)
    (ha : ∀ A ∈ T, ∀ σ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
      g (σ : Ω ≃ₐ[k] Ω) + h A (σ : Ω ≃ₐ[k] Ω) =
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ a
          (Work.SSGRoute.gesLocalToGalK K σ))
    (hapos : ∀ (c : Ω ≃ₐ[k] Ω) (hc : c ∈ K.fixingSubgroup), c ^ 2 = 1 →
      Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ a
        (Work.SSGRoute.gesGalKOfFixing K c hc) = 0)
    (χ : NK.GlobalCFT.IdeleClassGroup ↥K →* Multiplicative (ZMod 2))
    (hχU : Work.SSGRoute.H9.narrowGesU ↥K 2 T' ⊔
      Work.SSGRoute.EscapeCoreLib.pPowSubgroup 2 (NK.GlobalCFT.IdeleClassGroup ↥K) ≤ χ.ker)
    (hχW : NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥N' ≤ χ.ker) :
    χ (NK.GlobalCFT.IdeleClassGroup.mk ↥K
      (NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart (K := ↥K) T' a))) = 1 := by
  classical
  haveI hNumK : NumberField ↥K := NumberField.of_module_finite k ↥K
  haveI hCFT : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
  -- ## 1. the level field `F ≤ N'` with `N_F = narrowGesU ⊔ C² ⊔ N_{N'}`
  obtain ⟨F, hFfd, hFgal, hFnf, hFcomm, hFleN', hFnorm⟩ :=
    narrow_levelField 2 k Ω K N K hKN le_rfl T' N'
      (by rw [show (N ⊔ K : IntermediateField k Ω) = N from sup_eq_left.mpr hKN]; exact hNN')
  haveI hFfdI : FiniteDimensional ↥K F := hFfd
  haveI hFgalI : IsGalois ↥K F := hFgal
  haveI hFnfI : NumberField ↥F := hFnf
  haveI hFcommI : IsMulCommutative (↥F ≃ₐ[↥K] ↥F) := hFcomm
  -- ## 2. the Artin map of `F/↥K`, with all clauses
  have hp2F : Work.SSGRoute.EscapeCoreLib.pPowSubgroup 2
      (NK.GlobalCFT.IdeleClassGroup ↥K) ≤ NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥F := by
    rw [hFnorm]
    exact le_trans le_sup_right le_sup_left
  obtain ⟨Φ, hΦker, hΦloc, hΦfrob, hΦprod, hΦexp, hΦlift, hΦunith⟩ :=
    Work.SSGRoute.ZDataTwo.artinMap_fullClauses_of_levelField k Ω K F hp2F
  -- ## 3. `χ` descends to `Gal(F/↥K)`
  have hχFker : NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥F ≤ χ.ker := by
    rw [hFnorm]
    exact sup_le hχU hχW
  obtain ⟨χF, hχFart⟩ :=
    Work.SSGRoute.ZDataTwo.exists_levelCharacter_of_classCharacter k Ω K F Φ hΦker hΦfrob χ hχFker
  -- ## 4. its Kummer element `c`, with `↥K⟮c^{1/2}⟯ ≤ F`
  haveI hFnormI : Normal ↥K F := hFgal.to_normal
  obtain ⟨c, hcF, hχFkum⟩ :=
    Work.SSGRoute.N2v2.exists_kummerChar_of_vanishes_on_fixingSubgroup 2 k Ω K ζ hζ F F χF
      (by
        intro σ hσ
        have h1 : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) F σ = 1 := by
          rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker (K := ↥K) (L := Ω) F]
          exact hσ
        rw [h1, map_one])
  -- ## 5. `F/↥K` is unramified outside `T'`
  have hFunr : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥K, 𝔮 ∉ T' →
      NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥F) 𝔮 :=
    fun 𝔮 h𝔮 => isUnramifiedIn_of_narrowUnitIdeles_le_normClassSubgroup 2 k Ω K T' F
      (by rw [hFnorm]; exact le_trans le_sup_left le_sup_left) 𝔮 h𝔮
  -- ## 6. the Kummer element `bg` of the datum `g`
  obtain ⟨bg, hbg⟩ :=
    Work.SSGRoute.ZDataMup.KummerSurjectivity.kummerCharZMod_surjective_levelK 2 k Ω K ζ hζ g
      hg hgc
  -- ## 7. the big level `E ⊇ F ⊔ ↥K⟮a^{1/2}⟯ ⊔ ↥K⟮bg^{1/2}⟯`, abelian of exponent `2`
  have hFa := Work.SSGRoute.N2v2.kummerField_data 2 K ζ hζ a
  have hFbg := Work.SSGRoute.N2v2.kummerField_data 2 K ζ hζ bg
  haveI hFa_fd : FiniteDimensional ↥K (NK.LocalAnabelian.kummerField (K' := Ω) 2 a) := hFa.1
  haveI hFa_gal : IsGalois ↥K (NK.LocalAnabelian.kummerField (K' := Ω) 2 a) := hFa.2.1
  haveI hFa_nf : NumberField ↥(NK.LocalAnabelian.kummerField (K' := Ω) 2 a) := hFa.2.2.1
  haveI hFa_cm : IsMulCommutative (↥(NK.LocalAnabelian.kummerField (K' := Ω) 2 a) ≃ₐ[↥K]
    ↥(NK.LocalAnabelian.kummerField (K' := Ω) 2 a)) := hFa.2.2.2.1
  haveI hFbg_fd : FiniteDimensional ↥K (NK.LocalAnabelian.kummerField (K' := Ω) 2 bg) := hFbg.1
  haveI hFbg_gal : IsGalois ↥K (NK.LocalAnabelian.kummerField (K' := Ω) 2 bg) := hFbg.2.1
  haveI hFbg_nf : NumberField ↥(NK.LocalAnabelian.kummerField (K' := Ω) 2 bg) := hFbg.2.2.1
  haveI hFbg_cm : IsMulCommutative (↥(NK.LocalAnabelian.kummerField (K' := Ω) 2 bg) ≃ₐ[↥K]
    ↥(NK.LocalAnabelian.kummerField (K' := Ω) 2 bg)) := hFbg.2.2.2.1
  obtain ⟨E, hEfd, hEgal, hEcomm, hEnf, hFE, hFaE, hFbgE, _h2, _h3, hexpE⟩ :=
    Work.SSGRoute.N2v2.sup5_abelian_expP (k := k) (Ω := Ω) 2 K F
      (NK.LocalAnabelian.kummerField (K' := Ω) 2 a)
      (NK.LocalAnabelian.kummerField (K' := Ω) 2 bg) F F
      hΦexp hFa.2.2.2.2 hFbg.2.2.2.2 hΦexp hΦexp
  haveI hEfdI : FiniteDimensional ↥K E := hEfd
  haveI hEgalI : IsGalois ↥K E := hEgal
  haveI hEcommI : IsMulCommutative (↥E ≃ₐ[↥K] ↥E) := hEcomm
  haveI hEnfI : NumberField ↥E := hEnf
  -- ## 8. the Artin map of `E`, its local family `θ`, and the diagonal
  obtain ⟨ΦE, hΦEker, hΦEloc, hΦEfrob, hΦEprod, hΦElift, hΦEunith⟩ :=
    Work.SSGRoute.N2v2.exists_artinMap_fullClauses (K := K) E
  let θ : (v : NK.GlobalCFT.Place ↥K) →
      (NK.GlobalCFT.Place.localField ↥K v)ˣ →* (↥E ≃ₐ[↥K] ↥E) :=
    fun v => ΦE.comp (NK.CFTLib.IdeleHasse.onePlaceHom (K := ↥K) v)
  have hdiagLift : ∀ 𝔭 ∈ T', ∃ σ₀ : Ω ≃ₐ[↥K] Ω,
      ∀ (y : (↥K)ˣ), NK.LocalAnabelian.kummerField (K' := Ω) 2 y ≤ E →
      ∀ τ : Ω ≃ₐ[↥K] Ω,
        AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E τ =
          θ (NK.GlobalCFT.Place.ofFinite 𝔭)
            (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) y) →
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ y τ =
          Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ y σ₀ := by
    intro 𝔭 _
    exact Work.SSGRoute.N2v2.hdiag_E 2 K ζ hζ E ΦE 𝔭
      (fun c' hc' => Work.SSGRoute.N2v2.hdata_of_kummerField_le 2 K ζ hζ E ΦE hΦEker hΦEfrob
        𝔭 c' hc')
  -- ## 9. `χ` as a Kummer character at the level `E`
  obtain ⟨χE₁, hχE₁⟩ :=
    Work.SSGRoute.N2v2.exists_kummerChar_level 2 k Ω K ζ hζ E c (le_trans hcF hFE)
  -- ## 10. `g` kills the fixing subgroup of `E`
  have hgE : ∀ σ : Ω ≃ₐ[↥K] Ω, σ ∈ E.fixingSubgroup → g (σ.restrictScalars k) = 0 := by
    intro σ hσE
    have hσK : σ.restrictScalars k ∈ K.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact σ.commutes ⟨x, hx⟩
    rw [hbg (σ.restrictScalars k) hσK,
      Work.SSGRoute.N2v2.fixingSubgroupEquiv_restrictScalars_apply K σ hσK]
    exact Work.SSGRoute.N2v2.kummerCharZMod_eq_zero_of_kummerField_le 2 k Ω K ζ hζ bg E hFbgE
      σ hσE
  -- ## 11. the bridge `χ (mk y) = χE₁ (ΦE y)`
  have hbridge : ∀ y : NK.GlobalCFT.Idele ↥K, χF (Φ y) = χE₁ (ΦE y) := by
    intro y
    obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (F := ↥K) (K₁ := E) (E := Ω) (ΦE y)
    have hFσ : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) F σ = Φ y :=
      Work.SSGRoute.N2v2.restrictNormalHom_artinMap_eq_of_le 2 K F E hFE Φ hΦker hΦfrob ΦE
        hΦEker hΦEfrob σ y hσ
    calc χF (Φ y) = χF (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) F σ) := by rw [hFσ]
      _ = Multiplicative.ofAdd (Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ c σ)
            := hχFkum σ
      _ = χE₁ (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E σ) := (hχE₁ σ).symm
      _ = χE₁ (ΦE y) := by rw [hσ]
  -- ## 12. the archimedean input for `bg` and the `g`-sum
  have hbginf : ∀ (c' : Ω ≃ₐ[k] Ω) (hc' : c' ∈ K.fixingSubgroup), c' ^ 2 = 1 →
      Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ bg
        (Work.SSGRoute.gesGalKOfFixing K c' hc') = 0 := by
    intro c' hc' hc'2
    have h1 : Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ bg
        (Work.SSGRoute.gesGalKOfFixing K c' hc') = g c' := (hbg c' hc').symm
    rw [h1]
    exact hginf c' hc' hc'2
  have harchbg := Work.SSGRoute.ZDataTwo.arch_localNorm_of_involution_condition k Ω K ζ hζ bg N'
    hbginf
  have hbgprod : (∏ 𝔭 ∈ T', χ (NK.GlobalCFT.IdeleClassGroup.mk ↥K
      (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) bg)))) = 1 :=
    gsum_trichotomy_two_narrow k Ω K ζ hζ N hKN T hTfin hTdisj hTcov g hgram
      T' hTbelow N' hNN' χ hχU hχW bg hbg harchbg
  have hgsum : (∑ 𝔭 ∈ T', (χE₁ (θ (NK.GlobalCFT.Place.ofFinite 𝔭)
      (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) bg))).toAdd) = 0 := by
    rw [← Work.SSGRoute.GrunwaldEscapeCore.toAdd_prod_eq_sum 2 T'
      (fun 𝔭 => χE₁ (θ (NK.GlobalCFT.Place.ofFinite 𝔭)
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) bg)))]
    rw [show (∏ 𝔭 ∈ T', χE₁ (θ (NK.GlobalCFT.Place.ofFinite 𝔭)
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) bg)))
        = ∏ 𝔭 ∈ T', χ (NK.GlobalCFT.IdeleClassGroup.mk ↥K
            (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
              (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
                (NK.GlobalCFT.Place.ofFinite 𝔭) bg))) from
      Finset.prod_congr rfl (fun 𝔭 _ => ((hbridge (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) bg))).symm).trans
          (hχFart (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
            (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) bg))))]
    rw [hbgprod]
    rfl
  -- ## 13. the heart: the `χ_{c₁}`-sum over `T'` of the `a`-terms vanishes
  have hcL : NK.LocalAnabelian.kummerField (K' := Ω) 2 c ≤
      Work.SSGRoute.EscapeCoreLib.baseChange K N hKN := by
    rw [Work.SSGRoute.EscapeCoreLib.le_baseChange_iff]
    intro x hx
    have hxN' : x ∈ (N' : Set Ω) := hFleN' (hcF hx)
    rw [hNN'] at hxN'
    exact hxN'
  have hsum := Work.SSGRoute.N2v2.heart_two_sum 2 k Ω K ζ hζ N hKN T hTfin T' hTbelow hT'above
    hTcov g hg hgc
    (fun B hB hnotT hnsplit => hgram B hB (fun A hA hconj => by
      obtain ⟨τ, hτ, hτA⟩ := hconj
      exact hnotT A hA τ hτ hτA) hnsplit)
    h hh horth₁ a ha E hexpE θ hΦElift hΦEunith hdiagLift hgE hFaE bg
    (fun σ hσ => hbg σ hσ) c (le_trans hcF hFE) hcL χE₁ hχE₁ hgsum
  -- ## 14. the product of the `a`-terms is `1`
  have hproda : (∏ 𝔭 ∈ T', χF (Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
      (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) a)))) = 1 := by
    rw [show (∏ 𝔭 ∈ T', χF (Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
          (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) a))))
        = ∏ 𝔭 ∈ T', χE₁ (θ (NK.GlobalCFT.Place.ofFinite 𝔭)
            (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
              (NK.GlobalCFT.Place.ofFinite 𝔭) a)) from
      Finset.prod_congr rfl (fun 𝔭 _ => hbridge _)]
    have hinj : Function.Injective
        (Multiplicative.toAdd : Multiplicative (ZMod 2) → ZMod 2) := fun _ _ h => h
    refine hinj ?_
    rw [Work.SSGRoute.GrunwaldEscapeCore.toAdd_prod_eq_sum 2 T'
      (fun 𝔭 => χE₁ (θ (NK.GlobalCFT.Place.ofFinite 𝔭)
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) a))), hsum]
    rfl
  -- ## 15. the reduction to the local product
  have haposF := Work.SSGRoute.ZDataTwo.hapos_arch_localNorm_aux k Ω K ζ hζ a F hapos
  have hmain : χF (Φ (NK.NUV2.RouteB.RayModulus.fracIdele
      (Work.SSGRoute.tFreePart (K := ↥K) T' a))) = 1 :=
    Work.SSGRoute.ZDataTwo.artinFixes_localFactors_two k Ω K ζ hζ F c hcF χF hχFkum a T' hFunr Φ
      (fun x => by
        rw [← MonoidHom.mem_ker, hΦker]
        exact Subgroup.mem_sup_right (NK.GlobalCFT.Idele.mem_principalSubgroup.mpr ⟨x, rfl⟩))
      (fun y => by
        rw [← MonoidHom.mem_ker, hΦker]
        exact Subgroup.mem_sup_left (NK.GlobalCFT.Idele.mem_normImage.mpr ⟨y, fun v => rfl⟩))
      haposF hproda
  rw [← hχFart (NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart (K := ↥K) T' a))]
  exact hmain

theorem orthogonality_narrow_L2K (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2)
    (N : IntermediateField k Ω) [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, Work.SSGRoute.gesKConj K A B → A = B)
    (hTcov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (B.valuation (2 : Ω) < 1 ∨
        (∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ N.fixingSubgroup)) →
      ∃ A ∈ T, Work.SSGRoute.gesKConj K A B)
    (g : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hg : ∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, g (x * y) = g x + g y)
    (hgc : SSGRoute.IsLocConstOn K.fixingSubgroup g)
    (hgram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) → ¬ SSGRoute.IsSplitIn k N B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → g σ = 0)
    (hginf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → g c = 0)
    (h : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hh : ∀ A ∈ T, ∀ x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      ∀ y ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A (x * y) = h A x + h A y)
    (hhc : ∀ A ∈ T, ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      ∀ x ∈ U, x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup → h A x = 0)
    (horth₁ : ∀ A ∈ T,
      (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A σ = 0) ∨
      (∀ χ : (Ω ≃ₐ[k] Ω) → ZMod 2,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
        (∀ σ ∈ N.fixingSubgroup, χ σ = 0) →
        ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, χ σ = 0) ∨
      ((∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → h A σ = 0) ∧
        ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod 2,
          (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
          (∀ σ ∈ N.fixingSubgroup, χ σ = 0) →
          ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → χ σ = 0))
    (hinertia : ∀ A ∈ T, ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ →
      g σ + h A σ = 0)
    (T' : Finset (NK.Chebotarev.PrimeIdeal ↥K))
    (hTbelow : ∀ A ∈ T, ∃ 𝔭 ∈ T', A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (hT'above : ∀ 𝔭 ∈ T', ∃ A ∈ T, A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (M : IntermediateField ↥K Ω) [FiniteDimensional ↥K M] [IsGalois ↥K M] [NumberField ↥M]
    (hMnorm : NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥M =
      Work.SSGRoute.H9.narrowGesU ↥K 2 T' ⊔
        Work.SSGRoute.EscapeCoreLib.pPowSubgroup 2 (NK.GlobalCFT.IdeleClassGroup ↥K))
    (N' : IntermediateField ↥K Ω) [FiniteDimensional ↥K N'] [IsGalois ↥K N'] [NumberField ↥N']
    (hNN' : (N' : Set Ω) = (N : Set Ω))
    (a : (↥K)ˣ)
    (ha : ∀ A ∈ T, ∀ σ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
      g (σ : Ω ≃ₐ[k] Ω) + h A (σ : Ω ≃ₐ[k] Ω) =
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ a
          (Work.SSGRoute.gesLocalToGalK K σ))
    (hapos : ∀ (c : Ω ≃ₐ[k] Ω) (hc : c ∈ K.fixingSubgroup), c ^ 2 = 1 →
      Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ a
        (Work.SSGRoute.gesGalKOfFixing K c hc) = 0) :
    NK.GlobalCFT.IdeleClassGroup.mk ↥K (NK.NUV2.RouteB.RayModulus.fracIdele
        (Work.SSGRoute.tFreePart (K := ↥K) T' a)) ∈
      NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥M ⊔
        NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥N' := by
  classical
  haveI hNumK : NumberField ↥K := NumberField.of_module_finite k ↥K
  rw [hMnorm]
  -- finiteness of the narrow modulus, from `hMnorm`: it *is* the norm class subgroup of the
  -- finite extension `M/↥K`
  haveI hUfin : (Work.SSGRoute.H9.narrowGesU ↥K 2 T' ⊔
      Work.SSGRoute.EscapeCoreLib.pPowSubgroup 2 (NK.GlobalCFT.IdeleClassGroup ↥K)).FiniteIndex := by
    rw [← hMnorm]
    exact Subgroup.finiteIndex_iff.mpr
      (NK.GlobalCFTdeep.normClassSubgroup_index_ne_zero (K := ↥K) (L := ↥M))
  haveI hfin : (Work.SSGRoute.H9.narrowGesU ↥K 2 T' ⊔
      Work.SSGRoute.EscapeCoreLib.pPowSubgroup 2 (NK.GlobalCFT.IdeleClassGroup ↥K) ⊔
      NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥N').FiniteIndex :=
    Subgroup.finiteIndex_of_le le_sup_left
  refine (Work.SSGRoute.charSeparation_exponent_p (p := 2)
    (Work.SSGRoute.H9.narrowGesU ↥K 2 T' ⊔
      Work.SSGRoute.EscapeCoreLib.pPowSubgroup 2 (NK.GlobalCFT.IdeleClassGroup ↥K))
    (NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥N') le_sup_right _).mpr ?_
  intro χ hχ
  exact orth_two_chi_narrow k Ω K ζ hζ N hKN T hTfin hTdisj hTcov g hg hgc hgram hginf h hh hhc
    horth₁ hinertia T' hTbelow hT'above N' hNN' a ha hapos χ
    (fun u hu => hχ u (Subgroup.mem_sup_left hu)) (fun u hu => hχ u (Subgroup.mem_sup_right hu))

end Work.H9Narrow
