import Mathlib.AlgebraicGeometry.QuasiAffine
import Submission.Commons.AlgebraicGeometry.IrreducibleComponent.irreducibleComponent_iso_of_iso
import Submission.Commons.RingTheory.Localization.quotient_iso_atPrime
import Submission.Commons.RingTheory.Localization.away_atPrime_dictionary

open AlgebraicGeometry PrimeSpectrum CategoryTheory

namespace Commons.AlgebraicGeometry.Affine

lemma le_ker_algebraMap_atPrime {S : Type} [CommRing S] (𝔮 : Ideal S) (hmax : 𝔮.IsMaximal)
    (hfield : IsField (Localization.AtPrime 𝔮)) :
    𝔮 ≤ RingHom.ker (algebraMap S (Localization.AtPrime 𝔮)) := by
  haveI : 𝔮.IsPrime := hmax.isPrime
  haveI : IsLocalRing (Localization.AtPrime 𝔮) := inferInstance
  have hmap : Ideal.map (algebraMap S (Localization.AtPrime 𝔮)) 𝔮 =
      IsLocalRing.maximalIdeal (Localization.AtPrime 𝔮) :=
    IsLocalization.AtPrime.map_eq_maximalIdeal 𝔮 _
  have hbot : IsLocalRing.maximalIdeal (Localization.AtPrime 𝔮) = ⊥ := by
    letI : Field (Localization.AtPrime 𝔮) := hfield.toField
    exact IsLocalRing.maximalIdeal_eq_bot
  intro b hb
  have : algebraMap S (Localization.AtPrime 𝔮) b ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime 𝔮) := by
    rw [← hmap]; exact Ideal.mem_map_of_mem _ hb
  rw [hbot] at this
  simpa using this

lemma ker_algebraMap_away_of_isolated {S T : Type} [CommRing S] [CommRing T] [Algebra S T]
    (h : S) [IsLocalization.Away h T]
    (𝔮 : Ideal S) (hmax : 𝔮.IsMaximal)
    (hfield : IsField (Localization.AtPrime 𝔮))
    (hD : (PrimeSpectrum.basicOpen h : Set (PrimeSpectrum S)) = {⟨𝔮, hmax.isPrime⟩}) :
    RingHom.ker (algebraMap S T) = 𝔮 := by
  haveI : 𝔮.IsPrime := hmax.isPrime
  have hnotmem : h ∉ 𝔮 := by
    intro hh
    have h1 : (⟨𝔮, hmax.isPrime⟩ : PrimeSpectrum S) ∉
        (PrimeSpectrum.basicOpen h : Set (PrimeSpectrum S)) := by
      intro hcon
      exact ((PrimeSpectrum.mem_basicOpen h (⟨𝔮, hmax.isPrime⟩ : PrimeSpectrum S)).mp hcon) hh
    rw [hD] at h1
    exact h1 (Set.mem_singleton _)
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker] at hx
    obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers h) T x).mp hx
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (m : S) h).mp m.2
    have hm' : h ^ n * x = 0 := by rw [hn]; exact hm
    exact (hmax.isPrime.mem_or_mem_of_mul_eq_zero hm').resolve_left
      (fun hcon => hnotmem (hmax.isPrime.mem_of_pow_mem n hcon))
  · intro x hx
    rw [RingHom.mem_ker]
    have hk := le_ker_algebraMap_atPrime 𝔮 hmax hfield hx
    rw [RingHom.mem_ker] at hk
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff (𝔮.primeCompl) _ x).mp hk
    have hsnot : (s : S) ∉ 𝔮 := s.2
    have hsub : PrimeSpectrum.basicOpen h ≤ PrimeSpectrum.basicOpen (s : S) := by
      rw [← SetLike.coe_subset_coe, hD]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact (PrimeSpectrum.mem_basicOpen (s : S) (⟨𝔮, hmax.isPrime⟩ : PrimeSpectrum S)).mpr hsnot
    have hrad : h ∈ (Ideal.span {(s : S)}).radical :=
      (PrimeSpectrum.basicOpen_le_basicOpen_iff h (s : S)).mp hsub
    obtain ⟨n, hn⟩ := (Ideal.mem_radical_iff).mp hrad
    obtain ⟨c, hc⟩ := (Ideal.mem_span_singleton).mp hn
    have hxn : h ^ n * x = 0 := by
      rw [hc]
      calc (↑s * c) * x = c * (↑s * x) := by ring
        _ = 0 := by rw [hs, mul_zero]
    exact (IsLocalization.map_eq_zero_iff (Submonoid.powers h) T x).mpr
      ⟨⟨h ^ n, (Submonoid.mem_powers_iff (h ^ n) h).mpr ⟨n, rfl⟩⟩, hxn⟩

lemma Ueq {B : Type} [CommRing B] (𝔭 : Ideal B) (hmax : 𝔭.IsMaximal) [IsNoetherianRing B]
    (hZ : PrimeSpectrum.zeroLocus (𝔭 : Set B) ∈ irreducibleComponents (Spec (CommRingCat.of B))) :
    ((Spec (CommRingCat.of B)).irreducibleComponentOpen
      (PrimeSpectrum.zeroLocus (𝔭 : Set B)) : Set (Spec (CommRingCat.of B)))
      = PrimeSpectrum.zeroLocus (𝔭 : Set B) := by
  haveI : IsNoetherian (Spec (CommRingCat.of B)) := isNoetherian_Spec.mpr inferInstance
  have hZ' : PrimeSpectrum.zeroLocus (𝔭 : Set B) ∈ irreducibleComponents (PrimeSpectrum B) := hZ
  change ((⋃₀ (irreducibleComponents (PrimeSpectrum B) \
    {PrimeSpectrum.zeroLocus (𝔭 : Set B)}))ᶜ) = PrimeSpectrum.zeroLocus (𝔭 : Set B)
  have hZsing : PrimeSpectrum.zeroLocus (𝔭 : Set B) = {⟨𝔭, hmax.isPrime⟩} :=
    zeroLocus_eq_singleton 𝔭
  have hZmax : Maximal (fun s : Set (PrimeSpectrum B) => IsClosed s ∧ IsIrreducible s)
      (PrimeSpectrum.zeroLocus (𝔭 : Set B)) := by
    have := hZ'
    simpa only [irreducibleComponents_eq_maximals_closed, Set.mem_setOf_eq] using this
  have hcl : closure ((⋃₀ (irreducibleComponents (PrimeSpectrum B) \
      {PrimeSpectrum.zeroLocus (𝔭 : Set B)}))ᶜ) = PrimeSpectrum.zeroLocus (𝔭 : Set B) :=
    closure_sUnion_irreducibleComponents_sdiff_singleton
      TopologicalSpace.NoetherianSpace.finite_irreducibleComponents _ hZ'
  apply Set.Subset.antisymm
  · intro x hx
    exact hcl ▸ subset_closure hx
  · intro x hx
    rw [Set.mem_compl_iff, Set.mem_sUnion]
    rintro ⟨W, hWS, hxW⟩
    rw [hZsing, Set.mem_singleton_iff] at hx
    rw [hx] at hxW
    have hZsubW : PrimeSpectrum.zeroLocus (𝔭 : Set B) ⊆ W := by
      rw [hZsing, Set.singleton_subset_iff]; exact hxW
    have hWclirr : IsClosed W ∧ IsIrreducible W := by
      have h := hWS.1
      have h2 : Maximal (fun s : Set (PrimeSpectrum B) => IsClosed s ∧ IsIrreducible s) W := by
        simpa only [irreducibleComponents_eq_maximals_closed, Set.mem_setOf_eq] using h
      exact h2.1
    exact hWS.2 (Set.mem_singleton_iff.mpr
      (Set.Subset.antisymm (hZmax.2 hWclirr hZsubW) hZsubW))

lemma ker_app_eq {X : Scheme} (U : X.Opens) :
    RingHom.ker ((U.ι).app ⊤).hom =
      RingHom.ker ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom) := by
  have h : U.ι ''ᵁ U.ι ⁻¹ᵁ ⊤ = U := by rw [Scheme.Hom.preimage_top, Scheme.Opens.ι_image_top]
  rw [Scheme.Opens.ι_app]
  change RingHom.ker (CommRingCat.Hom.hom (X.presheaf.map (homOfLE
      (x := U.ι ''ᵁ U.ι ⁻¹ᵁ ⊤) (Set.image_preimage_subset (U.ι) ⊤)).op)) =
    RingHom.ker (CommRingCat.Hom.hom (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op))
  have h₁ : X.presheaf.map (homOfLE (x := U.ι ''ᵁ U.ι ⁻¹ᵁ ⊤)
      (Set.image_preimage_subset (U.ι) ⊤)).op =
      X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ X.presheaf.map (eqToHom h).op := by
    rw [← Functor.map_comp, ← op_comp]
    exact congrArg _ (Subsingleton.elim _ _)
  rw [h₁, CommRingCat.hom_comp, RingHom.ker_comp_of_injective _ (by
    intro a b hab
    exact (ConcreteCategory.bijective_of_isIso (X.presheaf.map (eqToHom h).op)).1 hab)]

noncomputable def subschemeIsoSpecQuotient {X : Scheme} [IsAffine X] (I : X.IdealSheafData) :
    I.subscheme ≅ Spec (CommRingCat.of (Γ(X, ⊤) ⧸ I.ideal ⟨⊤, isAffineOpen_top X⟩)) := by
  haveI : IsAffine I.subscheme := (IsClosedImmersion.isAffine_surjective_of_isAffine I.subschemeι).1
  have hpre : I.subschemeι ⁻¹ᵁ (⊤ : X.Opens) = ⊤ := Scheme.Hom.preimage_top _
  let e : Γ(I.subscheme, ⊤) ≅ CommRingCat.of (Γ(X, ⊤) ⧸ I.ideal ⟨⊤, isAffineOpen_top X⟩) :=
    (I.subscheme.presheaf.mapIso (eqToIso hpre).op).symm ≪≫
      I.subschemeObjIso ⟨⊤, isAffineOpen_top X⟩
  exact (Scheme.isoSpec I.subscheme).trans (Iso.symm (Iso.mk (Spec.map e.hom) (Spec.map e.inv)
    (by rw [← Spec.map_comp (f := e.inv) (g := e.hom), Iso.inv_hom_id, Spec.map_id])
    (by rw [← Spec.map_comp (f := e.hom) (g := e.inv), Iso.hom_inv_id, Spec.map_id])))

lemma exists_basicOpen {B : Type} [CommRing B] (𝔭 : Ideal B) (hmax : 𝔭.IsMaximal) [IsNoetherianRing B]
    (hZ : PrimeSpectrum.zeroLocus (𝔭 : Set B) ∈ irreducibleComponents (Spec (CommRingCat.of B))) :
    ∃ b : B, PrimeSpectrum.basicOpen b =
      (Spec (CommRingCat.of B)).irreducibleComponentOpen (PrimeSpectrum.zeroLocus (𝔭 : Set B)) := by
  haveI : IsNoetherian (Spec (CommRingCat.of B)) := isNoetherian_Spec.mpr inferInstance
  haveI : IsAffine (Spec (CommRingCat.of B)) := inferInstance
  have hUeq := Ueq 𝔭 hmax hZ
  have hZsing : PrimeSpectrum.zeroLocus (𝔭 : Set B) = {⟨𝔭, hmax.isPrime⟩} := zeroLocus_eq_singleton 𝔭
  have hmem : (⟨𝔭, hmax.isPrime⟩ : ↥(Spec (CommRingCat.of B))) ∈
      (Spec (CommRingCat.of B)).irreducibleComponentOpen (PrimeSpectrum.zeroLocus (𝔭 : Set B)) := by
    have h : (⟨𝔭, hmax.isPrime⟩ : ↥(Spec (CommRingCat.of B))) ∈
        (((Spec (CommRingCat.of B)).irreducibleComponentOpen
          (PrimeSpectrum.zeroLocus (𝔭 : Set B))) : Set (Spec (CommRingCat.of B))) := by
      rw [hUeq, hZsing]
      exact Set.mem_singleton _
    exact h
  obtain ⟨V, hVmem, hxV, hVU⟩ := (isBasis_basicOpen (Spec (CommRingCat.of B))).exists_subset_of_mem_open
    hmem ((Spec (CommRingCat.of B)).irreducibleComponentOpen
      (PrimeSpectrum.zeroLocus (𝔭 : Set B))).isOpen
  rw [Set.mem_image] at hVmem
  obtain ⟨V', hV'mem, hV'eq⟩ := hVmem
  rw [Set.mem_range] at hV'mem
  obtain ⟨h, hh⟩ := hV'mem
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of B)).hom h, ?_⟩
  rw [← basicOpen_eq_of_affine']
  rw [hh]
  apply le_antisymm
  · intro y hy
    exact hVU (hV'eq ▸ hy)
  · intro y hy
    have hy1 : y ∈ PrimeSpectrum.zeroLocus (𝔭 : Set B) := hUeq ▸ hy
    rw [hZsing, Set.mem_singleton_iff] at hy1
    rw [hy1]
    convert hxV using 1
    exact (Set.ext_iff.mp hV'eq _)





noncomputable def specRingEquiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Spec (CommRingCat.of R) ≅ Spec (CommRingCat.of S) :=
  (Scheme.Spec.mapIso e.toCommRingCatIso.op).symm

theorem core_affine_irreducibleComponent_iso_spec_quotient {B : Type} [CommRing B] [IsNoetherianRing B] (𝔭 : Ideal B) (hmax : 𝔭.IsMaximal)
    (hfield : IsField (Localization.AtPrime 𝔭)) :
    ∃ Z, ∃ hZ : Z ∈ irreducibleComponents (Spec (CommRingCat.of B)),
      Nonempty ((Spec (CommRingCat.of B)).irreducibleComponent Z hZ ≅
        Spec (CommRingCat.of (B ⧸ 𝔭))) := by
  haveI : 𝔭.IsPrime := hmax.isPrime
  haveI hNoeth : IsNoetherian (Spec (CommRingCat.of B)) := isNoetherian_Spec.mpr inferInstance
  haveI hAff : IsAffine (Spec (CommRingCat.of B)) := inferInstance
  have hmin : 𝔭 ∈ minimalPrimes B := by
    show IsMinimalPrime 𝔭
    rw [IsMinimalPrime.iff_minimal]
    refine ⟨hmax.isPrime, ?_⟩
    intro q hq hqle x hx
    have hk := le_ker_algebraMap_atPrime 𝔭 hmax hfield hx
    rw [RingHom.mem_ker] at hk
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff (𝔭.primeCompl) _ x).mp hk
    exact (hq.mem_or_mem_of_mul_eq_zero hs).resolve_left (fun hcon => s.2 (hqle hcon))
  have hZ : PrimeSpectrum.zeroLocus (𝔭 : Set B) ∈ irreducibleComponents (Spec (CommRingCat.of B)) := by
    change PrimeSpectrum.zeroLocus (𝔭 : Set B) ∈ irreducibleComponents (PrimeSpectrum B)
    rw [show (𝔭 : Set B) = ↑𝔭 from rfl]
    rw [PrimeSpectrum.zeroLocus_ideal_mem_irreducibleComponents]
    rwa [hmax.isPrime.radical]
  refine ⟨PrimeSpectrum.zeroLocus (𝔭 : Set B), hZ, ?_⟩
  let φ : Γ(Spec (CommRingCat.of B), ⊤) ≃+* B :=
    (Scheme.ΓSpecIso (CommRingCat.of B)).commRingCatIsoToRingEquiv
  let 𝔭S : Ideal Γ(Spec (CommRingCat.of B), ⊤) := Ideal.comap φ.toRingHom 𝔭
  obtain ⟨b, hb⟩ := exists_basicOpen 𝔭 hmax hZ
  have hbD : (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum B)) = {⟨𝔭, hmax.isPrime⟩} := by
    have h2 := congrArg (fun V : (Spec (CommRingCat.of B)).Opens =>
      (V : Set (Spec (CommRingCat.of B)))) hb
    rw [show (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum B)) =
        (((Spec (CommRingCat.of B)).irreducibleComponentOpen
          (PrimeSpectrum.zeroLocus (𝔭 : Set B))) : Set (Spec (CommRingCat.of B))) from h2]
    rw [Ueq 𝔭 hmax hZ]
    exact zeroLocus_eq_singleton 𝔭
  have hkerB : RingHom.ker (algebraMap B (Localization.Away b)) = 𝔭 :=
    ker_algebraMap_away_of_isolated b 𝔭 hmax hfield hbD
  have hU : (Spec (CommRingCat.of B)).irreducibleComponentOpen (PrimeSpectrum.zeroLocus (𝔭 : Set B))
      = (Spec (CommRingCat.of B)).basicOpen (φ.symm b) := by
    rw [← hb, basicOpen_eq_of_affine']
    congr 1
    exact (φ.apply_symm_apply b).symm
  have hker : ((Spec (CommRingCat.of B)).irreducibleComponentIdeal
      (PrimeSpectrum.zeroLocus (𝔭 : Set B)) hZ).ideal
      ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of B))⟩ = 𝔭S := by
    have h1 : ((Spec (CommRingCat.of B)).irreducibleComponentIdeal
        (PrimeSpectrum.zeroLocus (𝔭 : Set B)) hZ).ideal
        ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of B))⟩ =
        RingHom.ker (((Spec (CommRingCat.of B)).irreducibleComponentOpen
          (PrimeSpectrum.zeroLocus (𝔭 : Set B))).ι.app ⊤).hom := by
      change (Scheme.Hom.ker ((Spec (CommRingCat.of B)).irreducibleComponentOpen
          (PrimeSpectrum.zeroLocus (𝔭 : Set B))).ι).ideal
          ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of B))⟩ = _
      rw [Scheme.Hom.ker_apply]
    rw [h1, ker_app_eq, hU]
    change RingHom.ker (algebraMap Γ(Spec (CommRingCat.of B), ⊤)
      Γ(Spec (CommRingCat.of B), (Spec (CommRingCat.of B)).basicOpen (φ.symm b))) = 𝔭S
    haveI : IsLocalization.Away (φ.symm b)
        Γ(Spec (CommRingCat.of B), (Spec (CommRingCat.of B)).basicOpen (φ.symm b)) := inferInstance
    apply le_antisymm
    · intro x hx
      rw [RingHom.mem_ker] at hx
      obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (φ.symm b)) _ x).mp hx
      obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (m : Γ(Spec (CommRingCat.of B), ⊤)) (φ.symm b)).mp m.2
      have hm' : (φ.symm b) ^ n * x = 0 := by rw [hn]; exact hm
      have hbx : b ^ n * φ x = 0 := by
        have := congrArg φ hm'
        simp only [map_mul, map_pow, map_zero, RingEquiv.apply_symm_apply] at this
        exact this
      have hmem : φ.toRingHom x ∈ RingHom.ker (algebraMap B (Localization.Away b)) := by
        rw [RingHom.mem_ker]
        exact (IsLocalization.map_eq_zero_iff (Submonoid.powers b) _ (φ x)).mpr
          ⟨⟨b ^ n, (Submonoid.mem_powers_iff (b ^ n) b).mpr ⟨n, rfl⟩⟩, hbx⟩
      rw [hkerB] at hmem
      exact hmem
    · intro x hx
      have hx' : φ.toRingHom x ∈ 𝔭 := hx
      rw [← hkerB, RingHom.mem_ker] at hx'
      obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers b) _ (φ x)).mp hx'
      obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (m : B) b).mp m.2
      have hm' : b ^ n * φ x = 0 := by rw [hn]; exact hm
      rw [RingHom.mem_ker]
      exact (IsLocalization.map_eq_zero_iff (Submonoid.powers (φ.symm b)) _ x).mpr
        ⟨⟨(φ.symm b) ^ n, (Submonoid.mem_powers_iff ((φ.symm b) ^ n) (φ.symm b)).mpr ⟨n, rfl⟩⟩,
          φ.injective (by
            simp only [map_mul, map_pow, map_zero, RingEquiv.apply_symm_apply]
            exact hm')⟩
  have hI : (Spec (CommRingCat.of B)).irreducibleComponentIdeal
      (PrimeSpectrum.zeroLocus (𝔭 : Set B)) hZ = Scheme.IdealSheafData.ofIdealTop 𝔭S := by
    apply Scheme.IdealSheafData.ext_of_isAffine
    rw [hker]
    rw [Scheme.IdealSheafData.ofIdealTop_ideal]
    simp
  refine ⟨?_⟩
  change ((Spec (CommRingCat.of B)).irreducibleComponentIdeal
      (PrimeSpectrum.zeroLocus (𝔭 : Set B)) hZ).subscheme ≅ Spec (CommRingCat.of (B ⧸ 𝔭))
  rw [hI]
  have hIid : (Scheme.IdealSheafData.ofIdealTop 𝔭S).ideal
      ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of B))⟩ = 𝔭S := by
    rw [Scheme.IdealSheafData.ofIdealTop_ideal]
    simp
  have hiso1 : (Scheme.IdealSheafData.ofIdealTop 𝔭S).subscheme
      ≅ Spec (CommRingCat.of (Γ(Spec (CommRingCat.of B), ⊤) ⧸
          (Scheme.IdealSheafData.ofIdealTop 𝔭S).ideal
            ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of B))⟩)) :=
    subschemeIsoSpecQuotient (Scheme.IdealSheafData.ofIdealTop 𝔭S)
  rw [hIid] at hiso1
  exact hiso1.trans (specRingEquiv
    (Ideal.quotientEquiv 𝔭S 𝔭 φ (Ideal.map_comap_of_surjective φ.toRingHom φ.surjective 𝔭).symm))



/-- The target theorem. -/
theorem irreducibleComponent_iso_spec_of_localization
    {A K : Type} [CommRing A] [Field K] (𝔭 : Ideal A) (hmax : 𝔭.IsMaximal)
    (f : A) (hf : f ∉ 𝔭) (hiso : Nonempty (@Localization.AtPrime _ _ 𝔭 hmax.isPrime ≃+* K))
    [AlgebraicGeometry.IsNoetherian ((AlgebraicGeometry.Spec (.of A)).basicOpen
      ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv f) :
        AlgebraicGeometry.Scheme)] :
    ∃ Z, ∃ hZ : Z ∈ irreducibleComponents ((AlgebraicGeometry.Spec (.of A)).basicOpen
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv f) :
          AlgebraicGeometry.Scheme),
      Nonempty (((AlgebraicGeometry.Spec (.of A)).basicOpen
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv f) :
          AlgebraicGeometry.Scheme).irreducibleComponent Z hZ
          ≅ AlgebraicGeometry.Spec (.of K)) := by
  set g : Γ(Spec (CommRingCat.of A), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv f with hgdef
  set X : Scheme := ((Spec (.of A)).basicOpen g : Scheme) with hXdef
  have hbg : ((Spec (.of A)).basicOpen g : (Spec (.of A)).Opens) =
      (PrimeSpectrum.basicOpen f : (Spec (.of A)).Opens) := by
    rw [basicOpen_eq_of_affine']
    congr 1
    rw [hgdef]
    exact Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of A)) f
  have hXeq : X = (Scheme.Opens.toScheme (X := Spec (CommRingCat.of A))
      (PrimeSpectrum.basicOpen f) : Scheme) := by
    rw [hXdef]
    exact congrArg (fun U : (Spec (.of A)).Opens => (Scheme.Opens.toScheme U : Scheme)) hbg
  haveI : IsNoetherian X := ‹_›
  let B := Localization.Away f
  have eXY : X ≅ Spec (CommRingCat.of B) :=
    (eqToIso hXeq) ≪≫ basicOpenIsoSpecAway (R := CommRingCat.of A) f
  haveI hNY : IsNoetherian (Spec (CommRingCat.of B)) := by
    haveI : IsOpenImmersion eXY.inv := inferInstance
    haveI : IsLocallyNoetherian (Spec (CommRingCat.of B)) :=
      isLocallyNoetherian_of_isOpenImmersion eXY.inv
    haveI : CompactSpace (Spec (CommRingCat.of B)) :=
      (Scheme.homeoOfIso eXY).compactSpace
    exact ⟨⟩
  haveI : IsNoetherianRing B := isNoetherian_Spec.mp hNY
  obtain ⟨𝔭', h𝔭', hmax', hfield', hiso'⟩ :=
    Commons.RingTheory.Localization.away_atPrime_dictionary 𝔭 hmax f hf hiso
  obtain ⟨Z', hZ', eCore⟩ := core_affine_irreducibleComponent_iso_spec_quotient (B := B) 𝔭' hmax' hfield'
  obtain ⟨eK⟩ := hiso'
  have eQ : (Spec (CommRingCat.of B)).irreducibleComponent Z' hZ' ≅ Spec (.of K) :=
    eCore.some.trans (specRingEquiv eK)
  obtain ⟨Z, hZ, ⟨eZ⟩⟩ :=
    Commons.AlgebraicGeometry.IrreducibleComponent.irreducibleComponent_iso_of_iso eXY.symm Z' hZ'
  exact ⟨Z, hZ, ⟨eZ.symm.trans eQ⟩⟩

end Commons.AlgebraicGeometry.Affine