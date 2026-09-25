import Mathlib
import Submission.NK.NUV2.LC.RouteB.Defs
import Submission.NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension
import Submission.NK.TameStructureDeep.TameDeep.inertiaDeg_dvd_of_isPrimitiveRoot
import Submission.NK.NUV2.LC.RouteB.extendScalars_sup_adjoin

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace NK.NUV2.LC.RouteB

open NumberField IsDedekindDomain

/-- **The cyclotomic enlargement of a level.**  Let `F` be a number field with separable closure
`K'`, `L` a finite Galois level, `𝔭` a finite prime of `F` *unramified* in `L`, and `A` a place of
`K'` over `𝔭`.  Then there is a larger level `L' ⊇ L`, still unramified over `𝔭`, and primes
`𝔮` of `L`, `𝔴` of `L'` cut out by `A`, such that `p · f(𝔮|𝔭) ∣ f(𝔴|𝔭)`.

Construction: with `m := (Ideal.absNorm 𝔮.asIdeal) ^ p - 1`, take `L' := L ⊔ (adjoin F {ζ})` where
`ζ ∈ K'` is a primitive `m`-th root of unity; then `L' = L(ζ_m)`, the extension is cyclotomic
(hence unramified at `𝔭`, because `m ∉ 𝔮'` for every prime `𝔮'` of `L` over `𝔭`), and
`p · f(𝔮|𝔭) ∣ f(𝔴|𝔭)` follows from the tower formula `f(𝔴|𝔭) = f(𝔴|𝔮) · f(𝔮|𝔭)` together with
`p ∣ f(𝔴|𝔮)`; the latter is `NK.TameStructureDeep.TameDeep.inertiaDeg_dvd_of_isPrimitiveRoot`
applied over the base `L` (the image of `ζ` in `𝔴.adicCompletion L'` is a primitive
`(N𝔮) ^ p - 1`-st root of unity, and `N𝔮 = #κ(𝔮)`). -/
theorem exists_cyclotomic_level_dvd_inertiaDeg (p : ℕ) (hp : p.Prime) {F K' : Type} [Field F]
    [NumberField F] [Field K'] [Algebra F K'] [IsSepClosure F K']
    (L : FiniteGaloisIntermediateField F K') (A : NK.BrauerHasse.OverFinitePrime F K')
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (hA : A.1.comap (algebraMap F K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F 𝔭)
    (hunr : NK.HeckeL.IsUnramifiedIn (K := F) (L := ↥(L : IntermediateField F K')) 𝔭) :
    ∃ (L' : FiniteGaloisIntermediateField F K'), L ≤ L' ∧
      NK.HeckeL.IsUnramifiedIn (K := F) (L := ↥(L' : IntermediateField F K')) 𝔭 ∧
      ∃ (𝔮 : IsDedekindDomain.HeightOneSpectrum
            (NumberField.RingOfIntegers ↥(L : IntermediateField F K')))
        (𝔴 : IsDedekindDomain.HeightOneSpectrum
            (NumberField.RingOfIntegers ↥(L' : IntermediateField F K'))),
        A.1.comap (algebraMap ↥(L : IntermediateField F K') K') =
            IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
              ↥(L : IntermediateField F K') 𝔮 ∧
          A.1.comap (algebraMap ↥(L' : IntermediateField F K') K') =
            IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
              ↥(L' : IntermediateField F K') 𝔴 ∧
          p * 𝔮.asIdeal.inertiaDeg (NumberField.RingOfIntegers F) ∣
            𝔴.asIdeal.inertiaDeg (NumberField.RingOfIntegers F) := by
  classical
  -- ## 0. The base level `L` and the prime `𝔮` cut out by the place `A`
  let LL : IntermediateField F K' := (L : IntermediateField F K')
  haveI hfinLL : FiniteDimensional F ↥LL := L.finiteDimensional
  let 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥LL) :=
    Submission.NeukirchUchida.Local.placeOf 𝔭 A.1 hA LL
  have h𝔮 : A.1.comap (algebraMap ↥LL K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥LL 𝔮 :=
    Submission.NeukirchUchida.Local.comap_eq_valuationSubringAtPrime_placeOf 𝔭 A.1 hA LL
  -- ## 1. The level `m = (N𝔮) ^ p - 1` and a primitive `m`-th root of unity in `K'`
  set N : ℕ := Ideal.absNorm 𝔮.asIdeal with hN
  set m : ℕ := N ^ p - 1 with hm
  haveI hczF : CharZero F := NumberField.to_charZero
  haveI hczK' : CharZero K' :=
    charZero_of_injective_algebraMap (RingHom.injective (algebraMap F K'))
  have hN2 : 2 ≤ N := by
    have h0 : N ≠ 0 := by
      rw [hN, Ideal.absNorm_ne_zero_iff]
      exact Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum 𝔮
    have h1 : N ≠ 1 := by
      rw [hN]
      intro h
      exact (inferInstance : 𝔮.asIdeal.IsPrime).ne_top (Ideal.absNorm_eq_one_iff.mp h)
    omega
  have hm0 : 0 < m := by
    have hp2 : 2 ≤ p := hp.two_le
    have h4 : 4 ≤ N ^ p := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp2
        _ ≤ N ^ p := Nat.pow_le_pow_left hN2 p
    rw [hm]
    omega
  haveI hNez : NeZero m := ⟨hm0.ne'⟩
  haveI hNezK' : NeZero (m : K') := ⟨by
    rw [Nat.cast_ne_zero]
    exact hm0.ne'⟩
  haveI hsc : IsSepClosed K' := IsSepClosure.sep_closed (k := F) (K := K')
  haveI hsepFK' : Algebra.IsSeparable F K' := IsSepClosure.separable
  haveI hintFK' : Algebra.IsIntegral F K' := ⟨fun x => Algebra.IsSeparable.isIntegral F x⟩
  have hdeg : (Polynomial.cyclotomic m K').degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.mpr hm0).ne'
  obtain ⟨ζ, hζroot⟩ := IsSepClosed.exists_root (Polynomial.cyclotomic m K') hdeg
    (Polynomial.separable_cyclotomic m K')
  have hζ : IsPrimitiveRoot ζ m := (Polynomial.isRoot_cyclotomic_iff).mp hζroot
  -- ## 2. The cyclotomic field `M = F(ζ)` and the level `L' = L ⊔ M`
  let M : IntermediateField F K' := IntermediateField.adjoin F ({ζ} : Set K')
  haveI hcycM : IsCyclotomicExtension ({m} : Set ℕ) F M :=
    hζ.intermediateField_adjoin_isCyclotomicExtension F
  haveI hfinM : FiniteDimensional F M := IsCyclotomicExtension.finiteDimensional {m} F M
  haveI hgalM : IsGalois F M := IsCyclotomicExtension.isGalois {m} F M
  let Mfg : FiniteGaloisIntermediateField F K' := { toIntermediateField := M }
  let L' : FiniteGaloisIntermediateField F K' := L ⊔ Mfg
  -- the `↥L`-view of `L'`, which is the compositum `L ⊔ M`
  let L'int : IntermediateField ↥LL K' :=
    IntermediateField.extendScalars (F := LL) (E := LL ⊔ M) le_sup_left
  have hGen : L'int = IntermediateField.adjoin ↥LL ({ζ} : Set K') :=
    extendScalars_sup_adjoin LL ({ζ} : Set K')
  haveI hcycL'int : IsCyclotomicExtension ({m} : Set ℕ) ↥LL ↥L'int :=
    (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin m ↥LL K' L'int hζ).mpr hGen
  haveI hfinL'int : FiniteDimensional ↥LL ↥L'int :=
    IsCyclotomicExtension.finiteDimensional {m} ↥LL ↥L'int
  haveI hnfLL : NumberField ↥LL :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField LL
  haveI hnfL' : NumberField ↥(L' : IntermediateField F K') :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (L' : IntermediateField F K')
  haveI hnfL'int : NumberField ↥L'int := hnfL'
  have h𝔮lies : 𝔮.asIdeal.LiesOver 𝔭.asIdeal :=
    Submission.NeukirchUchida.Local.placeOf_liesOver 𝔭 A.1 hA LL
  have hNpow : N = Ideal.absNorm 𝔭.asIdeal ^ 𝔮.asIdeal.inertiaDeg (NumberField.RingOfIntegers F) := by
    rw [hN]
    exact Commons.NumberTheory.NumberField.absNorm_eq_pow_inertiaDeg_of_liesOver 𝔭 𝔮 h𝔮lies
  -- ## 3. `L'` is unramified over `𝔭`
  have hunrL'int : NK.HeckeL.IsUnramifiedIn (K := F) (L := ↥L'int) 𝔭 := by
    intro 𝔓 h𝔓
    -- the prime of `L` below `𝔓`
    let 𝔮' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥LL) :=
      ⟨𝔓.asIdeal.under (NumberField.RingOfIntegers ↥LL), inferInstance,
        Ideal.under_ne_bot (NumberField.RingOfIntegers ↥LL) 𝔓.ne_bot⟩
    have h𝔓𝔮' : 𝔓.asIdeal.LiesOver 𝔮'.asIdeal := ⟨rfl⟩
    haveI : 𝔓.asIdeal.LiesOver 𝔭.asIdeal := h𝔓
    haveI : 𝔓.asIdeal.LiesOver 𝔮'.asIdeal := h𝔓𝔮'
    have h𝔮'𝔭 : 𝔮'.asIdeal.LiesOver 𝔭.asIdeal :=
      Ideal.LiesOver.tower_bot 𝔓.asIdeal 𝔮'.asIdeal 𝔭.asIdeal
    haveI : 𝔮'.asIdeal.LiesOver 𝔭.asIdeal := h𝔮'𝔭
    -- `N𝔮` is a power of the rational prime below `𝔭`, so it lies in every prime above `𝔭`
    have hmem_p : (Ideal.absNorm 𝔭.asIdeal : NumberField.RingOfIntegers ↥LL) ∈ 𝔮'.asIdeal := by
      have hcomap : Ideal.comap (algebraMap (NumberField.RingOfIntegers F)
          (NumberField.RingOfIntegers ↥LL)) 𝔮'.asIdeal = 𝔭.asIdeal := by
        rw [← Ideal.under_def]
        exact (Ideal.over_def 𝔮'.asIdeal 𝔭.asIdeal).symm
      have h : algebraMap (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers ↥LL)
          (Ideal.absNorm 𝔭.asIdeal : NumberField.RingOfIntegers F) ∈ 𝔮'.asIdeal := by
        rw [← Ideal.mem_comap, hcomap]
        exact Ideal.absNorm_mem 𝔭.asIdeal
      simpa using h
    have hNmem : (N : NumberField.RingOfIntegers ↥LL) ∈ 𝔮'.asIdeal := by
      rw [hNpow, Nat.cast_pow]
      exact Ideal.pow_mem_of_mem _ hmem_p _
        (Ideal.inertiaDeg_pos 𝔮.asIdeal (NumberField.RingOfIntegers F))
    have hcop : (m : NumberField.RingOfIntegers ↥LL) ∉ 𝔮'.asIdeal := by
      intro hmem
      have h1le : 1 ≤ N ^ p := Nat.one_le_pow p N (by omega)
      have hpN : (N : NumberField.RingOfIntegers ↥LL) ^ p ∈ 𝔮'.asIdeal :=
        Ideal.pow_mem_of_mem _ hNmem p hp.pos
      have hmN : (m : NumberField.RingOfIntegers ↥LL) =
          (N : NumberField.RingOfIntegers ↥LL) ^ p - 1 := by
        rw [hm, Nat.cast_sub h1le, Nat.cast_pow, Nat.cast_one]
      rw [hmN] at hmem
      have hone : (1 : NumberField.RingOfIntegers ↥LL) ∈ 𝔮'.asIdeal := by
        have hsub := sub_mem hpN hmem
        simpa using hsub
      exact (inferInstance : 𝔮'.asIdeal.IsPrime).ne_top ((Ideal.eq_top_iff_one _).mpr hone)
    have hunr𝔮' : NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := ↥LL)
        (L := ↥L'int) 𝔮' :=
      NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension (k := ↥LL) (Ω := ↥L'int) m 𝔮' hcop
    have he1 : 𝔓.asIdeal.ramificationIdx (NumberField.RingOfIntegers ↥LL) = 1 :=
      hunr𝔮' 𝔓 h𝔓𝔮'
    have he2 : 𝔮'.asIdeal.ramificationIdx (NumberField.RingOfIntegers F) = 1 :=
      hunr 𝔮' h𝔮'𝔭
    have htower := Ideal.ramificationIdx_tower (R := NumberField.RingOfIntegers F)
      (S := NumberField.RingOfIntegers ↥LL)
      (T := NumberField.RingOfIntegers ↥L'int) 𝔮'.asIdeal 𝔓.asIdeal
    simp [htower, he1, he2]
  have hunrL' : NK.HeckeL.IsUnramifiedIn (K := F)
      (L := ↥(L' : IntermediateField F K')) 𝔭 := hunrL'int
  -- ## 4. The prime of `L'` cut out by `A`, and the divisibility of the inertia degree
  let 𝔴 : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers ↥(L' : IntermediateField F K')) :=
    Submission.NeukirchUchida.Local.placeOf 𝔭 A.1 hA (L' : IntermediateField F K')
  have h𝔴 : A.1.comap (algebraMap ↥(L' : IntermediateField F K') K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
        ↥(L' : IntermediateField F K') 𝔴 :=
    Submission.NeukirchUchida.Local.comap_eq_valuationSubringAtPrime_placeOf 𝔭 A.1 hA
      (L' : IntermediateField F K')
  let 𝔴' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L'int) := 𝔴
  have h𝔴' : A.1.comap (algebraMap ↥L'int K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L'int 𝔴' := h𝔴
  have h𝔴𝔮 : 𝔴'.asIdeal.LiesOver 𝔮.asIdeal :=
    NK.ReconstructField.liesOver_of_comap_eq_valRingGen (K := ↥LL) (L := ↥L'int) (K' := K')
      𝔮 𝔴' A.1 h𝔴' h𝔮
  haveI h𝔴𝔮' : 𝔴'.asIdeal.LiesOver 𝔮.asIdeal := h𝔴𝔮
  have hp_dvd : p ∣ 𝔴'.asIdeal.inertiaDeg (NumberField.RingOfIntegers ↥LL) := by
    have hζint : ζ ∈ L'int := by
      rw [hGen]
      exact IntermediateField.subset_adjoin ↥LL ({ζ} : Set K') (Set.mem_singleton ζ)
    have hζsub : IsPrimitiveRoot (⟨ζ, hζint⟩ : ↥L'int) m :=
      IsPrimitiveRoot.coe_submonoidClass_iff.mp (by simpa using hζ)
    have hinj : Function.Injective
        (algebraMap ↥L'int (𝔴'.adicCompletion ↥L'int) : ↥L'int →+* _) :=
      RingHom.injective _
    have hcard : Nat.card (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers ↥LL)) = N := by
      rw [Commons.NumberTheory.NumberField.residueCard_adicCompletion_eq_absNorm 𝔮, ← hN]
    have hexp : (Nat.card (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers ↥LL))) ^ p - 1
        = m := by
      simp [hcard, hm]
    have hroot : IsPrimitiveRoot
        (algebraMap ↥L'int (𝔴'.adicCompletion ↥L'int) (⟨ζ, hζint⟩ : ↥L'int))
        ((Nat.card (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers ↥LL))) ^ p - 1) := by
      rw [hexp]
      exact hζsub.map_of_injective hinj
    exact NK.TameStructureDeep.TameDeep.inertiaDeg_dvd_of_isPrimitiveRoot
      (K := ↥LL) (L := ↥L'int) 𝔮 𝔴' h𝔴𝔮 hp.pos hroot
  have htower2 : 𝔴'.asIdeal.inertiaDeg (NumberField.RingOfIntegers F) =
      𝔮.asIdeal.inertiaDeg (NumberField.RingOfIntegers F) *
        𝔴'.asIdeal.inertiaDeg (NumberField.RingOfIntegers ↥LL) :=
    Ideal.inertiaDeg_tower (R := NumberField.RingOfIntegers F)
      (S := NumberField.RingOfIntegers ↥LL)
      (T := NumberField.RingOfIntegers ↥L'int) 𝔮.asIdeal 𝔴'.asIdeal
  have hdiv : p * 𝔮.asIdeal.inertiaDeg (NumberField.RingOfIntegers F) ∣
      𝔴'.asIdeal.inertiaDeg (NumberField.RingOfIntegers F) := by
    obtain ⟨k, hk⟩ := hp_dvd
    exact ⟨k, by rw [htower2, hk]; ring⟩
  exact ⟨L', le_sup_left, hunrL', 𝔮, 𝔴, h𝔮, h𝔴, hdiv⟩

end NK.NUV2.LC.RouteB
