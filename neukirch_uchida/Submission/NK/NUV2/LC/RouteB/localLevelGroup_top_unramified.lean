import Mathlib
import Submission.NK.NUV2.LC.RouteB.Defs
import Submission.NK.NUV2.LC.RouteB.decompRestrict_bij
import Submission.NK.NUV2.LC.finiteSupportTwistDefs

namespace NK.NUV2.LC.RouteB

open NK.GlobalCFT

/-! ## The stabiliser of a finite place is the decomposition group

The finite place `Place.ofFinite 𝔮` of a number field `L` is the prime `𝔮` of `𝓞 L`; the two
actions of `Gal(L/F)` on the finite `HeightOneSpectrum`s of `𝓞 L` that occur in the workspace
(`Submission.NeukirchUchida.Local.placeSmul`, built from `galRestrict`, and
`NK.GlobalCFT.Place.smulHeightOneSpectrum`, built from `Place.ringOfIntegersEquiv`) agree, so
the `MulAction.stabilizer` of `Place.ofFinite 𝔮` is the decomposition subgroup
`Submission.NeukirchUchida.Local.decompositionSubgroup 𝔮`. -/

/-- The two actions of `Gal(L/F)` on the finite places of `L` agree: `placeSmul` (from
`galRestrict`) is `Place.smulHeightOneSpectrum` (from `Place.ringOfIntegersEquiv`). -/
lemma localLevelGroup_placeSmul_eq {F L : Type} [Field F] [NumberField F] [Field L] [NumberField L]
    [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (σ : Gal(L/F)) (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    Submission.NeukirchUchida.Local.placeSmul σ 𝔮 =
      NK.GlobalCFT.Place.smulHeightOneSpectrum σ 𝔮 := by
  apply IsDedekindDomain.HeightOneSpectrum.ext
  simp only [Submission.NeukirchUchida.Local.placeSmul_asIdeal,
    NK.GlobalCFT.Place.smulHeightOneSpectrum_asIdeal,
    NK.GlobalCFT.Galois.ringOfIntegersEquiv_eq_galRestrict]
  exact congrArg (fun (f : NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers L) =>
    Ideal.map f 𝔮.asIdeal) rfl

/-- **The stabiliser of a finite place is the decomposition subgroup.** -/
lemma localLevelGroup_stabilizer_eq {F L : Type} [Field F] [NumberField F] [Field L] [NumberField L]
    [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    MulAction.stabilizer Gal(L/F) (NK.GlobalCFT.Place.ofFinite 𝔮) =
      Submission.NeukirchUchida.Local.decompositionSubgroup (K := F) 𝔮 := by
  ext σ
  rw [MulAction.mem_stabilizer_iff, Submission.NeukirchUchida.Local.mem_decompositionSubgroup,
    NK.GlobalCFT.Place.smul_ofFinite, NK.GlobalCFT.Place.ofFinite_inj]
  exact ⟨fun h => by rw [localLevelGroup_placeSmul_eq σ 𝔮]; exact h,
    fun h => by rw [← localLevelGroup_placeSmul_eq σ 𝔮]; exact h⟩

/-! ## A place over a finite prime

The hypotheses `hA` and `h𝔮` of the target -- that the valuation ring of the place `A` of the
separable closure restricts to the valuation ring of `𝔭` respectively `𝔮` -- determine `𝔮` as a
place above `𝔭`: passing the restriction to `F` through the intermediate field `↥L` exhibits the
`under` of `𝔮` as the prime cut out by `A`, whence by injectivity of `𝔮 ↦ 𝒪_{L,𝔮}` it is `𝔭`. -/

/-- **A place of a finite Galois level whose valuation ring restricts to `𝒪_{F,𝔭}` lies over
`𝔭`.** -/
lemma localLevelGroup_liesOver {F K' : Type} [Field F] [NumberField F] [Field K']
    [Algebra F K'] [IsSepClosure F K'] (L : FiniteGaloisIntermediateField F K')
    (A : NK.BrauerHasse.OverFinitePrime F K')
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (𝔮 : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers ↥(L : IntermediateField F K')))
    (hA : A.1.comap (algebraMap F K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F 𝔭)
    (h𝔮 : A.1.comap (algebraMap ↥(L : IntermediateField F K') K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
        ↥(L : IntermediateField F K') 𝔮) :
    𝔮.asIdeal.LiesOver 𝔭.asIdeal := by
  -- the algebra maps form a compatible tower `F → ↥L → K'`
  have htower : (algebraMap F K') =
      (algebraMap ↥(L : IntermediateField F K') K').comp
        (algebraMap F ↥(L : IntermediateField F K')) := by
    ext x
    exact IsScalarTower.algebraMap_apply F ↥(L : IntermediateField F K') K' x
  -- restricting `𝒪_{L,𝔮}` all the way to `F` gives `𝒪_{F,𝔭}`
  have hchain : (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
        ↥(L : IntermediateField F K') 𝔮).comap
        (algebraMap F ↥(L : IntermediateField F K')) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F 𝔭 := by
    rw [← h𝔮, ValuationSubring.comap_comap, ← htower, hA]
  -- the same restriction computed prime-theoretically is `𝒪_{F,𝔮.under}`
  have hliesUnder : 𝔮.asIdeal.LiesOver (𝔮.under (NumberField.RingOfIntegers F)).asIdeal := by
    rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
    infer_instance
  have hunder := Commons.RingTheory.Valuation.comap_valuationSubringAtPrime
      (K := F) (L := ↥(L : IntermediateField F K')) (𝔮.under (NumberField.RingOfIntegers F)) 𝔮
      hliesUnder
  -- `𝔮.under = 𝔭` by injectivity of `q ↦ 𝒪_{L,q}`
  have hpub : 𝔮.under (NumberField.RingOfIntegers F) = 𝔭 :=
    Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (by rw [← hunder, hchain])
  exact ⟨by rw [← hpub, IsDedekindDomain.HeightOneSpectrum.under_asIdeal]⟩

/-- **The local level group of the full Galois group at an unramified prime is cyclic of order
the inertia degree.**  For a number field `F` with separable closure `K'`, a finite Galois level
`L`, a place `A` of `K'` over a finite prime `𝔭` of `F` unramified in `L`, with `𝔮` the prime of
`L` below `A`: the local level group `(D_A)/(D_A ∩ Gal(K'/L))` (for the full group `⊤`) is cyclic
and has as many elements as the inertia degree of `𝔮` over `𝔭`. -/
theorem localLevelGroup_top_unramified {F K' : Type} [Field F] [NumberField F] [Field K']
    [Algebra F K'] [IsSepClosure F K'] (L : FiniteGaloisIntermediateField F K')
    (A : NK.BrauerHasse.OverFinitePrime F K')
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (𝔮 : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers ↥(L : IntermediateField F K')))
    (hA : A.1.comap (algebraMap F K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F 𝔭)
    (h𝔮 : A.1.comap (algebraMap ↥(L : IntermediateField F K') K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
        ↥(L : IntermediateField F K') 𝔮)
    (hunr : NK.HeckeL.IsUnramifiedIn (K := F) (L := ↥(L : IntermediateField F K')) 𝔭) :
    IsCyclic (NK.BrauerHasse.LocalLevelGroup (K := F) (K' := K')
        (⊤ : Subgroup Gal(K'/F)) A.1 L) ∧
      Nat.card (NK.BrauerHasse.LocalLevelGroup (K := F) (K' := K')
        (⊤ : Subgroup Gal(K'/F)) A.1 L) =
        𝔮.asIdeal.inertiaDeg (NumberField.RingOfIntegers F) := by
  -- `𝔮` is a place above `𝔭`, and it is unramified over `𝔭` by hypothesis
  have hliesOver := localLevelGroup_liesOver (F := F) (K' := K') L A 𝔭 𝔮 hA h𝔮
  have hram : 𝔮.asIdeal.ramificationIdx (NumberField.RingOfIntegers F) = 1 := hunr 𝔮 hliesOver
  -- a Frobenius element `σ` at `𝔮`; the decomposition group of `𝔮` is generated by it
  obtain ⟨σ, hσ⟩ := NK.Chebotarev.exists_isFrobAt (K := F)
    (L := ↥(L : IntermediateField F K')) 𝔭 𝔮 hliesOver
  have hdecomp := NK.ChebotarevGeneral.decompositionSubgroup_eq_zpowers_of_isFrobAt (K := F)
    (N := ↥(L : IntermediateField F K')) 𝔮 σ hram hσ
  -- the stabiliser of `Place.ofFinite 𝔮` is therefore also `⟨σ⟩`
  have hstab : MulAction.stabilizer Gal(↥(L : IntermediateField F K')/F)
      (NK.GlobalCFT.Place.ofFinite 𝔮) = Subgroup.zpowers σ := by
    rw [localLevelGroup_stabilizer_eq (F := F) 𝔮, hdecomp]
  -- the local level group is the decomposition group at the level
  obtain ⟨e, _he⟩ := NK.NUV2.LC.RouteB.decompRestrict_bij (K := F) (K' := K') A L 𝔮 h𝔮
  refine ⟨?_, ?_⟩
  · exact (MulEquiv.isCyclic e).mpr (by rw [hstab]; infer_instance)
  · calc Nat.card (NK.BrauerHasse.LocalLevelGroup (K := F) (K' := K')
          (⊤ : Subgroup Gal(K'/F)) A.1 L)
        = Nat.card (MulAction.stabilizer Gal(↥(L : IntermediateField F K')/F)
            (NK.GlobalCFT.Place.ofFinite 𝔮)) := Nat.card_congr e.toEquiv
      _ = Nat.card (Subgroup.zpowers σ) := by rw [hstab]
      _ = orderOf σ := Nat.card_zpowers σ
      _ = 𝔮.asIdeal.inertiaDeg (NumberField.RingOfIntegers F) :=
          NK.Chebotarev.IsFrobAtOrderOfEqInertiaDeg (p := 𝔭) (P := 𝔮) hliesOver hram hσ

end NK.NUV2.LC.RouteB
