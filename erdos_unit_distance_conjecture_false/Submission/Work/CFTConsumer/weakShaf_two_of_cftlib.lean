import Mathlib
import Submission.Work.CFTConsumer.Defs
import Submission.Work.CFT.Kummer.All
import Submission.Work.CFT.Kummer.deltaK_eq_zero_of_totallyReal
import Submission.Work.Tower.Shafarevich.Group.generatorRank_eq_finrank_H1

namespace Work.CFTConsumer

open NumberField
open scoped Classical nonZeroDivisors

/-- A totally real number field contains no primitive cube root of unity, so the indicator
`CFTLib.delta F 3` vanishes.  (Reduced to the Kummer indicator `deltaK`, for which the
corresponding statement is `Work.CFT.Kummer.deltaK_eq_zero_of_totallyReal`.) -/
theorem delta_three_eq_zero_of_totallyReal (F : Type) [Field F] [NumberField F]
    [NumberField.IsTotallyReal F] : CFTLib.delta F 3 = 0 := by
  have h0 : Work.CFT.Kummer.deltaK F 3 = 0 :=
    Work.CFT.Kummer.deltaK_eq_zero_of_totallyReal F 3 (by norm_num) (by norm_num)
  rw [Work.CFT.Kummer.deltaK_eq_zero_iff] at h0
  unfold CFTLib.delta
  by_cases h : ∃ ζ : F, IsPrimitiveRoot ζ 3
  · exfalso
    obtain ⟨ζ, hζ⟩ := h
    obtain ⟨u, hu⟩ := hζ.isUnit (by norm_num : (3 : ℕ) ≠ 0)
    exact h0 ⟨u, IsPrimitiveRoot.coe_units_iff.mp (hu ▸ hζ)⟩
  · simp [h]

/-- For a totally real number field of degree `3`, `r₁ + r₂ - 1 = 2`. -/
theorem nrRealPlaces_add_nrComplexPlaces_sub_one (F : Type) [Field F] [NumberField F]
    [NumberField.IsTotallyReal F] (hdeg : Module.finrank ℚ F = 3) :
    InfinitePlace.nrRealPlaces F + InfinitePlace.nrComplexPlaces F - 1 = 2 := by
  have h1 : InfinitePlace.nrRealPlaces F = 3 := by
    rw [← NumberField.IsTotallyReal.finrank F, hdeg]
  have h2 : InfinitePlace.nrComplexPlaces F = 0 :=
    NumberField.IsTotallyReal.nrComplexPlaces_eq_zero F
  omega

/-- **Shafarevich's relation-rank estimate from the shared CFT interfaces.**

`Work.CFTConsumer.WeakShaf 2` says: for a totally real cubic field `F`, a finite
everywhere-unramified Galois `3`-extension `K/F` and a finite set `T` of nonzero primes of `F`
which splits completely in `K`, has trivial Frobenius classes in the Frattini quotient
(`IsFrobeniusTrivialInFrattini`) and with respect to which `K` is maximal among the `T`-split
extensions,
`proPRelationRank 3 (Gal(K/F)) ≤ generatorRank (Gal(K/F)) + 2 + |T|`.

Proof route (all ingredients are in the workspace): apply `CFTLib.ShafBound` to `F`, `K`, `p = 3`
and the set `T' : Finset (HeightOneSpectrum (𝓞 F))` of the elements of `T` (built with the
primality and nonzero proofs given in `T`; `T'.card ≤ T.card`);

* `CFTLib.IsUnramified F K` from `Work.Tower.IsUnramifiedExtension F K`: the finite part is
  `Work.Tower.isUnramifiedExtension_iff_forallPrimes` +
  `Work.Tower.isUnramifiedExtensionForallPrimes_iff_differentIdeal_eq_top`, the infinite part is
  `IsUnramifiedAtInfinitePlaces_of_odd_finrank` (the degree is odd because `Gal(K/F)` is a
  `3`-group: `IsPGroup.iff_card`, `IsGalois.card_aut_eq_finrank`);
* `CFTLib.SplitsAt F K T'` from the hypothesis `∀ 𝔭 ∈ T, Work.Tower.SplitsCompletelyIn F K 𝔭`
  via `Work.CFTConsumer.EFOne.of_splitsCompletelyIn` (and `Ideal.inertiaDegIn`);
* `CFTLib.ClassCond F K 3 T'` from `h2` (`MaximalClassCond`) applied to `F`, `K`, `T'`: its
  maximality hypothesis `CFTLib.IsMaximalUnramified F K 3 T'` follows from
  `IsMaximalSplittingExtension F K T` (a `T`-split competitor is in particular `T'`-split, using
  `CFTLib.SplitsAt` + unramifiedness to get `Work.Tower.SplitsCompletelyIn`), and its splitting
  hypothesis is the `SplitsAt` above;
* the numerical side `InfinitePlace.nrRealPlaces F + InfinitePlace.nrComplexPlaces F - 1 = 2`,
  from `NumberField.IsTotallyReal.nrComplexPlaces_eq_zero` and
  `NumberField.IsTotallyReal.finrank` with `Module.finrank ℚ F = 3`;
* `CFTLib.delta F 3 = 0` (no primitive cube root of unity in a totally real field; cf.
  `Work.CFT.Kummer.deltaK_eq_zero_of_totallyReal`, `Work.CFT.Kummer.deltaK_eq_one_iff`);
* `Work.Tower.Shafarevich.generatorRank_eq_finrank_H1` to replace `dim H¹` by `generatorRank`
  (`proPRelationRank 3 G` is by definition `dim H²`). -/
theorem weakShaf_two_of_cftlib (h1 : CFTLib.ShafBound) (h2 : CFTLib.MaximalClassCond) :
    Work.CFTConsumer.WeakShaf 2 := by
  intro F _ _ _ hdeg K _ _ _ _ _ hKunr hK3 T hTprime hTne hfrob hmax hsplit
  -- The set `T'` of height-one primes of `𝓞 F` underlying the nonzero primes of `T`.
  let T' : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :=
    T.attach.image fun 𝔭 => ⟨𝔭.1, hTprime 𝔭.1 𝔭.2, hTne 𝔭.1 𝔭.2⟩
  have hcard : T'.card ≤ T.card := by
    simp only [T']
    rw [← Finset.card_attach (s := T)]
    exact Finset.card_image_le
  have hmem : ∀ (𝔭 : Ideal (𝓞 F)) (h𝔭 : 𝔭 ∈ T),
      (⟨𝔭, hTprime 𝔭 h𝔭, hTne 𝔭 h𝔭⟩ : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) ∈ T' := by
    intro 𝔭 h𝔭
    simp only [T']
    exact Finset.mem_image.mpr ⟨⟨𝔭, h𝔭⟩, Finset.mem_attach T ⟨𝔭, h𝔭⟩, rfl⟩
  have hasIdeal : ∀ v ∈ T', v.asIdeal ∈ T := by
    intro v hv
    simp only [T'] at hv
    obtain ⟨𝔭, -, heq⟩ := Finset.mem_image.mp hv
    have h2 : (⟨𝔭.1, hTprime 𝔭.1 𝔭.2, hTne 𝔭.1 𝔭.2⟩ :
        IsDedekindDomain.HeightOneSpectrum (𝓞 F)).asIdeal = v.asIdeal :=
      congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal heq
    have h1 : v.asIdeal = 𝔭.1 := h2.symm
    exact h1 ▸ 𝔭.2
  -- `Gal(K/F)` is a finite `3`-group, hence `[K : F]` is odd.
  have hodd : Odd (Module.finrank F K) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hK3
    rw [IsGalois.card_aut_eq_finrank] at hn
    rw [hn]
    exact Odd.pow (by norm_num : Odd (3 : ℕ))
  -- Unramifiedness in the sense of the shared interface.
  have hunr : CFTLib.IsUnramified F K := by
    refine ⟨?_, ?_⟩
    · rw [← Work.Tower.isUnramifiedExtensionForallPrimes_iff_differentIdeal_eq_top]
      exact hKunr.forallPrimes
    · exact IsUnramifiedAtInfinitePlaces_of_odd_finrank hodd
  -- `T'` splits in `K`.
  have hsplitAt : CFTLib.SplitsAt F K T' := by
    intro v hv
    have hvT : v.asIdeal ∈ T := hasIdeal v hv
    have hsc : Work.Tower.SplitsCompletelyIn F K v.asIdeal := hsplit v.asIdeal hvT
    have hne : v.asIdeal ≠ ⊥ := hTne v.asIdeal hvT
    have hef : EFOne F K v.asIdeal := EFOne.of_splitsCompletelyIn hne hsc
    haveI : IsGaloisGroup Gal(K/F) (𝓞 F) (𝓞 K) :=
      IsGaloisGroup.of_isFractionRing Gal(K/F) (𝓞 F) (𝓞 K) F K
    obtain ⟨P⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 K)))
    haveI : P.1.IsPrime := P.2.1
    haveI : P.1.LiesOver v.asIdeal := P.2.2
    rw [Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal P.1 Gal(K/F)]
    exact (hef P).2
  -- `K` is maximal among the everywhere-unramified `3`-extensions in which `T'` splits.
  have hmaxUnr : CFTLib.IsMaximalUnramified F K 3 T' := by
    intro L _ _ _ _ _ hL3 hLunr hLsplit
    have hunrForall : Work.Tower.IsUnramifiedExtensionForallPrimes F L :=
      (Work.Tower.isUnramifiedExtensionForallPrimes_iff_differentIdeal_eq_top).mpr hLunr.1
    have hunrExt : Work.Tower.IsUnramifiedExtension F L :=
      Work.Tower.IsUnramifiedExtension.of_forallPrimes hunrForall
    have hsplitT : ∀ 𝔭 ∈ T, Work.Tower.SplitsCompletelyIn F L 𝔭 := by
      intro 𝔭 h𝔭
      have hprime : 𝔭.IsPrime := hTprime 𝔭 h𝔭
      have hne : 𝔭 ≠ ⊥ := hTne 𝔭 h𝔭
      have hf : Ideal.inertiaDegIn 𝔭 (𝓞 L) = 1 :=
        hLsplit ⟨𝔭, hprime, hne⟩ (hmem 𝔭 h𝔭)
      haveI : IsGaloisGroup Gal(L/F) (𝓞 F) (𝓞 L) :=
        IsGaloisGroup.of_isFractionRing Gal(L/F) (𝓞 F) (𝓞 L) F L
      have hef : EFOne F L 𝔭 := by
        intro P
        haveI : P.1.IsPrime := P.2.1
        haveI : P.1.LiesOver 𝔭 := P.2.2
        exact ⟨hunrForall P.1 P.2.1,
          by rw [← Ideal.inertiaDegIn_eq_inertiaDeg 𝔭 P.1 Gal(L/F)]; exact hf⟩
      exact EFOne.splitsCompletelyIn hprime hne hef
    obtain ⟨f, -⟩ := hmax L hunrExt hL3 hsplitT
    exact ⟨f⟩
  -- The class condition, from maximality.
  have hclass : CFTLib.ClassCond F K 3 T' := h2 F K 3 T' hK3 hunr hsplitAt hmaxUnr
  -- Shafarevich's bound.
  have hbound := h1 F K 3 T' hK3 hunr hsplitAt hclass
  have hdelta : CFTLib.delta F 3 = 0 := delta_three_eq_zero_of_totallyReal F
  have hnum : InfinitePlace.nrRealPlaces F + InfinitePlace.nrComplexPlaces F - 1 = 2 :=
    nrRealPlaces_add_nrComplexPlaces_sub_one F hdeg
  have key : Module.finrank (ZMod 3) (Work.Tower.Shafarevich.H2Fp 3 (K ≃ₐ[F] K)) ≤
      Module.finrank (ZMod 3) (Work.Tower.Shafarevich.H1Fp 3 (K ≃ₐ[F] K)) + 2 + T.card := by
    have hb : Module.finrank (ZMod 3) (Work.Tower.Shafarevich.H2Fp 3 (K ≃ₐ[F] K)) ≤
        Module.finrank (ZMod 3) (Work.Tower.Shafarevich.H1Fp 3 (K ≃ₐ[F] K)) +
          (InfinitePlace.nrRealPlaces F + InfinitePlace.nrComplexPlaces F - 1) +
            CFTLib.delta F 3 + T'.card := hbound
    rw [hnum, hdelta] at hb
    omega
  rw [Work.Tower.Shafarevich.proPRelationRank,
    Work.Tower.Shafarevich.generatorRank_eq_finrank_H1 3 (K ≃ₐ[F] K) hK3]
  exact key

end Work.CFTConsumer
