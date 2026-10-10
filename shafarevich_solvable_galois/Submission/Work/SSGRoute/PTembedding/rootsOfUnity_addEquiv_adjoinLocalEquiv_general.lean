import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.PTembedding.rootsOfUnity_addEquiv_adjoinLocalEquiv

/-!
# The local/global identification is compatible with the `n`-th roots of unity (general `n`)

This file generalises `rootsOfUnity_addEquiv_adjoinLocalEquiv` from a prime `p` to an arbitrary
non-zero `n`.  Nothing in the argument needed primality of `p`: the only two places where
`Fact p.Prime` entered the proof of the prime version were

* the "extensionality" lemmas `toMul_smul_ofField`, `toMul_smul_decomp`, `muMapOfField_val`
  (whose statements never used primality — the `Fact` hypothesis was a vestigial section
  variable), and
* the proof that the map on roots of unity is *surjective*, which used
  `IsPrimitiveRoot.eq_pow_of_pow_eq_one` (`[NeZero p]` suffices, together with the fact that the
  target is a domain) together with `IsPrimitiveRoot.ne_zero`.

Consequently the same proof, with `p` replaced by `n` and `Fact p.Prime` by `NeZero n`, gives the
general statement: for a finite Galois extension `K/k` inside `Ω` containing a primitive `n`-th
root of unity `ζ`, the groups `μ_n(M)` (`M = 𝔨·Ω`) and `μ_n(K)` are isomorphic, compatibly with
the action of the decomposition group `D_A` via `NK.Mine.adjoinLocalEquiv`.

The main result is `rootsOfUnity_addEquiv_adjoinLocalEquiv_general`.
-/

open Work.SSGRoute

namespace Work.SSGRoute.PTembedding

noncomputable section

open scoped Pointwise

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## The `n`-th roots of unity and the Galois action (primality-free restatements) -/

section Naturality

/-- The underlying element of `M` of `MupKummer.muMapOfField F E n g v` is `g` applied to the
underlying element of `v`; the primality-free version of `muMapOfField_val`. -/
theorem muMapOfField_valN {F E : Type} [Field F] [Field E] [Algebra F E] {n : ℕ}
    (g : E ≃ₐ[F] E) (v : rootsOfUnity n E) :
    (((MupKummer.muMapOfField F E n g v : rootsOfUnity n E) : Eˣ) : E) =
      g ((v : Eˣ) : E) := by
  rw [MupKummer.muMapOfField_coe, Work.SSGRoute.PT.algEquivUnitsMapOfField_coe]

/-- The action of `Gal(K/F)` on `μ_n(K)` through `MupKummer.muMapOfField`;
the primality-free version of `toMul_smul_ofField`. -/
theorem toMul_smul_ofFieldN {F E : Type} [Field F] [Field E] [Algebra F E]
    {K : IntermediateField F E} {n : ℕ} (g : ↥K ≃ₐ[F] ↥K) (x : MupCard.MuAdd n K) :
    Additive.toMul (g • x) = MupKummer.muMapOfField F ↥K n g (Additive.toMul x) := rfl

/-- The action of the decomposition group of `A` on `μ_n(K)` goes through the restriction
`res k K`; the primality-free version of `toMul_smul_decomp`. -/
theorem toMul_smul_decompN {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω]
    {K : IntermediateField k Ω} [IsGalois k K] {n : ℕ}
    (A : ValuationSubring Ω) (σ : ↥(SSGRoute.decomp k A)) (x : MupCard.MuAdd n K) :
    Additive.toMul (σ • x) =
      MupKummer.muMapOfField k ↥K n (SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω))
        (Additive.toMul x) := rfl

end Naturality

/-! ## The map `μ_n(K) → μ_n(𝔨·Ω)` -/

section GeneralN

variable {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω]
  [IsSepClosure k Ω]

/-- **The map `μ_n(K) → μ_n(𝔨·Ω)`** induced by the inclusion `K ⊆ Ω` followed by `coInAdjoin`;
the general-`n` version of `muAddAdjoinMap`. -/
def muAddAdjoinMapN (n : ℕ) (K : IntermediateField k Ω)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (A : ValuationSubring Ω)
    [Algebra (IsDedekindDomain.HeightOneSpectrum.adicCompletion k 𝔭)
      (NK.NeukirchUchida.placeCompletion A)] :
    MupCard.MuAdd n K →+ MupCard.MuAdd n (NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A) :=
  MonoidHom.toAdditive ((restrictRootsOfUnity (coInAdjoinHom 𝔭 A) n).comp
    (restrictRootsOfUnity (algebraMap ↥K Ω) n))

theorem muAddAdjoinMapN_apply (n : ℕ) (K : IntermediateField k Ω)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (A : ValuationSubring Ω)
    [Algebra (IsDedekindDomain.HeightOneSpectrum.adicCompletion k 𝔭)
      (NK.NeukirchUchida.placeCompletion A)] (x : MupCard.MuAdd n K) :
    Additive.toMul (muAddAdjoinMapN n K 𝔭 A x)
      = (restrictRootsOfUnity (coInAdjoinHom 𝔭 A) n)
        ((restrictRootsOfUnity (algebraMap ↥K Ω) n) (Additive.toMul x)) := rfl

/-- The underlying element of `M` of `muAddAdjoinMapN n K 𝔭 A x`. -/
theorem muAddAdjoinMapN_val (n : ℕ) (K : IntermediateField k Ω)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (A : ValuationSubring Ω)
    [Algebra (IsDedekindDomain.HeightOneSpectrum.adicCompletion k 𝔭)
      (NK.NeukirchUchida.placeCompletion A)] (x : MupCard.MuAdd n K) :
    (((Additive.toMul (muAddAdjoinMapN n K 𝔭 A x) :
        rootsOfUnity n ↥(NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A)) :
        (↥(NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A))ˣ) :
        ↥(NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A))
      = coInAdjoinHom 𝔭 A
          (algebraMap ↥K Ω (((Additive.toMul x : rootsOfUnity n ↥K) : (↥K)ˣ) : ↥K)) := by
  rw [muAddAdjoinMapN_apply, restrictRootsOfUnity_coe_apply, restrictRootsOfUnity_coe_apply]

/-- **Injectivity** of `muAddAdjoinMapN`, from the injectivity of `coInAdjoinHom` (and of the
inclusion `K ⊆ Ω`). -/
theorem muAddAdjoinMapN_injective (n : ℕ) (K : IntermediateField k Ω)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (A : ValuationSubring Ω)
    [Algebra (IsDedekindDomain.HeightOneSpectrum.adicCompletion k 𝔭)
      (NK.NeukirchUchida.placeCompletion A)] :
    Function.Injective (muAddAdjoinMapN n K 𝔭 A) := by
  have h1 : Function.Injective (restrictRootsOfUnity (coInAdjoinHom 𝔭 A) n) :=
    restrictRootsOfUnity_injective (coInAdjoinHom 𝔭 A) (coInAdjoinHom_injective 𝔭 A) n
  have h2 : Function.Injective (restrictRootsOfUnity (algebraMap ↥K Ω) n) :=
    restrictRootsOfUnity_injective (algebraMap ↥K Ω) (RingHom.injective (algebraMap ↥K Ω)) n
  have h3 : Function.Injective (fun z : rootsOfUnity n ↥K =>
      (restrictRootsOfUnity (coInAdjoinHom 𝔭 A) n)
        ((restrictRootsOfUnity (algebraMap ↥K Ω) n) z)) := h1.comp h2
  intro x y hxy
  exact Additive.toMul.injective (h3 (congrArg Additive.toMul hxy))

/-- **Surjectivity**: every `n`-th root of unity of `M = 𝔨·Ω` is the image of one of `K`, because
`ζ` is primitive in `Ω` (hence, by injectivity of `coInAdjoinHom`, in `M`) and every `n`-th root
of unity of a field is a power of a primitive one. -/
theorem muAddAdjoinMapN_surjective (n : ℕ) [NeZero n] (K : IntermediateField k Ω)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (A : ValuationSubring Ω)
    [Algebra (IsDedekindDomain.HeightOneSpectrum.adicCompletion k 𝔭)
      (NK.NeukirchUchida.placeCompletion A)]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ n) (hζK : ζ ∈ K) :
    Function.Surjective (muAddAdjoinMapN n K 𝔭 A) := by
  intro x
  have hζM : IsPrimitiveRoot (coInAdjoinHom 𝔭 A ζ) n :=
    hζ.map_of_injective (f := coInAdjoinHom 𝔭 A) (coInAdjoinHom_injective 𝔭 A)
  let u : rootsOfUnity n ↥(NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A) := Additive.toMul x
  have hu : ((u : (↥(NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A))ˣ) :
      ↥(NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A)) ^ n = 1 :=
    (mem_rootsOfUnity' n (u : (↥(NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A))ˣ)).mp u.2
  obtain ⟨i, -, hi⟩ := hζM.eq_pow_of_pow_eq_one hu
  have hw0 : (⟨ζ ^ i, pow_mem hζK i⟩ : ↥K) ≠ 0 := by
    intro h
    have h2 : (ζ ^ i : Ω) = 0 := congrArg Subtype.val h
    exact pow_ne_zero i (hζ.ne_zero (NeZero.ne n)) h2
  let v : (↥K)ˣ := Units.mk0 ⟨ζ ^ i, pow_mem hζK i⟩ hw0
  have hv : v ^ n = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    show (⟨ζ ^ i, pow_mem hζK i⟩ : ↥K) ^ n = 1
    refine Subtype.ext ?_
    simp only [IntermediateField.coe_pow, IntermediateField.coe_one]
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  refine ⟨Additive.ofMul ⟨v, (mem_rootsOfUnity n v).mpr hv⟩, ?_⟩
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  rw [muAddAdjoinMapN_val]
  show coInAdjoinHom 𝔭 A (ζ ^ i) =
    ((u : (↥(NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A))ˣ) :
      ↥(NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A))
  rw [map_pow]
  exact hi

/-- **`muAddAdjoinMapN` intertwines the action of `D_A` with the action of `Gal(M/𝔨)`** under the
identification `adjoinLocalEquiv`: this is `decompositionToAdjoin_coInAdjoin`. -/
theorem muAddAdjoinMapN_smul (n : ℕ) (A : ValuationSubring Ω)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (h𝔭 : A.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k 𝔭)
    [Algebra (IsDedekindDomain.HeightOneSpectrum.adicCompletion k 𝔭)
      (NK.NeukirchUchida.placeCompletion A)]
    (halg : ∀ z : IsDedekindDomain.HeightOneSpectrum.adicCompletion k 𝔭,
      (algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion k 𝔭)
        (NK.NeukirchUchida.placeCompletion A)) z =
        NK.NeukirchUchida.adicCompletionToPlaceCompletion 𝔭 A h𝔭 z)
    (hW : (NK.NeukirchUchida.placeCompletionIntegers A).comap
        (NK.NeukirchUchida.adicCompletionToPlaceCompletion 𝔭 A h𝔭) =
      IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers k 𝔭)
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (σ : ↥(SSGRoute.decomp k A)) (x : MupCard.MuAdd n K) :
    muAddAdjoinMapN n K 𝔭 A (σ • x) =
      (NK.Mine.adjoinLocalEquiv 𝔭 A h𝔭 halg hW σ) • muAddAdjoinMapN n K 𝔭 A x := by
  let D : ↥(NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A) ≃ₐ[
      IsDedekindDomain.HeightOneSpectrum.adicCompletion k 𝔭]
      ↥(NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A) :=
    NK.NeukirchUchida.decompositionToAdjoin 𝔭 A h𝔭 halg σ
  have hD : (NK.Mine.adjoinLocalEquiv 𝔭 A h𝔭 halg hW σ) = D := rfl
  have hDco : ∀ y : Ω, D (coInAdjoinHom 𝔭 A y) =
      coInAdjoinHom 𝔭 A ((σ : Ω ≃ₐ[k] Ω) y) := fun y =>
    NK.NeukirchUchida.decompositionToAdjoin_coInAdjoin 𝔭 A h𝔭 halg σ y
  rw [hD]
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  rw [muAddAdjoinMapN_val, toMul_smul_decompN, toMul_smul_ofFieldN, muMapOfField_valN,
    muMapOfField_valN, muAddAdjoinMapN_val, res_apply_eq, hDco]

end GeneralN

/-- **The explicit local/global identification is compatible with the `n`-th roots of unity.**

Let `k` be a number field, `Ω` an algebraic closure of `k`, `A` a finite place of `Ω` over `k`,
`𝔭` the prime of `k` below `A`, `𝔨 = k_𝔭` the `𝔭`-adic completion of `k` and
`M = 𝔨·Ω ⊆ placeCompletion A` the subfield generated by (the image of) `𝔨` and (that of) `Ω`
(`NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A`).

Let `K` be a finite Galois extension of `k` inside `Ω` containing a primitive `n`-th root of unity
`ζ`.  Then there is an isomorphism `μ_n(M) ≅ μ_n(K)` compatible with the action of the
decomposition group `D_A = decomp k A`: under the explicit identification
`NK.Mine.adjoinLocalEquiv : D_A ≃* Gal(M/𝔨)`, the action on `μ_n(M)`
(written `Additive (rootsOfUnity n M)`) corresponds to the action on `MupCard.MuAdd n K`. -/
theorem rootsOfUnity_addEquiv_adjoinLocalEquiv_general
    (n : ℕ) [NeZero n] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    [Algebra (IsDedekindDomain.HeightOneSpectrum.adicCompletion k
        (Submission.NeukirchUchida.primeOf A hA)) (NK.NeukirchUchida.placeCompletion A)]
    (halg : ∀ z : IsDedekindDomain.HeightOneSpectrum.adicCompletion k
        (Submission.NeukirchUchida.primeOf A hA),
      (algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion k
          (Submission.NeukirchUchida.primeOf A hA))
        (NK.NeukirchUchida.placeCompletion A)) z =
        NK.NeukirchUchida.adicCompletionToPlaceCompletion
          (Submission.NeukirchUchida.primeOf A hA) A
          (Submission.NeukirchUchida.primeOf_spec A hA) z)
    (hW : (NK.NeukirchUchida.placeCompletionIntegers A).comap
        (NK.NeukirchUchida.adicCompletionToPlaceCompletion
          (Submission.NeukirchUchida.primeOf A hA) A
          (Submission.NeukirchUchida.primeOf_spec A hA)) =
      IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers k
        (Submission.NeukirchUchida.primeOf A hA))
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ n) (hζK : ζ ∈ K) :
    ∃ Ψ : Additive (rootsOfUnity n (↥(NK.NeukirchUchida.adjoinPlaceCompletion
          (Submission.NeukirchUchida.primeOf A hA) A))) ≃+ MupCard.MuAdd n K,
      ∀ (σ : ↥(SSGRoute.decomp k A))
        (x : Additive (rootsOfUnity n (↥(NK.NeukirchUchida.adjoinPlaceCompletion
          (Submission.NeukirchUchida.primeOf A hA) A)))),
        Ψ ((NK.Mine.adjoinLocalEquiv (Submission.NeukirchUchida.primeOf A hA) A
              (Submission.NeukirchUchida.primeOf_spec A hA) halg hW σ) • x)
          = σ • Ψ x := by
  have hb : Function.Bijective (muAddAdjoinMapN n K
      (Submission.NeukirchUchida.primeOf A hA) A) :=
    ⟨muAddAdjoinMapN_injective n K (Submission.NeukirchUchida.primeOf A hA) A,
      muAddAdjoinMapN_surjective n K (Submission.NeukirchUchida.primeOf A hA) A
        ζ hζ hζK⟩
  let e : MupCard.MuAdd n K ≃+
      MupCard.MuAdd n (NK.NeukirchUchida.adjoinPlaceCompletion
        (Submission.NeukirchUchida.primeOf A hA) A) :=
    AddEquiv.ofBijective (muAddAdjoinMapN n K
      (Submission.NeukirchUchida.primeOf A hA) A) hb
  refine ⟨e.symm, ?_⟩
  intro σ x
  have hkey : e (σ • e.symm x) =
      (NK.Mine.adjoinLocalEquiv (Submission.NeukirchUchida.primeOf A hA) A
        (Submission.NeukirchUchida.primeOf_spec A hA) halg hW σ) • x := by
    have h1 : muAddAdjoinMapN n K (Submission.NeukirchUchida.primeOf A hA) A
        (σ • e.symm x) =
        (NK.Mine.adjoinLocalEquiv (Submission.NeukirchUchida.primeOf A hA) A
          (Submission.NeukirchUchida.primeOf_spec A hA) halg hW σ) •
          muAddAdjoinMapN n K (Submission.NeukirchUchida.primeOf A hA) A (e.symm x) :=
      muAddAdjoinMapN_smul n A (Submission.NeukirchUchida.primeOf A hA)
        (Submission.NeukirchUchida.primeOf_spec A hA) halg hW K σ (e.symm x)
    have h2 : muAddAdjoinMapN n K (Submission.NeukirchUchida.primeOf A hA) A (e.symm x) = x :=
      AddEquiv.apply_symm_apply e x
    calc e (σ • e.symm x)
        = muAddAdjoinMapN n K (Submission.NeukirchUchida.primeOf A hA) A (σ • e.symm x) := rfl
      _ = (NK.Mine.adjoinLocalEquiv (Submission.NeukirchUchida.primeOf A hA) A
            (Submission.NeukirchUchida.primeOf_spec A hA) halg hW σ) •
            muAddAdjoinMapN n K (Submission.NeukirchUchida.primeOf A hA) A (e.symm x) := h1
      _ = (NK.Mine.adjoinLocalEquiv (Submission.NeukirchUchida.primeOf A hA) A
            (Submission.NeukirchUchida.primeOf_spec A hA) halg hW σ) • x := by rw [h2]
  calc e.symm ((NK.Mine.adjoinLocalEquiv (Submission.NeukirchUchida.primeOf A hA) A
        (Submission.NeukirchUchida.primeOf_spec A hA) halg hW σ) • x)
      = e.symm (e (σ • e.symm x)) := by rw [hkey]
    _ = σ • e.symm x := AddEquiv.symm_apply_apply e (σ • e.symm x)

end

end Work.SSGRoute.PTembedding
