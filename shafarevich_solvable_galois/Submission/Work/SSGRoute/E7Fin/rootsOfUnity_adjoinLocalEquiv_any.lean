import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.PTembedding.rootsOfUnity_addEquiv_adjoinLocalEquiv

/-!
# `μ_n(𝔨·Ω) ≅ μ_n(Ω)`, compatibly with the decomposition group

The main result of `PTembedding.rootsOfUnity_addEquiv_adjoinLocalEquiv` identifies `μ_p(𝔨·Ω)` with
`μ_p(K)` (`p` prime, `K/k` finite Galois containing a primitive `p`-th root of unity) — the
*finite* version.  This file proves the corresponding statement for **arbitrary** `n` with the
*full* separable closure `Ω` in place of `K`: the map `coInAdjoinHom : Ω →+* 𝔨·Ω` is injective and
carries a primitive `n`-th root of unity `ζ ∈ Ω` to a primitive `n`-th root of unity of `𝔨·Ω`, so
it induces an isomorphism of the groups of `n`-th roots of unity, and by
`NK.NeukirchUchida.decompositionToAdjoin_coInAdjoin` it intertwines the natural action of the
decomposition group `D_A` on `μ_n(Ω)` with the action on `μ_n(𝔨·Ω)` given by the identification
`NK.Mine.adjoinLocalEquiv : D_A ≃* Gal(𝔨·Ω/𝔨)`.
-/

open SSGRoute Work.SSGRoute

namespace Work.SSGRoute.E7Fin

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## The map `μ_n(Ω) → μ_n(𝔨·Ω)` induced by `coInAdjoin` -/

/-- **The map induced by `coInAdjoin` on the `n`-th roots of unity**: the composite of the
underlying map `Ω →+* 𝔨·Ω` of `coInAdjoin` with the restriction to `μ_n`. -/
def muAddAdjoinMapAny (n : ℕ) {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω]
    [Algebra k Ω] [IsSepClosure k Ω]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (A : ValuationSubring Ω)
    [Algebra (IsDedekindDomain.HeightOneSpectrum.adicCompletion k 𝔭)
      (NK.NeukirchUchida.placeCompletion A)] :
    Additive (rootsOfUnity n Ω) →+
      Additive (rootsOfUnity n (↥(NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A))) :=
  MonoidHom.toAdditive (restrictRootsOfUnity (PTembedding.coInAdjoinHom 𝔭 A) n)

theorem muAddAdjoinMapAny_apply (n : ℕ) {k : Type} [Field k] [NumberField k] {Ω : Type}
    [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (A : ValuationSubring Ω)
    [Algebra (IsDedekindDomain.HeightOneSpectrum.adicCompletion k 𝔭)
      (NK.NeukirchUchida.placeCompletion A)]
    (x : Additive (rootsOfUnity n Ω)) :
    muAddAdjoinMapAny n (𝔭 := 𝔭) A x
      = MonoidHom.toAdditive (restrictRootsOfUnity (PTembedding.coInAdjoinHom 𝔭 A) n) x := rfl

/-- The value of `muAddAdjoinMapAny` at the level of `rootsOfUnity`. -/
theorem muAddAdjoinMapAny_toMul (n : ℕ) {k : Type} [Field k] [NumberField k] {Ω : Type}
    [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (A : ValuationSubring Ω)
    [Algebra (IsDedekindDomain.HeightOneSpectrum.adicCompletion k 𝔭)
      (NK.NeukirchUchida.placeCompletion A)]
    (x : Additive (rootsOfUnity n Ω)) :
    Additive.toMul (muAddAdjoinMapAny n (𝔭 := 𝔭) A x)
      = restrictRootsOfUnity (PTembedding.coInAdjoinHom 𝔭 A) n (Additive.toMul x) := rfl

/-- The value of `muAddAdjoinMapAny` in the completion. -/
theorem muAddAdjoinMapAny_val (n : ℕ) {k : Type} [Field k] [NumberField k] {Ω : Type}
    [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (A : ValuationSubring Ω)
    [Algebra (IsDedekindDomain.HeightOneSpectrum.adicCompletion k 𝔭)
      (NK.NeukirchUchida.placeCompletion A)]
    (x : Additive (rootsOfUnity n Ω)) :
    (((Additive.toMul (muAddAdjoinMapAny n (𝔭 := 𝔭) A x) :
        rootsOfUnity n (↥(NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A))) :
        (↥(NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A))ˣ) :
        ↥(NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A))
      = PTembedding.coInAdjoinHom 𝔭 A
          (((Additive.toMul x : rootsOfUnity n Ω) : Ωˣ) : Ω) := by
  rw [muAddAdjoinMapAny_toMul, restrictRootsOfUnity_coe_apply]

theorem muAddAdjoinMapAny_injective (n : ℕ) {k : Type} [Field k] [NumberField k] {Ω : Type}
    [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (A : ValuationSubring Ω)
    [Algebra (IsDedekindDomain.HeightOneSpectrum.adicCompletion k 𝔭)
      (NK.NeukirchUchida.placeCompletion A)] :
    Function.Injective (muAddAdjoinMapAny n (𝔭 := 𝔭) A) := by
  have h1 : Function.Injective
      (restrictRootsOfUnity (PTembedding.coInAdjoinHom 𝔭 A) n) :=
    PTembedding.restrictRootsOfUnity_injective _
      (PTembedding.coInAdjoinHom_injective 𝔭 A) n
  intro x y hxy
  exact Additive.toMul.injective (h1 (congrArg Additive.toMul hxy))

/-- **Surjectivity**: every `n`-th root of unity of `𝔨·Ω` is the image of one of `Ω`, because
`ζ` is primitive in `Ω` (hence, `coInAdjoin` being injective, in `𝔨·Ω`) and generates `μ_n`. -/
theorem muAddAdjoinMapAny_surjective (n : ℕ) [NeZero n] {k : Type} [Field k] [NumberField k]
    {Ω : Type} [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (A : ValuationSubring Ω)
    [Algebra (IsDedekindDomain.HeightOneSpectrum.adicCompletion k 𝔭)
      (NK.NeukirchUchida.placeCompletion A)]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ n) :
    Function.Surjective (muAddAdjoinMapAny n (𝔭 := 𝔭) A) := by
  intro x
  have hζM : IsPrimitiveRoot (PTembedding.coInAdjoinHom 𝔭 A ζ) n :=
    hζ.map_of_injective (PTembedding.coInAdjoinHom_injective 𝔭 A)
  let u : rootsOfUnity n (↥(NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A)) := Additive.toMul x
  have hu : ((u : (↥(NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A))ˣ) :
      ↥(NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A)) ^ n = 1 :=
    (mem_rootsOfUnity' n (u : (↥(NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A))ˣ)).mp u.2
  obtain ⟨i, -, hi⟩ := hζM.eq_pow_of_pow_eq_one hu
  have hz : ζ ^ i ≠ 0 := pow_ne_zero i (hζ.ne_zero NeZero.out)
  let v : Ωˣ := Units.mk0 (ζ ^ i) hz
  have hv : v ^ n = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    show (ζ ^ i) ^ n = 1
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  refine ⟨Additive.ofMul ⟨v, (mem_rootsOfUnity n v).mpr hv⟩, ?_⟩
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  rw [muAddAdjoinMapAny_toMul, restrictRootsOfUnity_coe_apply]
  show PTembedding.coInAdjoinHom 𝔭 A (ζ ^ i) =
    ((u : (↥(NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A))ˣ) :
      ↥(NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A))
  rw [map_pow]
  exact hi

/-! ## The action of a subgroup of `G_k` on `μ_n(Ω)` and the field action -/

theorem toMul_smul_subgroup_rootsOfUnity {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (n : ℕ) (H : Subgroup (Ω ≃ₐ[k] Ω)) (h : ↥H) (y : Additive (rootsOfUnity n Ω)) :
    Additive.toMul (h • y) = PTembedding.MupKummer.muMapOfField k Ω n
      (h : Ω ≃ₐ[k] Ω) (Additive.toMul y) := rfl

theorem val_smul_subgroup_rootsOfUnity {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (n : ℕ) (H : Subgroup (Ω ≃ₐ[k] Ω)) (h : ↥H) (y : Additive (rootsOfUnity n Ω)) :
    (((Additive.toMul (h • y) : rootsOfUnity n Ω) : Ωˣ) : Ω)
      = (h : Ω ≃ₐ[k] Ω) (((Additive.toMul y : rootsOfUnity n Ω) : Ωˣ) : Ω) := by
  rw [toMul_smul_subgroup_rootsOfUnity, PTembedding.MupKummer.muMapOfField_coe,
    PT.algEquivUnitsMapOfField_coe]

theorem toMul_smul_algEquiv_rootsOfUnity {F E : Type} [Field F] [Field E] [Algebra F E]
    (n : ℕ) (τ : E ≃ₐ[F] E) (z : Additive (rootsOfUnity n E)) :
    Additive.toMul (τ • z) = PTembedding.MupKummer.muMapOfField F E n τ (Additive.toMul z) :=
  rfl

theorem val_smul_algEquiv_rootsOfUnity {F E : Type} [Field F] [Field E] [Algebra F E]
    (n : ℕ) (τ : E ≃ₐ[F] E) (z : Additive (rootsOfUnity n E)) :
    (((Additive.toMul (τ • z) : rootsOfUnity n E) : Eˣ) : E)
      = τ (((Additive.toMul z : rootsOfUnity n E) : Eˣ) : E) := by
  rw [toMul_smul_algEquiv_rootsOfUnity, PTembedding.MupKummer.muMapOfField_coe,
    PT.algEquivUnitsMapOfField_coe]

/-! ## The main result -/

/-- **The statement for an arbitrary prime `𝔭` of `k` below `A`** (the statement of
`rootsOfUnity_adjoinLocalEquiv_any` only ever uses `𝔭 = primeOf A hA`). -/
theorem rootsOfUnity_adjoinLocalEquiv_any_aux (n : ℕ) [NeZero n] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (A : ValuationSubring Ω)
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
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ n) :
    ∃ Ψ : Additive (rootsOfUnity n (↥(NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A))) ≃+
        Additive (rootsOfUnity n Ω),
      ∀ (σ : ↥(SSGRoute.decomp k A))
        (x : Additive (rootsOfUnity n (↥(NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A)))),
        Ψ ((NK.Mine.adjoinLocalEquiv 𝔭 A h𝔭 halg hW σ) • x) = σ • Ψ x := by
  have hbij : Function.Bijective (muAddAdjoinMapAny n (𝔭 := 𝔭) A) :=
    ⟨muAddAdjoinMapAny_injective n (𝔭 := 𝔭) A,
      muAddAdjoinMapAny_surjective n (𝔭 := 𝔭) A ζ hζ⟩
  let e : Additive (rootsOfUnity n Ω) ≃+
      Additive (rootsOfUnity n (↥(NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A))) :=
    AddEquiv.ofBijective (muAddAdjoinMapAny n (𝔭 := 𝔭) A) hbij
  have e_spec : ∀ z, e z = muAddAdjoinMapAny n (𝔭 := 𝔭) A z := fun z => rfl
  have hforward : ∀ (σ : ↥(SSGRoute.decomp k A)) (y : Additive (rootsOfUnity n Ω)),
      e (σ • y) = (NK.Mine.adjoinLocalEquiv 𝔭 A h𝔭 halg hW σ) • e y := by
    intro σ y
    have hD : (NK.Mine.adjoinLocalEquiv 𝔭 A h𝔭 halg hW σ)
        = NK.NeukirchUchida.decompositionToAdjoin 𝔭 A h𝔭 halg σ := rfl
    rw [hD]
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    rw [e_spec (σ • y), e_spec y, muAddAdjoinMapAny_val, val_smul_subgroup_rootsOfUnity,
      val_smul_algEquiv_rootsOfUnity, muAddAdjoinMapAny_val]
    exact (NK.NeukirchUchida.decompositionToAdjoin_coInAdjoin 𝔭 A h𝔭 halg σ
      (((Additive.toMul y : rootsOfUnity n Ω) : Ωˣ) : Ω)).symm
  refine ⟨e.symm, ?_⟩
  intro σ x
  have hkey : e (σ • e.symm x) = (NK.Mine.adjoinLocalEquiv 𝔭 A h𝔭 halg hW σ) • x := by
    rw [hforward σ (e.symm x), AddEquiv.apply_symm_apply]
  calc e.symm ((NK.Mine.adjoinLocalEquiv 𝔭 A h𝔭 halg hW σ) • x)
      = e.symm (e (σ • e.symm x)) := by rw [hkey]
    _ = σ • e.symm x := AddEquiv.symm_apply_apply e (σ • e.symm x)

theorem rootsOfUnity_adjoinLocalEquiv_any (n : ℕ) [NeZero n] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A)
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
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ n) :
    ∃ Ψ : Additive (rootsOfUnity n (↥(NK.NeukirchUchida.adjoinPlaceCompletion
          (Submission.NeukirchUchida.primeOf A hA) A))) ≃+ Additive (rootsOfUnity n Ω),
      ∀ (σ : ↥(SSGRoute.decomp k A))
        (x : Additive (rootsOfUnity n (↥(NK.NeukirchUchida.adjoinPlaceCompletion
          (Submission.NeukirchUchida.primeOf A hA) A)))),
        Ψ ((NK.Mine.adjoinLocalEquiv (Submission.NeukirchUchida.primeOf A hA) A
              (Submission.NeukirchUchida.primeOf_spec A hA) halg hW σ) • x)
          = σ • Ψ x :=
  rootsOfUnity_adjoinLocalEquiv_any_aux n k Ω A
    (Submission.NeukirchUchida.primeOf A hA) (Submission.NeukirchUchida.primeOf_spec A hA)
    halg hW ζ hζ

end

end Work.SSGRoute.E7Fin
