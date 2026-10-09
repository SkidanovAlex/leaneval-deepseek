import Mathlib
import Submission.NK.Mine.AdjoinLocalGalois
import Submission.Work.SSGRoute.ZDataMup.mupLocalVocab
import Submission.Work.SSGRoute.ZDataMup.mupLocalForm
import Submission.Work.SSGRoute.finite_openKernel_homs_decomp_kernel

/-!
# The "bad case" of the norm localisation: an element of `K'` that is a `p`-th power in the
completion is a `p`-th power in the decomposition field

`NOTES_hcyc_carry_reduction.md` §50.6 and
`PING_injectivity_without_norm_localisation.md` reduce the node
`PT.kummerHilbertCyclic_levelGroup_pt` to two halves.  The *delicate* half (the norm
localisation `(δ)`) is **not needed**: the target follows from injectivity of `α¹`, and injectivity
is detected by the *local* level (local class field theory on the completion), which requires only
the *trivial* direction `N_{F/𝒦}Fˣ ⊆ N_{E/κ}Eˣ` of the norm comparison — see the PING.

The statement that makes this work — and the only genuinely new mathematical input — is the
following, proved here:

> if `α ∈ K'` is a `p`-th power in the completion `K_𝔭` of the number field `K`
> (`K'` a separable closure of `K`, `𝔭` the prime of `K` below the place of `K'` given by `A`),
> then `α` is a `p`-th power in the decomposition field `Ω ^ D_A`.

Classically this says that the localisation map `𝒦ˣ/(𝒦ˣ)^p → κˣ/(κˣ)^p` is injective — the
Kummer group of the decomposition field `𝒦` is exactly the local one.  The proof uses the
on-disk fact that *the elements of the completion of `K'` which are algebraic over `K` are exactly
the image of `K'`* (`NK.NeukirchUchida.isAlgebraic_iff_exists_placeCompletionCoe`): a `p`-th root
`u ∈ K_𝔭` of `α` is algebraic over `K`, hence is the image of some `y ∈ K'` with `y^p = α`; and
`y` is fixed by the decomposition group because the decomposition group acts on the adjoined
completion `M = K_𝔭 · K'` through `K_𝔭`-algebra automorphisms (`NK.Mine.adjoinLocalEquiv`) which
fix `K_𝔭` pointwise, while `y ∈ K'` has its image in `K_𝔭`.

The two lemmas below are the two steps; the second is the form consumed by the injectivity route.
-/

open scoped Pointwise

namespace Work.SSGRoute.PT

variable {K K' : Type*} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **Core step**: an element `y ∈ K'` whose image in the adjoined completion `M = K_𝔭 · K'` lies
in `K_𝔭` is fixed by the decomposition group of `A`.

The proof is the computation `(adjoinLocalEquiv σ)(coInAdjoin y) = coInAdjoin (σ y)` (the action on
the image of `K'` is the Galois action, `decompositionToAdjoin_coInAdjoin`) together with the fact
that `adjoinLocalEquiv σ` is `K_𝔭`-linear, hence fixes `K_𝔭` pointwise. -/
theorem mem_fixedField_of_coInAdjoin_mem_range
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K 𝔭)
    [Algebra (𝔭.adicCompletion K) (NK.NeukirchUchida.placeCompletion A)]
    (halg : ∀ z : 𝔭.adicCompletion K,
      algebraMap _ _ z = NK.NeukirchUchida.adicCompletionToPlaceCompletion 𝔭 A hA z)
    (hW : (NK.NeukirchUchida.placeCompletionIntegers A).comap
        (NK.NeukirchUchida.adicCompletionToPlaceCompletion 𝔭 A hA) =
      IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K 𝔭)
    (y : K')
    (h : ∃ u : 𝔭.adicCompletion K,
      NK.NeukirchUchida.coInAdjoin (K := K) (K' := K') 𝔭 A y = algebraMap _ _ u) :
    y ∈ IntermediateField.fixedField (NK.Mine.decompositionGroupOf K K' A) := by
  obtain ⟨u, hu⟩ := h
  rw [IntermediateField.mem_fixedField_iff]
  intro σ hσ
  have h1 : (NK.Mine.adjoinLocalEquiv 𝔭 A hA halg hW ⟨σ, hσ⟩)
      (NK.NeukirchUchida.coInAdjoin (K := K) (K' := K') 𝔭 A y)
      = NK.NeukirchUchida.coInAdjoin (K := K) (K' := K') 𝔭 A (σ y) := by
    rw [NK.Mine.adjoinLocalEquiv_apply]
    exact NK.NeukirchUchida.decompositionToAdjoin_coInAdjoin (K := K) (K' := K') 𝔭 A hA halg
      ⟨σ, hσ⟩ y
  have h2 : (NK.Mine.adjoinLocalEquiv 𝔭 A hA halg hW ⟨σ, hσ⟩)
      (NK.NeukirchUchida.coInAdjoin (K := K) (K' := K') 𝔭 A y)
      = NK.NeukirchUchida.coInAdjoin (K := K) (K' := K') 𝔭 A y := by
    rw [hu]
    exact (NK.Mine.adjoinLocalEquiv 𝔭 A hA halg hW ⟨σ, hσ⟩).commutes u
  have h3 : NK.NeukirchUchida.coInAdjoin (K := K) (K' := K') 𝔭 A (σ y)
      = NK.NeukirchUchida.coInAdjoin (K := K) (K' := K') 𝔭 A y := h1 ▸ h2
  have h4 : NK.NeukirchUchida.placeCompletionCoe A (σ y)
      = NK.NeukirchUchida.placeCompletionCoe A y := by
    have h5 := congrArg
      (fun z : NK.NeukirchUchida.adjoinPlaceCompletion (K := K) (K' := K') 𝔭 A =>
        (z : NK.NeukirchUchida.placeCompletion A)) h3
    simpa only [NK.NeukirchUchida.coe_coInAdjoin] using h5
  exact RingHom.injective (NK.NeukirchUchida.placeCompletionCoe A) h4

/-- **The "bad case"**: if `α ∈ K'` has a `p`-th root in the completion `K_𝔭`, then `α` has a `p`-th
root in the decomposition field `Ω ^ D_A` — i.e. `α` is a `p`-th power of an element of
`IntermediateField.fixedField (decompositionGroupOf K K' A)`.

This is the injectivity of `KummerGroup p (Ω ^ D_A) → KummerGroup p K_𝔭` on the `K`-side, the input
that makes the injectivity route of `PING_injectivity_without_norm_localisation.md` work without the
delicate direction of the norm localisation. -/
theorem exists_pow_eq_of_pow_mem_range
    (p : ℕ) [Fact p.Prime]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K 𝔭)
    [Algebra (𝔭.adicCompletion K) (NK.NeukirchUchida.placeCompletion A)]
    (halg : ∀ z : 𝔭.adicCompletion K,
      algebraMap _ _ z = NK.NeukirchUchida.adicCompletionToPlaceCompletion 𝔭 A hA z)
    (hW : (NK.NeukirchUchida.placeCompletionIntegers A).comap
        (NK.NeukirchUchida.adicCompletionToPlaceCompletion 𝔭 A hA) =
      IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K 𝔭)
    (α : K') (u : 𝔭.adicCompletion K)
    (hu : (algebraMap (𝔭.adicCompletion K) (NK.NeukirchUchida.placeCompletion A) u) ^ p
      = NK.NeukirchUchida.placeCompletionCoe A α) :
    ∃ y ∈ IntermediateField.fixedField (NK.Mine.decompositionGroupOf K K' A), y ^ p = α := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  -- the image of `α` in the completion is algebraic over `K`
  have hαalg : IsAlgebraic K (NK.NeukirchUchida.placeCompletionCoe A α) :=
    IsAlgebraic.ringHom_of_comp_eq (RingHom.id K) (NK.NeukirchUchida.placeCompletionCoe A)
      ((Algebra.IsSeparable.isAlgebraic K K').isAlgebraic α) Function.injective_id (by
        ext x
        exact NK.NeukirchUchida.algebraMap_placeCompletionCoe A x)
  -- hence so is its `p`-th root `u` in the completion
  have hualg : IsAlgebraic K (algebraMap (𝔭.adicCompletion K)
      (NK.NeukirchUchida.placeCompletion A) u) := by
    refine IsAlgebraic.of_pow hp ?_
    rw [hu]
    exact hαalg
  -- the fundamental fact: the algebraic elements of the completion are the image of `K'`
  obtain ⟨y, hy⟩ :=
    (NK.NeukirchUchida.isAlgebraic_iff_exists_placeCompletionCoe A _).mp hualg
  -- `y` is fixed by the decomposition group
  have hyfix : y ∈ IntermediateField.fixedField (NK.Mine.decompositionGroupOf K K' A) := by
    refine mem_fixedField_of_coInAdjoin_mem_range 𝔭 A hA halg hW y ⟨u, ?_⟩
    apply Subtype.ext
    rw [NK.NeukirchUchida.coe_coInAdjoin]
    exact hy
  refine ⟨y, hyfix, ?_⟩
  -- and `y ^ p = α`
  exact RingHom.injective (NK.NeukirchUchida.placeCompletionCoe A)
    (by rw [map_pow, hy, ← hu])

end Work.SSGRoute.PT

namespace Work.SSGRoute.PT

open _root_.SSGRoute
open Work.SSGRoute

/-- **The "bad case" at the level group `mupLocalGroup k Ω K A`.**

If `α ∈ Ω` has a `p`-th root `u` in the completion `κ = mupCompletion (K := K) A hAK`, then `α` is
the `p`-th power of an element of the fixed field of the level group
`mupLocalGroup k Ω K A = decomp k A ⊓ K.fixingSubgroup`.

This is the form consumed by the injectivity route: an element of the Kummer group of `Ω ^ H` that
is a `p`-th power in the completion of `K` is already a `p`-th power in the decomposition field. -/
theorem exists_pow_eq_of_pow_mem_range_mupLocalGroup
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField ↥K] [IsSepClosure ↥K Ω]
    (A : ValuationSubring Ω) (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤)
    [inst : Algebra (ZDataMup.mupCompletion (K := K) A hAK)
      (NK.NeukirchUchida.placeCompletion A)]
    (halg : ∀ z : ZDataMup.mupCompletion (K := K) A hAK,
      algebraMap _ _ z = NK.NeukirchUchida.adicCompletionToPlaceCompletion
        (Submission.NeukirchUchida.primeOf A hAK) A
        (Submission.NeukirchUchida.primeOf_spec A hAK) z)
    (hW : (NK.NeukirchUchida.placeCompletionIntegers A).comap
        (NK.NeukirchUchida.adicCompletionToPlaceCompletion
          (Submission.NeukirchUchida.primeOf A hAK) A
          (Submission.NeukirchUchida.primeOf_spec A hAK)) =
      IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ↥K
        (Submission.NeukirchUchida.primeOf A hAK))
    (α : Ω) (u : ZDataMup.mupCompletion (K := K) A hAK)
    (hu : (algebraMap _ (NK.NeukirchUchida.placeCompletion A) u) ^ p
      = NK.NeukirchUchida.placeCompletionCoe A α) :
    ∃ y : Ω, y ∈ IntermediateField.fixedField (ZDataMup.mupLocalGroup k Ω K A) ∧ y ^ p = α := by
  obtain ⟨y, hyfix, hyp⟩ := exists_pow_eq_of_pow_mem_range (K := ↥K) (K' := Ω) p
    (Submission.NeukirchUchida.primeOf A hAK) A
    (Submission.NeukirchUchida.primeOf_spec A hAK) halg hW α u hu
  refine ⟨y, ?_, hyp⟩
  rw [IntermediateField.mem_fixedField_iff]
  intro σ hσ
  have hσK : σ ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp hσ).2
  have hσd : σ ∈ SSGRoute.decomp k A := (Subgroup.mem_inf.mp hσ).1
  have hτ : (IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσK⟩
      ∈ NK.Mine.decompositionGroupOf (K := ↥K) (K' := Ω) A :=
    (fixingSubgroupEquiv_mem_decomp k Ω K A σ hσK).mpr hσd
  have hτy : ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσK⟩ : Ω ≃ₐ[↥K] Ω) y = y :=
    (IntermediateField.mem_fixedField_iff
      (NK.Mine.decompositionGroupOf (K := ↥K) (K' := Ω) A) y).mp hyfix _ hτ
  have hfun : (((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσK⟩ : Ω ≃ₐ[↥K] Ω) : Ω → Ω)
      = ⇑σ := rfl
  rwa [hfun] at hτy

end Work.SSGRoute.PT
