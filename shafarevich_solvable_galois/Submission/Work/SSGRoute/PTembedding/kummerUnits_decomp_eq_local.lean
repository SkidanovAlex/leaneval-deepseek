import Mathlib
import Submission.Work.SSGRoute.PTembedding.kbdDefs
import Submission.Work.SSGRoute.PTembedding.rootsOfUnity_addEquiv_adjoinLocalEquiv
import Submission.Work.SSGRoute.PTembedding.h1loc_mup_card_kummer
import Submission.Work.SSGRoute.PTembedding.kummer_decomp_main
import Submission.Work.SSGRoute.PTembedding.kummer_decomp
import Submission.Work.SSGRoute.PTembedding.KummerMuDefs
import Submission.Work.SSGRoute.adjoin_primitiveRoot_isGalois_coprime
import Submission.Commons.NumberTheory.NumberField.charZero_adicCompletion
import Submission.NK.Mine.AdjoinLocalGalois
import Submission.NK.Mine.exists_isHomeomorph_mulEquiv_sepClosure_of_decompositionGroup_map

/-!
# The local Kummer group of the completion is the Kummer group of the decomposition field

This file proves `kummerUnits_decomp_eq_local`: at a finite place `A` of `Ω` over the number
field `k`, the `p`-Kummer group `𝔨ˣ ⧸ (𝔨ˣ)^p` of the completion `𝔨 = k_𝔭` has the same
cardinality as the `p`-Kummer group `Fˣ ⧸ (Fˣ)^p` of the decomposition field
`F = Ω^{D_A}`.

The route is Kummer theory on both sides plus the identification of Galois groups:

* `𝔨ˣ ⧸ (𝔨ˣ)^p ≅ H¹(Gal(𝔨̄/𝔨), μ_p)` (`MupCard.kummer_unitsQuotient_aux`);
* `H¹(Gal(AlgebraicClosure 𝔨/𝔨), μ_p) ≅ H¹(Gal(M/𝔨), μ_p)` where `M = 𝔨·Ω` is the separable
  closure of `𝔨` inside the place completion of `Ω` at `A` (`rootsOfUnity_autCongr_equiv`);
* `H¹(Gal(M/𝔨), μ_p) ≅ H¹(D_A, μ_p)` via the explicit identification
  `NK.Mine.adjoinLocalEquiv : D_A ≃* Gal(M/𝔨)`, whose compatibility with `μ_p` reduces to
  `NK.NeukirchUchida.decompositionToAdjoin_coInAdjoin`;
* `H¹(D_A, μ_p) ≅ Fˣ ⧸ (Fˣ)^p` (`MupCard.card_H1_decomp_muAdd_eq_KummerGroup`).
-/

open scoped Classical
open Work.SSGRoute

namespace Work.SSGRoute.PTembedding

noncomputable section

set_option linter.style.haveILetI false

namespace KummerUnitsDecomp

variable (k : Type) [Field k] [NumberField k] (Ω : Type) [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]

/-- The prime of `k` below a finite place `A` of `Ω`. -/
abbrev primeUnder (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k) :=
  Submission.NeukirchUchida.primeOf A hA

/-- `M = 𝔨·Ω ⊆ ` the place completion of `Ω` at `A`: a separable closure of `𝔨`. -/
abbrev adjoinField (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    [Algebra (Work.SSGRoute.PTembedding.localFieldOf k A hA)
      (NK.NeukirchUchida.placeCompletion A)] : Type :=
  ↥(NK.NeukirchUchida.adjoinPlaceCompletion (primeUnder k Ω A hA) A)

end KummerUnitsDecomp

/-! ## The existence of a primitive root of unity whose field is finite Galois over `k` -/

theorem exists_galois_adjoin_primitiveRoot (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] :
    ∃ (K : IntermediateField k Ω) (ζ : Ω), IsPrimitiveRoot ζ p ∧ ζ ∈ K ∧
      FiniteDimensional k K ∧ IsGalois k K := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (RingHom.injective (algebraMap k Ω))
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  haveI : IsSepClosed Ω := inferInstance
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω p
  refine ⟨IntermediateField.adjoin k ({ζ} : Set Ω), ζ, hζ,
    IntermediateField.subset_adjoin k _ (Set.mem_singleton ζ), ?_, ?_⟩
  · exact (Work.SSGRoute.adjoin_primitiveRoot_isGalois_coprime p k Ω ζ hζ).2.1
  · exact (Work.SSGRoute.adjoin_primitiveRoot_isGalois_coprime p k Ω ζ hζ).1

/-! ## Assembly -/

/-- `Nat.card` is insensitive to the `Additive` type tag. -/
theorem natCard_additive (X : Type*) : Nat.card (Additive X) = Nat.card X :=
  Nat.card_congr (Additive.toMul : Additive X ≃ X)

theorem kummerUnits_decomp_eq_local
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    Nat.card ((Work.SSGRoute.PTembedding.localFieldOf k A hA)ˣ ⧸
        ((powMonoidHom p : (Work.SSGRoute.PTembedding.localFieldOf k A hA)ˣ →*
          (Work.SSGRoute.PTembedding.localFieldOf k A hA)ˣ).range))
      = Nat.card (Work.SSGRoute.mup.KummerGroup p (Work.SSGRoute.mup.decompField k Ω A)) := by
  classical
  -- ## the ambient algebra structure `𝔨 → placeCompletion A` and the field `M = 𝔨·Ω`
  letI : Algebra (Work.SSGRoute.PTembedding.localFieldOf k A hA)
      (NK.NeukirchUchida.placeCompletion A) :=
    (NK.NeukirchUchida.adicCompletionToPlaceCompletion (KummerUnitsDecomp.primeUnder k Ω A hA) A
      (Submission.NeukirchUchida.primeOf_spec A hA)).toAlgebra
  have halg : ∀ z : Work.SSGRoute.PTembedding.localFieldOf k A hA,
      (algebraMap (Work.SSGRoute.PTembedding.localFieldOf k A hA)
        (NK.NeukirchUchida.placeCompletion A)) z =
        NK.NeukirchUchida.adicCompletionToPlaceCompletion
          (KummerUnitsDecomp.primeUnder k Ω A hA) A
          (Submission.NeukirchUchida.primeOf_spec A hA) z := fun z => rfl
  have hW : (NK.NeukirchUchida.placeCompletionIntegers A).comap
        (NK.NeukirchUchida.adicCompletionToPlaceCompletion
          (KummerUnitsDecomp.primeUnder k Ω A hA) A
          (Submission.NeukirchUchida.primeOf_spec A hA)) =
      IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers k
        (KummerUnitsDecomp.primeUnder k Ω A hA) :=
    NK.NeukirchUchida.comap_adicCompletionToPlaceCompletion_eq_adicCompletionIntegers
      (KummerUnitsDecomp.primeUnder k Ω A hA) A (Submission.NeukirchUchida.primeOf_spec A hA)
  haveI hCharZero : CharZero (Work.SSGRoute.PTembedding.localFieldOf k A hA) :=
    Commons.NumberTheory.NumberField.charZero_adicCompletion
      (KummerUnitsDecomp.primeUnder k Ω A hA)
  haveI hSep : IsSepClosure (Work.SSGRoute.PTembedding.localFieldOf k A hA)
      (KummerUnitsDecomp.adjoinField k Ω A hA) :=
    NK.Mine.isSepClosure_adjoinPlaceCompletion (KummerUnitsDecomp.primeUnder k Ω A hA) A
      (Submission.NeukirchUchida.primeOf_spec A hA) halg
  haveI hGalM : IsGalois (Work.SSGRoute.PTembedding.localFieldOf k A hA)
      (KummerUnitsDecomp.adjoinField k Ω A hA) := hSep.isGalois
  haveI hGalCl : IsGalois (Work.SSGRoute.PTembedding.localFieldOf k A hA)
      (AlgebraicClosure (Work.SSGRoute.PTembedding.localFieldOf k A hA)) :=
    IsAlgClosure.isGalois _ _
  -- ## a primitive `p`-th root of unity and its (finite Galois) field over `k`
  obtain ⟨K, ζ, hζ, hζK, hfin, hgal⟩ := exists_galois_adjoin_primitiveRoot p k Ω
  haveI := hfin
  haveI := hgal
  -- ## Kummer theory over the completion
  obtain ⟨e1⟩ := kummer_unitsQuotient_aux (Work.SSGRoute.PTembedding.localFieldOf k A hA) p
  -- ## the two closures of `𝔨` are isomorphic
  let e2 : AlgebraicClosure (Work.SSGRoute.PTembedding.localFieldOf k A hA) ≃ₐ[
      Work.SSGRoute.PTembedding.localFieldOf k A hA]
      (KummerUnitsDecomp.adjoinField k Ω A hA) :=
    IsSepClosure.equiv (Work.SSGRoute.PTembedding.localFieldOf k A hA)
      (AlgebraicClosure (Work.SSGRoute.PTembedding.localFieldOf k A hA))
      (KummerUnitsDecomp.adjoinField k Ω A hA)
  obtain ⟨Ψ2, hΨ2⟩ := rootsOfUnity_autCongr_equiv
    (Work.SSGRoute.PTembedding.localFieldOf k A hA) e2 p
  have htr2 := PT.h1Transfer (Φ := AlgEquiv.autCongr e2)
    (NK.Mine.isHomeomorph_autCongr e2) Ψ2 hΨ2
  -- ## the explicit identification `D_A ≃* Gal(M/𝔨)` is compatible with `μ_p`
  obtain ⟨Ψ3, hΨ3⟩ := rootsOfUnity_addEquiv_adjoinLocalEquiv p k Ω A hA halg hW
    K ζ hζ hζK
  let Φ3 : Gal(KummerUnitsDecomp.adjoinField k Ω A hA /
      Work.SSGRoute.PTembedding.localFieldOf k A hA) ≃* ↥(SSGRoute.decomp k A) :=
    (NK.Mine.adjoinLocalEquiv (KummerUnitsDecomp.primeUnder k Ω A hA) A
      (Submission.NeukirchUchida.primeOf_spec A hA) halg hW).symm
  have hΦ3 : IsHomeomorph (Φ3 : Gal(KummerUnitsDecomp.adjoinField k Ω A hA /
      Work.SSGRoute.PTembedding.localFieldOf k A hA) → ↥(SSGRoute.decomp k A)) :=
    NK.Mine.isHomeomorph_symm _
      (NK.Mine.isHomeomorph_adjoinLocalEquiv (KummerUnitsDecomp.primeUnder k Ω A hA) A
        (Submission.NeukirchUchida.primeOf_spec A hA) halg hW)
  have hadj : ∀ g' : Gal(KummerUnitsDecomp.adjoinField k Ω A hA /
      Work.SSGRoute.PTembedding.localFieldOf k A hA),
      NK.Mine.adjoinLocalEquiv (KummerUnitsDecomp.primeUnder k Ω A hA) A
        (Submission.NeukirchUchida.primeOf_spec A hA) halg hW (Φ3 g') = g' := by
    intro g'
    change Φ3.symm (Φ3 g') = g'
    exact MulEquiv.symm_apply_apply Φ3 g'
  have hΨ3' : ∀ (g' : Gal(KummerUnitsDecomp.adjoinField k Ω A hA /
        Work.SSGRoute.PTembedding.localFieldOf k A hA))
      (m' : Additive (rootsOfUnity p (KummerUnitsDecomp.adjoinField k Ω A hA))),
      Ψ3 (g' • m') = Φ3 g' • Ψ3 m' := by
    intro g' m'
    have h := hΨ3 (Φ3 g') m'
    rwa [hadj g'] at h
  have htr3 := PT.h1Transfer (Φ := Φ3) hΦ3 Ψ3 hΨ3'
  -- ## Kummer theory over the decomposition field
  have h4 := MupCard.card_H1_decomp_muAdd_eq_KummerGroup (p := p) (k := k) (Ω := Ω) K ζ hζ hζK A hA
  -- ## assembly
  calc Nat.card ((Work.SSGRoute.PTembedding.localFieldOf k A hA)ˣ ⧸
        ((powMonoidHom p : (Work.SSGRoute.PTembedding.localFieldOf k A hA)ˣ →*
          (Work.SSGRoute.PTembedding.localFieldOf k A hA)ˣ).range))
      = Nat.card (Additive ((Work.SSGRoute.PTembedding.localFieldOf k A hA)ˣ ⧸
          ((powMonoidHom p : (Work.SSGRoute.PTembedding.localFieldOf k A hA)ˣ →*
            (Work.SSGRoute.PTembedding.localFieldOf k A hA)ˣ).range))) :=
        (natCard_additive _).symm
    _ = Nat.card (Work.AbsoluteKummer.H1 (Work.AbsoluteKummer.G
          (Work.SSGRoute.PTembedding.localFieldOf k A hA))
          (Additive (rootsOfUnity p (AlgebraicClosure
            (Work.SSGRoute.PTembedding.localFieldOf k A hA))))) :=
        (Nat.card_congr e1.toEquiv).symm
    _ = Nat.card (Work.AbsoluteKummer.H1 (Gal(KummerUnitsDecomp.adjoinField k Ω A hA /
          Work.SSGRoute.PTembedding.localFieldOf k A hA))
          (Additive (rootsOfUnity p (KummerUnitsDecomp.adjoinField k Ω A hA)))) :=
        Nat.card_congr htr2.toEquiv
    _ = Nat.card (Work.AbsoluteKummer.H1 ↥(SSGRoute.decomp k A) (MupCard.MuAdd p K)) :=
        Nat.card_congr htr3.toEquiv
    _ = Nat.card (Work.SSGRoute.mup.KummerGroup p (Work.SSGRoute.mup.decompField k Ω A)) := h4

end

end Work.SSGRoute.PTembedding
