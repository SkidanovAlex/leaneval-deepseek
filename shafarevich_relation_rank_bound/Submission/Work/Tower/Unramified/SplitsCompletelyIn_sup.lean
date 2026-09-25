import Mathlib
import Submission.Work.Tower.Unramified.Basic
import Submission.Work.Tower.Unramified.SplitsCompletelyIn_descent
import Submission.Work.Tower.Unramified.SplitsCompletelyIn_ncard
import Submission.Work.Tower.Unramified.SplitsCompletelyNF
import Submission.Work.Tower.Unramified.isUnramifiedExtensionForallPrimes_sup
import Submission.Work.Tower.Unramified.isFractionRing_of_span_eq_top
import Submission.Work.Tower.Unramified.span_eq_top_of_le
import Submission.Work.Tower.Unramified.splitsCompletelyIn_imp_NF
import Submission.Work.Tower.Unramified.splitsCompletelyIn_of_NF
import Submission.Work.Tower.Unramified.splitsCompletelyInNF_of_ramification_inertia
import Submission.Work.Tower.Unramified.compositum_splits_completely_alt
import Submission.Work.Tower.FrattiniLayer.splitsCompletelyIn_of_algHom

/-!
# Complete splitting ascends to composita

If a prime `𝔭` of `𝓞 F` splits completely in two finite extensions `E₁`, `E₂` of a number field
`F` (both lying in a common finite extension `L`), then it splits completely in the compositum
`E₁ ⊔ E₂`, and conversely.

* *Descent* (`E₁ ⊔ E₂` to `E₁`, `E₂`) is `Work.Tower.FrattiniLayer.splitsCompletelyIn_of_algHom`,
  applied to the two inclusions `E₁ ↪ E₁ ⊔ E₂` and `E₂ ↪ E₁ ⊔ E₂`.
* *Ascent* is the discrete case of the general theorem that complete splitting ascends to
  composita, `Work.Tower.Unramified.compositum_splits_completely_alt` (proved by passing to the
  normal closure `normalClosure F L (AlgebraicClosure F)` and computing `e · f` as the index of
  the stabilizer of a prime in the decomposition group).
* The degenerate case `𝔭 = ⊥`, where complete splitting is equivalent to the extension having
  degree one, is handled by `splitsCompletelyIn_bot_iff` and `finrank_sup_eq_one`.

## Main result

* `Work.Tower.Unramified.SplitsCompletelyIn_sup`.
-/

open NumberField
open scoped Classical nonZeroDivisors

namespace Work.Tower.Unramified

/-! ### Auxiliary lemmas -/

/-- A prime which splits completely is prime (a prime of `𝓞 L` lies over it). -/
theorem isPrime_of_splitsCompletelyIn {F L : Type*} [Field F] [Field L] [NumberField F]
    [NumberField L] [Algebra F L] [FiniteDimensional F L]
    {𝔭 : Ideal (NumberField.RingOfIntegers F)}
    (h : Work.Tower.SplitsCompletelyIn F L 𝔭) : 𝔭.IsPrime := by
  obtain ⟨𝔔, hprime, hlies, -, -⟩ := h
  haveI : (𝔔 ⟨0, Module.finrank_pos⟩).IsPrime := hprime _
  haveI : (𝔔 ⟨0, Module.finrank_pos⟩).LiesOver 𝔭 := hlies _
  exact Ideal.isPrime_of_liesOver (𝔔 ⟨0, Module.finrank_pos⟩) 𝔭

/-- An intermediate field that is one-dimensional over the base is the bottom field. -/
theorem eq_bot_of_finrank_eq_one {F L : Type*} [Field F] [Field L] [Algebra F L]
    (E : IntermediateField F L) [FiniteDimensional F E]
    (h : Module.finrank F ↥E = 1) : E = ⊥ := by
  have hinj : Function.Injective (Algebra.ofId F ↥E) := (Algebra.ofId F ↥E).injective
  have hsurj : Function.Surjective (Algebra.ofId F ↥E) := by
    have hrange : LinearMap.range (Algebra.ofId F ↥E).toLinearMap = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by
        rw [LinearMap.finrank_range_of_inj hinj, h, Module.finrank_self])
    exact LinearMap.range_eq_top.mp hrange
  refine le_antisymm (fun x hx => ?_) bot_le
  obtain ⟨c, hc⟩ := hsurj ⟨x, hx⟩
  rw [IntermediateField.mem_bot]
  exact ⟨c, by simpa using congrArg Subtype.val hc⟩

/-- The degree of a compositum is one if and only if both factors have degree one. -/
theorem finrank_sup_eq_one {F L : Type*} [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] {E₁ E₂ : IntermediateField F L} [FiniteDimensional F E₁]
    [FiniteDimensional F E₂] :
    Module.finrank F ↥(E₁ ⊔ E₂) = 1 ↔
      Module.finrank F ↥E₁ = 1 ∧ Module.finrank F ↥E₂ = 1 := by
  have key : ∀ (E E' : IntermediateField F L) [FiniteDimensional F E] (h : E ≤ E'),
      Module.finrank F ↥E ≤ Module.finrank F ↥E' := by
    intro E E' _ h
    refine LinearMap.finrank_le_finrank_of_injective
      (f := { toFun := fun x => (⟨(x : L), h x.2⟩ : ↥E')
              map_add' := fun a b => rfl
              map_smul' := fun c a => rfl }) ?_
    intro a b hab
    exact Subtype.ext (congrArg (fun z : ↥E' => (z : L)) hab)
  constructor
  · intro h
    exact ⟨le_antisymm (h ▸ key E₁ (E₁ ⊔ E₂) le_sup_left) Module.finrank_pos,
      le_antisymm (h ▸ key E₂ (E₁ ⊔ E₂) le_sup_right) Module.finrank_pos⟩
  · rintro ⟨h₁, h₂⟩
    have hE1 : E₁ = ⊥ := eq_bot_of_finrank_eq_one E₁ h₁
    have hE2 : E₂ = ⊥ := eq_bot_of_finrank_eq_one E₂ h₂
    subst hE1
    subst hE2
    simp

/-- Complete splitting at the zero ideal is equivalent to being one-dimensional. -/
theorem splitsCompletelyIn_bot_iff {F L : Type*} [Field F] [Field L] [NumberField F]
    [NumberField L] [Algebra F L] [FiniteDimensional F L] :
    Work.Tower.SplitsCompletelyIn F L ⊥ ↔ Module.finrank F L = 1 := by
  constructor
  · intro h
    have h1 : (⊥ : Ideal (𝓞 F)).primesOver (𝓞 L) = {⊥} := Ideal.primesOver_bot (𝓞 F) (𝓞 L)
    have h2 := SplitsCompletelyIn_ncard h
    rw [h1, Set.ncard_singleton] at h2
    exact h2.symm
  · intro h
    have hinjalg : Function.Injective (Algebra.ofId F L) :=
      RingHom.injective (Algebra.ofId F L).toRingHom
    have hrange : LinearMap.range (Algebra.ofId F L).toLinearMap = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by
        rw [LinearMap.finrank_range_of_inj hinjalg, Module.finrank_self, h])
    have hsurjalg : Function.Surjective (Algebra.ofId F L) :=
      LinearMap.range_eq_top.mp hrange
    let e : F ≃ₐ[F] L := AlgEquiv.ofBijective (Algebra.ofId F L) ⟨hinjalg, hsurjalg⟩
    have eR : (𝓞 F) ≃+* (𝓞 L) := RingOfIntegers.mapRingEquiv e.toRingEquiv
    refine ⟨fun _ => (⊥ : Ideal (𝓞 L)), fun i => Ideal.isPrime_bot, fun i => ⟨by rw [Ideal.under_bot]⟩,
      ?_, fun i => ?_⟩
    · intro i j _
      exact Fin.ext (by have := i.isLt; have := j.isLt; omega)
    · exact ⟨Ideal.quotientEquiv (⊥ : Ideal (𝓞 L)) (⊥ : Ideal (𝓞 F)) eR.symm
        (Ideal.map_bot (f := (eR.symm : 𝓞 L →+* 𝓞 F))).symm⟩

/-- There is `x ∈ S`, not in any prime over `𝔭` and nonzero, such that `S_x` is formally
unramified over `R`. -/
theorem exists_formallyUnramified_away {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain R] [IsDedekindDomain R] [IsDomain S] [Algebra.IsIntegral R S]
    [Algebra.EssFiniteType R S] [FaithfulSMul R S] {𝔭 : Ideal R} [h𝔭 : 𝔭.IsPrime] (h𝔭0 : 𝔭 ≠ ⊥)
    (h : Algebra.IsUnramifiedIn S 𝔭) :
    ∃ x : S, (∀ Q ∈ 𝔭.primesOver S, x ∉ Q) ∧ x ≠ 0 ∧
      Algebra.FormallyUnramified R (Localization.Away x) := by
  have hZ : IsClosed ((Algebra.unramifiedLocus R S)ᶜ) :=
    (Algebra.isOpen_unramifiedLocus (R := R) (A := S)).isClosed_compl
  obtain ⟨I, hI⟩ : ∃ I : Ideal S, (Algebra.unramifiedLocus R S)ᶜ = PrimeSpectrum.zeroLocus I :=
    ⟨PrimeSpectrum.vanishingIdeal ((Algebra.unramifiedLocus R S)ᶜ), by
      rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hZ.closure_eq]⟩
  have hfiber : PrimeSpectrum.zeroLocus (𝔭.map (algebraMap R S)) ⊆
      Algebra.unramifiedLocus R S := by
    intro P hP
    rw [PrimeSpectrum.mem_zeroLocus] at hP
    have hPprime : P.asIdeal.IsPrime := P.isPrime
    have hle : 𝔭 ≤ P.asIdeal.under R := by
      rw [Ideal.under_def]
      exact Ideal.map_le_iff_le_comap.mp hP
    have hunderne : P.asIdeal.under R ≠ ⊤ := by
      intro htop
      have h1 : (1 : S) ∈ P.asIdeal := by
        have : (1 : R) ∈ P.asIdeal.under R := by rw [htop]; exact Submodule.mem_top
        rwa [Ideal.under_def, Ideal.mem_comap, map_one] at this
      exact hPprime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    have h𝔭max : 𝔭.IsMaximal := h𝔭.isMaximal h𝔭0
    exact h P.asIdeal hPprime (Ideal.LiesOver.mk (h𝔭max.eq_of_le hunderne hle))
  have hempty : PrimeSpectrum.zeroLocus ((I ⊔ 𝔭.map (algebraMap R S)) : Ideal S) =
      (∅ : Set (PrimeSpectrum S)) := by
    refine Set.Subset.antisymm ?_ (Set.empty_subset _)
    intro P hP
    rw [PrimeSpectrum.mem_zeroLocus] at hP
    have h1 : P ∈ PrimeSpectrum.zeroLocus (I : Set S) := by
      rw [PrimeSpectrum.mem_zeroLocus]
      exact fun a ha => hP (Ideal.mem_sup_left ha)
    have h2 : P ∈ PrimeSpectrum.zeroLocus ((𝔭.map (algebraMap R S) : Ideal S) : Set S) := by
      rw [PrimeSpectrum.mem_zeroLocus]
      exact fun a ha => hP (Ideal.mem_sup_right ha)
    rw [← hI] at h1
    exact h1 (hfiber h2)
  have htop : I ⊔ 𝔭.map (algebraMap R S) = ⊤ := by
    by_contra hne
    obtain ⟨m, hmmax, hm⟩ := Ideal.exists_le_maximal _ hne
    have hmz : (⟨m, hmmax.isPrime⟩ : PrimeSpectrum S) ∈
        PrimeSpectrum.zeroLocus ((I ⊔ 𝔭.map (algebraMap R S)) : Ideal S) := by
      rw [PrimeSpectrum.mem_zeroLocus]
      exact fun a ha => hm ha
    rw [hempty] at hmz
    exact hmz
  obtain ⟨x, hxI, y, hy, hxy⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp htop)
  have hxQ : ∀ Q ∈ 𝔭.primesOver S, x ∉ Q := by
    rintro Q ⟨hQp, hQl⟩ hxQ
    have h𝔭SQ : 𝔭.map (algebraMap R S) ≤ Q := by
      refine Ideal.map_le_iff_le_comap.mpr ?_
      exact hQl.over.le
    have h1 : (1 : S) ∈ Q := by
      rw [← hxy]
      exact add_mem hxQ (h𝔭SQ hy)
    exact hQp.ne_top ((Ideal.eq_top_iff_one Q).mpr h1)
  have hxne : x ≠ 0 := by
    obtain ⟨Q, hQ⟩ := (inferInstance : Nonempty (𝔭.primesOver S))
    intro hx0
    exact hxQ Q hQ (hx0 ▸ Submodule.zero_mem Q)
  refine ⟨x, hxQ, hxne, ?_⟩
  refine Algebra.basicOpen_subset_unramifiedLocus_iff.mp ?_
  intro P hP
  have hxP : x ∉ P.asIdeal := (PrimeSpectrum.mem_basicOpen x P).mp hP
  have hnot : P ∉ PrimeSpectrum.zeroLocus (I : Set S) := fun hz => hxP (hz hxI)
  rw [← hI] at hnot
  simpa using hnot

/-! ### The main theorem -/

theorem SplitsCompletelyIn_sup {F L : Type*} [Field F] [Field L] [NumberField F] [NumberField L]
    [Algebra F L] [FiniteDimensional F L] {E₁ E₂ : IntermediateField F L}
    [FiniteDimensional F E₁] [FiniteDimensional F E₂]
    {𝔭 : Ideal (NumberField.RingOfIntegers F)} :
    Work.Tower.SplitsCompletelyIn F ↥(E₁ ⊔ E₂) 𝔭 ↔
      Work.Tower.SplitsCompletelyIn F ↥E₁ 𝔭 ∧ Work.Tower.SplitsCompletelyIn F ↥E₂ 𝔭 := by
  haveI : NumberField ↥(E₁ ⊔ E₂) := NumberField.of_module_finite F ↥(E₁ ⊔ E₂)
  constructor
  · intro h
    exact ⟨FrattiniLayer.splitsCompletelyIn_of_algHom 𝔭
        (IntermediateField.inclusion (le_sup_left : E₁ ≤ E₁ ⊔ E₂)) h,
      FrattiniLayer.splitsCompletelyIn_of_algHom 𝔭
        (IntermediateField.inclusion (le_sup_right : E₂ ≤ E₁ ⊔ E₂)) h⟩
  · rintro ⟨h₁, h₂⟩
    exact compositum_splits_completely_alt h₁ h₂

end Work.Tower.Unramified
