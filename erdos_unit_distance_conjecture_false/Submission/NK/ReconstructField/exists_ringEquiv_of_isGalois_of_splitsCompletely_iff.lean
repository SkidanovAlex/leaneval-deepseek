import Mathlib
import Submission.NK.ReconstructField.Bauer

namespace NK.ReconstructField

open IsDedekindDomain

/-- **Invariance of `SplitsCompletely` under a `ℚ`-algebra isomorphism**: the number of primes of
`𝓞 L` above a prime `p` of `𝓞 k` equals the number of primes of `𝓞 K` above `p` when
`K ≃ₐ[k] L`, and the degrees `[K : k]`, `[L : k]` agree. -/
theorem splitsCompletely_iff_of_algEquiv {k K L : Type*} [Field k] [NumberField k] [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra k K] [Algebra k L] (e : K ≃ₐ[k] L)
    (p : NK.Chebotarev.PrimeIdeal k) :
    SplitsCompletely k K p ↔ SplitsCompletely k L p := by
  have hncard : (p.asIdeal.primesOver (NumberField.RingOfIntegers K)).ncard =
      (p.asIdeal.primesOver (NumberField.RingOfIntegers L)).ncard := by
    let σ : NumberField.RingOfIntegers K ≃ₐ[NumberField.RingOfIntegers k]
        NumberField.RingOfIntegers L := NumberField.RingOfIntegers.mapAlgEquiv e
    have hσ : Function.Surjective
        (σ : NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers L) :=
      fun y => ⟨σ.symm y, by simp⟩
    have hσi : Function.Injective
        (σ : NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers L) :=
      fun x y h => by simpa using h
    have hσs : Function.Surjective
        (σ.symm : NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers K) :=
      fun y => ⟨σ y, by simp⟩
    have hσsi : Function.Injective
        (σ.symm : NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers K) :=
      fun x y h => by simpa using h
    refine Set.ncard_congr
      (fun P _ => Ideal.map (σ : NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers L) P)
      ?_ ?_ ?_
    · intro P hP
      have hprime : P.IsPrime := hP.1
      have hlies : P.LiesOver p.asIdeal := hP.2
      exact ⟨Ideal.map_isPrime_of_surjective hσ (by
        intro x hx
        rw [RingHom.mem_ker] at hx
        rw [show x = 0 by apply hσi; rw [hx, map_zero]]
        exact Submodule.zero_mem P), Ideal.map_equiv_liesOver P p.asIdeal σ⟩
    · intro P₁ P₂ h₁ h₂ heq
      rw [← Ideal.comap_map_of_bijective
            (σ : NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers L) (⟨hσi, hσ⟩)
            (I := P₁),
          ← Ideal.comap_map_of_bijective
            (σ : NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers L) (⟨hσi, hσ⟩)
            (I := P₂)]
      exact congrArg (Ideal.comap
        (σ : NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers L)) heq
    · intro Q hQ
      refine ⟨Ideal.map (σ.symm : NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers K) Q,
        ?_, ?_⟩
      · have hprime : Q.IsPrime := hQ.1
        have hlies : Q.LiesOver p.asIdeal := hQ.2
        exact ⟨Ideal.map_isPrime_of_surjective hσs (by
          intro x hx
          rw [RingHom.mem_ker] at hx
          rw [show x = 0 by apply hσsi; rw [hx, map_zero]]
          exact Submodule.zero_mem Q), Ideal.map_equiv_liesOver Q p.asIdeal σ.symm⟩
      · rw [Ideal.map_map]
        convert Ideal.map_id Q using 2
        ext x
        simp
  have hfin : Module.finrank k K = Module.finrank k L := e.toLinearEquiv.finrank_eq
  unfold SplitsCompletely
  rw [hncard, hfin]

/-- **Bauer's theorem, abstract form.**  Two number fields which are Galois over `ℚ` and have the
same completely split primes are isomorphic.

Proof route: choose `ℚ`-algebra embeddings of `K₁` and `K₂` into the algebraic closure
`AlgebraicClosure ℚ` (a number field is a finite separable extension of `ℚ`, and the algebraic
closure is algebraically closed); the images are finite Galois `IntermediateField`s of
`AlgebraicClosure ℚ` over `ℚ` with the same completely split primes (the split primes of a subfield
are transported across a `ℚ`-algebra isomorphism, by the induced bijection of the rings of integers
and of the primes over `p`), so `NK.ReconstructField.eq_of_splitsCompletely_iff` (Bauer, from the
unconditional density `1/[L:ℚ]` of the completely split primes) makes the images equal; the
embeddings then compose to a ring isomorphism `K₁ ≃+* K₂`.

This is the "abstract-isomorphism version" of Bauer's theorem, i.e. the Galois-over-`ℚ` case of the
weak Neukirch–Uchida statement; it is the reason why the reconstruction input
`NK.ReconstructField.ReconstructionInput` reduces to the place realization alone in that case. -/
theorem exists_ringEquiv_of_isGalois_of_splitsCompletely_iff
    {K₁ K₂ : Type*} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
    [IsGalois ℚ K₁] [IsGalois ℚ K₂]
    (h : ∀ p : NK.Chebotarev.PrimeIdeal ℚ,
      NK.ReconstructField.SplitsCompletely ℚ K₁ p ↔
        NK.ReconstructField.SplitsCompletely ℚ K₂ p) :
    Nonempty (K₁ ≃+* K₂) := by
  -- fix the `ℚ`-algebra structure on the algebraic closure to be the one induced by `ℚ ⊆ ℚ̄`
  letI : Algebra ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instAlgebra (k := ℚ) (R := ℚ)
  haveI hgal : IsGalois ℚ (AlgebraicClosure ℚ) := inferInstance
  -- `ℚ`-algebra embeddings of the two number fields into the algebraic closure
  let φ₁ : K₁ →ₐ[ℚ] AlgebraicClosure ℚ :=
    IsAlgClosed.lift (R := ℚ) (S := K₁) (M := AlgebraicClosure ℚ)
  let φ₂ : K₂ →ₐ[ℚ] AlgebraicClosure ℚ :=
    IsAlgClosed.lift (R := ℚ) (S := K₂) (M := AlgebraicClosure ℚ)
  let E₁ : IntermediateField ℚ (AlgebraicClosure ℚ) := φ₁.fieldRange
  let E₂ : IntermediateField ℚ (AlgebraicClosure ℚ) := φ₂.fieldRange
  let e₁ : K₁ ≃ₐ[ℚ] ↥E₁ := AlgEquiv.ofInjectiveField φ₁
  let e₂ : K₂ ≃ₐ[ℚ] ↥E₂ := AlgEquiv.ofInjectiveField φ₂
  have hgal₁ := IsGalois.of_algEquiv e₁
  have hgal₂ := IsGalois.of_algEquiv e₂
  have hfd₁ : FiniteDimensional ℚ ↥E₁ := e₁.toLinearEquiv.finiteDimensional
  have hfd₂ : FiniteDimensional ℚ ↥E₂ := e₂.toLinearEquiv.finiteDimensional
  have hnf₁ := Commons.NumberTheory.NumberField.numberField_of_intermediateField E₁
  have hnf₂ := Commons.NumberTheory.NumberField.numberField_of_intermediateField E₂
  have hnorm₁ := hgal₁.to_normal
  have hnorm₂ := hgal₂.to_normal
  haveI := hfd₁; haveI := hgal₁; haveI := hnf₁
  haveI := hfd₂; haveI := hgal₂; haveI := hnf₂
  -- the two images have the same completely split primes
  have hE : ∀ p : NK.Chebotarev.PrimeIdeal ℚ,
      SplitsCompletely ℚ ↥E₁ p ↔ SplitsCompletely ℚ ↥E₂ p := by
    intro p
    exact ((splitsCompletely_iff_of_algEquiv e₁ p).symm).trans
      ((h p).trans (splitsCompletely_iff_of_algEquiv e₂ p))
  -- Bauer: equal completely split prime sets force equal images in `ℚ̄`
  have hEE : E₁ = E₂ :=
    @eq_of_splitsCompletely_iff ℚ (AlgebraicClosure ℚ)
      _ _ _ _ hgal E₁ E₂ hfd₁ hnorm₁ hnf₁ hfd₂ hnorm₂ hnf₂ hE
  exact ⟨((e₁.trans (IntermediateField.equivOfEq hEE)).trans e₂.symm).toRingEquiv⟩

end NK.ReconstructField
