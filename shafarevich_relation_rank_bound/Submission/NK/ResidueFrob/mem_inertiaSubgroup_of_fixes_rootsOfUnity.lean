import Mathlib
import Submission.NK.ResidueFrob.Setup

namespace NK.ResidueFrob

open scoped Pointwise Classical
open IntermediateField

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-- **The explicit identification fixes the prime-to-`P` roots of unity when `u` does.**

This is the technical heart of `mem_inertiaSubgroup_of_fixes_rootsOfUnity`: for an element `u` of
the decomposition group of the place `A` of `K'` which fixes every root of unity of `K'` of order
prime to `P`, the image of `u` under the *explicit* identification
`adjoinLocalIso = (σ ↦ σ̂|_M) ⋊ (M ≃ₐ[K_𝔭] κ̄)` lies in the local inertia subgroup, i.e. it fixes
every root of unity of the local closure `κ̄` of order prime to `P`.

Indeed `adjoinLocalIso ⟨u, hu⟩` acts as `φ ∘ σ̂|_M ∘ φ⁻¹` on `κ̄`; a root of unity `w` of order
prime to `P` in `M = K_𝔭·K'` is algebraic over `K`, so lies in the image of `K'`
(`isAlgebraic_iff_exists_placeCompletionCoe`), say `w = coInAdjoin y`; then `y` is itself a
primitive `n`-th root of unity with `¬ P ∣ n`, so `u y = y` and
`decompositionToAdjoin_coInAdjoin` gives `σ̂|_M w = w`. -/
theorem mem_inertiaSubgroup_adjoinLocalIso_of_fixes_rootsOfUnity
    {K : Type*} [Field K] [NumberField K]
    {K' : Type*} [Field K'] [Algebra K K'] [IsSepClosure K K']
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K 𝔭)
    [Algebra (IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔭)
      (NK.NeukirchUchida.placeCompletion A)]
    (halg : ∀ z : IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔭,
      algebraMap _ _ z = NK.NeukirchUchida.adicCompletionToPlaceCompletion 𝔭 A hA z)
    (hW : (NK.NeukirchUchida.placeCompletionIntegers A).comap
        (NK.NeukirchUchida.adicCompletionToPlaceCompletion 𝔭 A hA) =
      IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K 𝔭)
    (P : ℕ) {u : Gal(K'/K)} (hu : u ∈ NK.Mine.decompositionGroupOf K K' A)
    (hfix : ∀ ζ : K', (∃ n : ℕ, ¬ P ∣ n ∧ IsPrimitiveRoot ζ n) → u ζ = ζ) :
    adjoinLocalIso 𝔭 A hA halg hW ⟨u, hu⟩ ∈
      NK.LocalAnabelian.inertiaSubgroup
        (κ := IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔭)
        (K' := SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔭)) P := by
  rw [NK.LocalAnabelian.mem_inertiaSubgroup_iff]
  intro n hn ζ hζ
  have hval : (adjoinLocalIso 𝔭 A hA halg hW ⟨u, hu⟩) ζ
      = adjoinSepEquiv 𝔭 A hA halg
          (NK.NeukirchUchida.decompositionToAdjoin 𝔭 A hA halg ⟨u, hu⟩
            ((adjoinSepEquiv 𝔭 A hA halg).symm ζ)) := by
    simp only [adjoinLocalIso, MulEquiv.trans_apply, AlgEquiv.autCongr_apply,
      AlgEquiv.trans_apply, decompositionAdjoinEquiv_apply]
  rw [hval]
  set φ := adjoinSepEquiv 𝔭 A hA halg with hφ
  set σ := NK.NeukirchUchida.decompositionToAdjoin 𝔭 A hA halg ⟨u, hu⟩ with hσ
  suffices σ (φ.symm ζ) = φ.symm ζ by rw [this, AlgEquiv.apply_symm_apply]
  set w := φ.symm ζ with hw_def
  -- `w` is a primitive `n`-th root of unity in `M`
  have hw_prim : IsPrimitiveRoot w n := hζ.map_of_injective φ.symm.injective
  have hn0 : 0 < n := Nat.pos_of_ne_zero fun h => hn (h.symm ▸ dvd_zero P)
  have hpow : ((w : ↥(NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A)) :
      NK.NeukirchUchida.placeCompletion A) ^ n = 1 := by
    rw [← IntermediateField.coe_pow, hw_prim.pow_eq_one]
    rfl
  -- so `w` is algebraic over `K`
  have hw_alg : IsAlgebraic K ((w : ↥(NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A)) :
      NK.NeukirchUchida.placeCompletion A) := by
    refine ⟨Polynomial.X ^ n - Polynomial.C 1, ?_, ?_⟩
    · exact Polynomial.X_pow_sub_C_ne_zero hn0 1
    · simp only [map_sub, map_pow, Polynomial.aeval_X, hpow, map_one, sub_self]
  -- hence `w` comes from an element `y` of `K'`
  obtain ⟨y, hy⟩ := (NK.NeukirchUchida.isAlgebraic_iff_exists_placeCompletionCoe A
    ((w : ↥(NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A)) :
      NK.NeukirchUchida.placeCompletion A)).mp hw_alg
  have hwy : NK.NeukirchUchida.coInAdjoin 𝔭 A y = w := Subtype.ext hy
  -- `y` is a primitive `n`-th root of unity
  have hy_pow : y ^ n = 1 := by
    apply RingHom.injective (NK.NeukirchUchida.placeCompletionCoe A)
    rw [map_pow, map_one, hy]
    exact hpow
  have hy_dvd : ∀ l : ℕ, y ^ l = 1 → n ∣ l := by
    intro l hl
    apply hw_prim.dvd_of_pow_eq_one l
    have hxl : ((w : ↥(NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A)) :
        NK.NeukirchUchida.placeCompletion A) ^ l = 1 := by
      have h := congrArg (NK.NeukirchUchida.placeCompletionCoe A) hl
      rw [map_pow, map_one, hy] at h
      exact h
    apply Subtype.ext
    rw [IntermediateField.coe_pow, hxl, IntermediateField.coe_one]
  have hy_prim : IsPrimitiveRoot y n := ⟨hy_pow, hy_dvd⟩
  have huy : u y = y := hfix y ⟨n, hn, hy_prim⟩
  rw [← hwy, hσ, NK.NeukirchUchida.decompositionToAdjoin_coInAdjoin]
  show NK.NeukirchUchida.coInAdjoin 𝔭 A (u y) = NK.NeukirchUchida.coInAdjoin 𝔭 A y
  rw [huy]

/--
STRATEGY. Use `NK.LocalTame.inertiaOfDecomposition_iff_of_localIso` with `hT` to replace the
opaque identification `NK.FrobeniusBridge.localGaloisEquiv` by the explicit
`NK.ResidueFrob.localGaloisEquivAdjoin` (this is why the `TameData` hypothesis is needed).  For
the explicit identification, `inertiaSubgroup p` is by definition the fixing subgroup of the
roots of unity of `κ̄` of order prime to `p`, and `localGaloisEquivAdjoin A ⟨u,hu⟩` is
`AlgEquiv.autCongr (adjoinSepEquiv p A hA halg) (decompositionToAdjoin ...)`, so it suffices to
show that `decompositionToAdjoin p A hA halg ⟨u,hu⟩` fixes every root of unity of `M = K_𝔭·K'`
of order prime to `p`.  For such a root of unity `w : ↥M`, `IsAlgebraic K w` holds (it is a root
of unity, hence algebraic over the prime field), so by
`NK.NeukirchUchida.isAlgebraic_iff_exists_placeCompletionCoe` there is `y : K'` with
`placeCompletionCoe A.1 y = (w : placeCompletion A.1)`, i.e. `w = coInAdjoin p A.1 y`; then `y` is
itself a primitive `n`-th root of unity for some `n` with `¬ p ∣ n` (use injectivity of
`placeCompletionCoe A.1`), so `u y = y` by `hfix`, and
`NK.NeukirchUchida.decompositionToAdjoin_coInAdjoin` gives the claim.
-/
theorem mem_inertiaSubgroup_of_fixes_rootsOfUnity {K : Type*} [Field K] [NumberField K]
    {K' : Type*} [Field K'] [Algebra K K'] [IsSepClosure K K']
    (A : NK.FrobeniusBridge.FinitePlaceOf K K') {p q : ℕ}
    (hT : NK.LocalTame.TameData p q (NK.FrobeniusBridge.localField A)
      (NK.FrobeniusBridge.localClosure A))
    {u : Gal(K'/K)}
    (hu : u ∈ Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := K') A.1)
    (hfix : ∀ ζ : K', (∃ n : ℕ, ¬ p ∣ n ∧ IsPrimitiveRoot ζ n) → u ζ = ζ) :
    NK.FrobeniusBridge.localGaloisEquiv A ⟨u, hu⟩ ∈
      NK.LocalAnabelian.inertiaSubgroup (κ := NK.FrobeniusBridge.localField A)
        (K' := NK.FrobeniusBridge.localClosure A) p := by
  -- the local algebra structure used by `localGaloisEquivAdjoin`
  letI : Algebra (NK.FrobeniusBridge.localField A) (NK.NeukirchUchida.placeCompletion A.1) :=
    (NK.NeukirchUchida.adicCompletionToPlaceCompletion
      (Submission.NeukirchUchida.primeOf A.1 A.2) A.1
      (Submission.NeukirchUchida.primeOf_spec A.1 A.2)).toAlgebra
  -- unwrap the explicit identification
  have hun : NK.ResidueFrob.localGaloisEquivAdjoin A ⟨u, hu⟩
      = adjoinLocalIso (Submission.NeukirchUchida.primeOf A.1 A.2) A.1
          (Submission.NeukirchUchida.primeOf_spec A.1 A.2) (fun z => rfl)
          (NK.NeukirchUchida.comap_adicCompletionToPlaceCompletion_eq_adicCompletionIntegers
            (Submission.NeukirchUchida.primeOf A.1 A.2) A.1
            (Submission.NeukirchUchida.primeOf_spec A.1 A.2)) ⟨u, hu⟩ := rfl
  -- switch from the opaque to the explicit identification
  refine (NK.LocalTame.inertiaOfDecomposition_iff_of_localIso hT
    (NK.FrobeniusBridge.localGaloisEquiv A) (localGaloisEquivAdjoin A) ⟨u, hu⟩).mpr ?_
  simp only [NK.LocalTame.inertiaOfDecomposition, Subgroup.mem_comap]
  change NK.ResidueFrob.localGaloisEquivAdjoin A ⟨u, hu⟩ ∈
    NK.LocalAnabelian.inertiaSubgroup (κ := NK.FrobeniusBridge.localField A)
      (K' := NK.FrobeniusBridge.localClosure A) p
  rw [hun]
  exact mem_inertiaSubgroup_adjoinLocalIso_of_fixes_rootsOfUnity
    (Submission.NeukirchUchida.primeOf A.1 A.2) A.1
    (Submission.NeukirchUchida.primeOf_spec A.1 A.2) (fun z => rfl) _ p hu hfix

end NK.ResidueFrob
