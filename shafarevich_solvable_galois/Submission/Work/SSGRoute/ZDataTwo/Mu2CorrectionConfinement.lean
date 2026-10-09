import Mathlib
import Submission.Work.SSGRoute.GrunwaldEscapeCore.gesCorrectionFromPrime
import Submission.Work.SSGRoute.GrunwaldEscapeCore.gesEscapePrimeSplit
import Submission.Work.SSGRoute.ZDataTwo.Mu2EscapeSquare
import Submission.Work.SSGRoute.shafarevich_z_data_two
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The confinement half of the `p = 2` escape correction, for an arbitrary input class

`Work.SSGRoute.GrunwaldEscapeCore.gesCorrectionFromPrime` (proved, all `p`) is the *Čebotarev*
half of the Grünwald-with-escape correction: given a fractional ideal `𝔵` whose divisor matches that
of `a ∈ (↥K)ˣ` away from the primes of `T'` and is one larger at a single new prime `𝔮`, and whose
idéle class lies in `U = gesU ↥K p T'`, it produces `b ∈ (↥K)ˣ` with the *same* local Kummer data at
the places of `T` as `a`, and unramified outside the `K`-primes of `T'` and of `𝔮`.

`Work.SSGRoute.GrunwaldEscapeCore.gesEscapeTrivialPair` builds `𝔵` and `𝔮` from the escape prime
produced by `gesEscapePrimeSplit`, but only for the *specific* element `a` coming out of
`grunwald_kummer_first_element` (and with an unusable-at-`p = 2` hypothesis `hKimag`).

This module performs the same construction for an **arbitrary** `a : (↥K)ˣ`, at `p = 2`, giving

`Work.SSGRoute.ZDataTwo.mu2Correction_confinement` — for every `a` there are `Q` and `b` with

* `Q` finite, split in `K`, avoiding the `G_K`-classes of `T`,
* `b` has the same local Kummer data at the places of `T` as `a`,
* `b` is unramified outside the `G_K`-classes of `T` and of `Q`,

i.e. the whole *confinement* half of `Mu2EscapeCorrection` (only the archimedean clause is missing —
and see the counterexample recorded in `ZDataTwo/Mu2EscapeSquare.lean`, showing that the datum-free
formulation of that clause is false).  Note that the coverage hypothesis here is the `G_K`-conjugacy
form used by `gesEscapeTrivialPair` (`∃ A ∈ T, gesKConj K A B`), *not* the `k`-conjugacy form
`∃ A ∈ T, IsConjPlace k A B` carried by `Mu2EscapeCorrection`: the Čebotarev step needs the
`K`-primes of the places over `2` to lie in `T'`, which the `k`-conjugacy form does not give unless
`T` is also closed under `G_k`-conjugation (as it is in the §4 recursion, where `T` is a union of
`G_k`-classes).  The general case additionally needs the read-off element `γ` to be totally positive.

The proof is the one of steps 3--6 of `gesEscapeTrivialPair` with `a` as an input; the only new
plumbing compared with that file is `gesKConj_iff_comap_eq` (the `G_K`-conjugacy of two places is
exactly the equality of the `K`-primes below them), which converts between the `ValuationSubring`
vocabulary of `Mu2EscapeCorrection` and the prime-ideal vocabulary of `gesCorrectionFromPrime`.
-/

open scoped Pointwise NumberField

namespace Work.SSGRoute.ZDataTwo

open _root_.SSGRoute
open NumberField IsDedekindDomain

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **Two places of `Ω` are `G_K`-conjugate exactly when their `K`-primes agree.** -/
theorem gesKConj_iff_comap_eq {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A B : ValuationSubring Ω) (hA : A.comap (algebraMap ↥K Ω) ≠ ⊤) :
    Work.SSGRoute.gesKConj K A B ↔
      A.comap (algebraMap ↥K Ω) = B.comap (algebraMap ↥K Ω) := by
  haveI : NumberField ↥K := NumberField.of_module_finite k ↥K
  constructor
  · rintro ⟨τ, hτ, hτA⟩
    rw [← hτA]
    exact (Work.SSGRoute.comap_smul_eq_of_mem_fixingSubgroup K hτ A).symm
  · exact Work.SSGRoute.exists_mem_fixingSubgroup_smul_eq_of_comap_eq K hA

/-- **The confinement half of the `p = 2` escape correction, for an arbitrary input class.** -/
theorem mu2Correction_confinement (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, Work.SSGRoute.gesKConj K A B → A = B)
    (hTcov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      B.valuation (2 : Ω) < 1 → ∃ A ∈ T, Work.SSGRoute.gesKConj K A B)
    (a : (↥K)ˣ) :
    ∃ (Q : ValuationSubring Ω) (b : (↥K)ˣ),
      SSGRoute.IsFinPlace k Q ∧ SSGRoute.IsSplitIn k K Q ∧
      (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A Q) ∧
      (∀ A ∈ T, ∀ σ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ b
            (Work.SSGRoute.gesLocalToGalK K σ) =
          Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ a
            (Work.SSGRoute.gesLocalToGalK K σ)) ∧
      (∀ (B : ValuationSubring Ω), SSGRoute.IsFinPlace k B →
        (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) →
        (¬ Work.SSGRoute.gesKConj K Q B) →
        ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup), SSGRoute.IsInertia k B σ →
          Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ b
            (Work.SSGRoute.gesGalKOfFixing K σ hσ) = 0) := by
  classical
  haveI hNumK : NumberField ↥K := NumberField.of_module_finite k ↥K
  -- the prime of `↥K` below each place of `T`
  let primeBelow : (A : {A // A ∈ T}) → NK.Chebotarev.PrimeIdeal ↥K :=
    fun A => (Work.SSGRoute.GrunwaldEscapeCore.exists_primeIdeal_of_comap_ne_top K A.1
      (hTfin A.1 A.2)).choose
  have hprimeBelow : ∀ A : {A // A ∈ T},
      A.1.comap (algebraMap ↥K Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K (primeBelow A) :=
    fun A => (Work.SSGRoute.GrunwaldEscapeCore.exists_primeIdeal_of_comap_ne_top K A.1
      (hTfin A.1 A.2)).choose_spec
  let T' : Finset (NK.Chebotarev.PrimeIdeal ↥K) := T.attach.image primeBelow
  have hT'below : ∀ A ∈ T, ∃ 𝔭 ∈ T',
      A.comap (algebraMap ↥K Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 := by
    intro A hA
    exact ⟨primeBelow ⟨A, hA⟩, Finset.mem_image_of_mem _ (Finset.mem_attach T ⟨A, hA⟩),
      hprimeBelow ⟨A, hA⟩⟩
  have hT'above : ∀ 𝔭 ∈ T', ∃ A ∈ T,
      A.comap (algebraMap ↥K Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 := by
    intro 𝔭 h𝔭
    obtain ⟨A, -, hA⟩ := Finset.mem_image.mp h𝔭
    exact ⟨A.1, A.2, by rw [← hA]; exact hprimeBelow A⟩
  have hcomapK_ne_top : ∀ {B : ValuationSubring Ω}, SSGRoute.IsFinPlace k B →
      B.comap (algebraMap ↥K Ω) ≠ ⊤ := by
    intro B hB
    exact Work.SSGRoute.comap_algebraMap_ne_top_of_isFinPlace K hB
  have hT'p : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → B.valuation (2 : Ω) < 1 →
      ∃ 𝔭 ∈ T',
        B.comap (algebraMap ↥K Ω) =
          IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 := by
    intro B hB hp
    obtain ⟨A, hA, hconj⟩ := hTcov B hB hp
    obtain ⟨𝔭, h𝔭T', h𝔭A⟩ := hT'below A hA
    refine ⟨𝔭, h𝔭T', ?_⟩
    have hAB : A.comap (algebraMap ↥K Ω) = B.comap (algebraMap ↥K Ω) :=
      (gesKConj_iff_comap_eq K A B (hcomapK_ne_top (hTfin A hA))).mp hconj
    rw [← h𝔭A, hAB]
  -- ## the `T'`-free part of the divisor of `a`
  let dfree : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥K) → ℤ := fun q =>
    if q ∈ T' then 0 else FractionalIdeal.count ↥K q
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 ↥K)) (a : ↥K))
  have hdfree : ∀ᶠ q in Filter.cofinite, dfree q = 0 := by
    filter_upwards [FractionalIdeal.finite_factors
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 ↥K)) (a : ↥K))] with q hq
    by_cases hqT : q ∈ T'
    · simp [dfree, hqT]
    · simp [dfree, hqT, hq]
  let y𝔡 : NK.GlobalCFT.Idele ↥K := NK.GlobalCFT.IdeleClassGroup.ideleOfFun ↥K dfree hdfree
  let 𝔡 : FractionalIdeal (nonZeroDivisors (𝓞 ↥K)) ↥K := y𝔡.idealOf
  have hcount𝔡 : ∀ q, FractionalIdeal.count ↥K q 𝔡 = dfree q := by
    intro q
    rw [NK.GlobalCFT.Idele.count_idealOf, NK.GlobalCFT.IdeleClassGroup.exp_ideleOfFun]
  -- ## Čebotarev: the escape prime
  obtain ⟨Q, 𝔮, hQfin, hQsplit, h𝔮T', hQcomap, hQnotT, hclass⟩ :=
    Work.SSGRoute.GrunwaldEscapeCore.gesEscapePrimeSplit 2 k Ω K T' T hTfin hT'below
      (NK.GlobalCFT.IdeleClassGroup.mk ↥K (NK.NUV2.RouteB.RayModulus.fracIdele 𝔡))
  -- ## the fractional ideal `𝔵 = 𝔡 · (𝔮)`
  let 𝔵 : FractionalIdeal (nonZeroDivisors (𝓞 ↥K)) ↥K :=
    𝔡 * (NK.HeckeL.ideleOfPrime ↥K 𝔮).idealOf
  have hcount𝔮 : ∀ q, FractionalIdeal.count ↥K q (NK.HeckeL.ideleOfPrime ↥K 𝔮).idealOf =
      (if q = 𝔮 then 1 else 0) := by
    intro q
    rw [NK.GlobalCFT.Idele.count_idealOf]
    show NK.GlobalCFT.Idele.exp q (NK.GlobalCFT.IdeleClassGroup.ideleOfFun ↥K
      (fun q' => if q' = 𝔮 then 1 else 0) _) = _
    rw [NK.GlobalCFT.IdeleClassGroup.exp_ideleOfFun]
  have hcount𝔵 : ∀ q, FractionalIdeal.count ↥K q 𝔵 = dfree q + (if q = 𝔮 then 1 else 0) := by
    intro q
    rw [FractionalIdeal.count_mul ↥K q (NK.GlobalCFT.Idele.idealOf_ne_zero y𝔡)
        (NK.GlobalCFT.Idele.idealOf_ne_zero (NK.HeckeL.ideleOfPrime ↥K 𝔮)),
      hcount𝔡 q, hcount𝔮 q]
  have h𝔵T : ∀ 𝔭 ∈ T', FractionalIdeal.count ↥K 𝔭 𝔵 = 0 := by
    intro 𝔭 h𝔭
    have h𝔭𝔮 : 𝔭 ≠ 𝔮 := fun h => h𝔮T' (h ▸ h𝔭)
    rw [hcount𝔵 𝔭, if_neg h𝔭𝔮, add_zero]
    simp [dfree, h𝔭]
  have h𝔵div : ∀ 𝔭, 𝔭 ∉ T' → 𝔭 ≠ 𝔮 → FractionalIdeal.count ↥K 𝔭 𝔵 =
      FractionalIdeal.count ↥K 𝔭
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 ↥K)) (a : ↥K)) := by
    intro 𝔭 h𝔭T h𝔭𝔮
    rw [hcount𝔵 𝔭, if_neg h𝔭𝔮, add_zero]
    simp [dfree, h𝔭T]
  have h𝔵𝔮 : 𝔮 ∉ T' → FractionalIdeal.count ↥K 𝔮 𝔵 =
      FractionalIdeal.count ↥K 𝔮
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 ↥K)) (a : ↥K)) + 1 := by
    intro h𝔮T
    rw [hcount𝔵 𝔮, if_pos rfl]
    simp [dfree, h𝔮T]
  have hfrac𝔮 : NK.NUV2.RouteB.RayModulus.fracIdele
      ((NK.HeckeL.ideleOfPrime ↥K 𝔮).idealOf) = NK.HeckeL.ideleOfPrime ↥K 𝔮 := by
    rw [NK.NUV2.RouteB.RayModulus.fracIdele_idealOf]
    refine (NK.HeckeL.Basic.IdeleFun.congr _ _ ?_).trans rfl
    funext q
    show NK.GlobalCFT.Idele.exp q (NK.GlobalCFT.IdeleClassGroup.ideleOfFun ↥K
      (fun q' => if q' = 𝔮 then 1 else 0) _) = _
    rw [NK.GlobalCFT.IdeleClassGroup.exp_ideleOfFun]
  have hmem : NK.GlobalCFT.IdeleClassGroup.mk ↥K (NK.NUV2.RouteB.RayModulus.fracIdele 𝔵) ∈
      Work.SSGRoute.GrunwaldEscapeCore.gesU ↥K 2 T' := by
    have hfrac : NK.NUV2.RouteB.RayModulus.fracIdele 𝔵 =
        NK.NUV2.RouteB.RayModulus.fracIdele 𝔡 * NK.HeckeL.ideleOfPrime ↥K 𝔮 := by
      rw [NK.NUV2.RouteB.RayModulus.fracIdele_mul (NK.GlobalCFT.Idele.idealOf_ne_zero y𝔡)
        (NK.GlobalCFT.Idele.idealOf_ne_zero (NK.HeckeL.ideleOfPrime ↥K 𝔮)), hfrac𝔮]
    rw [hfrac, map_mul]
    simpa only [mul_comm] using hclass
  -- ## the correction
  obtain ⟨b, hagree, hunr⟩ :=
    Work.SSGRoute.GrunwaldEscapeCore.gesCorrectionFromPrime 2 k Ω K ζ hζ T hTfin T' hT'below
      hT'p a 𝔵 h𝔵T 𝔮 h𝔵div h𝔵𝔮 hmem
  refine ⟨Q, b, hQfin, hQsplit, hQnotT, ?_, ?_⟩
  · intro A hA σ
    exact (hagree A hA σ).symm
  · intro B hB hnotT hnotQ σ hσ hI
    refine hunr B hB (fun 𝔭 h𝔭 h𝔭B => ?_) (fun h𝔮B => ?_) σ hσ hI
    · obtain ⟨A, hA, hAcomap⟩ := hT'above 𝔭 h𝔭
      exact hnotT A hA ((gesKConj_iff_comap_eq K A B (hcomapK_ne_top (hTfin A hA))).mpr
        (by rw [hAcomap, h𝔭B]))
    · exact hnotQ ((gesKConj_iff_comap_eq K Q B (hcomapK_ne_top hQfin)).mpr (by rw [hQcomap, h𝔮B]))

end Work.SSGRoute.ZDataTwo
