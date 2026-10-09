import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ZDataTwo.KummerCocharBase
import Submission.Work.SSGRoute.ZDataTwo.SignAdjustment
import Submission.Work.SSGRoute.ZDataTwo.Mu2EscapeStep
import Submission.Work.SSGRoute.ZDataTwo.firstElementTotallyPositive
import Submission.Work.SSGRoute.H9.NarrowReadOff
import Submission.Work.SSGRoute.H9.NarrowCorrection
import Submission.Work.SSGRoute.H9.NarrowMu2
import Submission.Work.SSGRoute.H9.NarrowFiniteIndex
import Submission.Work.SSGRoute.step4_y_escape_v2.GesUFacts
import Submission.Work.SSGRoute.GrunwaldEscapeCore.escape_prime_orthogonality
import Submission.Work.SSGRoute.GrunwaldEscapeCore.gesCorrectionFromPrime
import Submission.Work.SSGRoute.ZConstruction.TwoFieldOrthogonality
import Submission.Work.SSGRoute.ZDataTwo.mu2KummerFirstElement
import Submission.Work.SSGRoute.EscapeCoreLib.memGesUOfIsFrobAtPrime
import Submission.Work.SSG8Escape.escape_prime_ssg8
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `p = 2` escape realisation with the orthogonality field and the escape field *separated*

This is the two-field `p = 2` escape of Schmidt--Wingberg §4 that the realisation
`Work.SSGRoute.ZRealV2.z_realisation_of_grunwald_v2_own` needs at `p = 2` (see
`ACTION_p2_twoFieldRealisation.md` §2 and `PING_NoKimag_realisation_escape_field.md`): the single-field
oracle `Work.SSGRoute.ZDataTwo.mu2EscapeRealisationH` conflates the field at which the prescribed
datum's orthogonality is read off (which must be the *small* field `Λ`, so that the correction blocks
over `S₀ ∖ S` are orthogonal) with the field in which the escape prime is split (which must be the
*big* field `Λ ⊔ L₂`, so that clause (5) of the realisation reaches the level `L ≤ Λ ⊔ L₂`).

The arithmetic of the escape step is the same as in the oracle
(`ZDataTwo/mu2EscapeRealisationH.lean`): the totally positive first element
(`ZDataTwo.firstElement_totallyPositive`), the class field `M` of the narrow modulus
`U' = narrowGesU ↥K 2 T' ⊔ C_↥K²`, the escape prime (`GrunwaldEscapeCore.escape_prime_orthogonality`)
and the read-off at that prime (`H9.correctionFromPrime_narrow`, which also transports the total
positivity to the corrected element `b`).  The only change is the **interface**: the orthogonality of
the class `𝔡` of the `T'`-free part of `a` is not reproved here but taken as a hypothesis, in the
form in which the two-field narrow orthogonality of `Work.SSGRoute.NoKimag.OrthHsplitTwoNarrow`
delivers it (with `N'` the copy over `↥K` of `Λ ⊔ L₂`).  This keeps the escape free of every
`hKimag`-type hypothesis and free of the (still open) orthogonality development. -/

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute
open scoped Pointwise
open NumberField IsDedekindDomain
open NK.GlobalCFT

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

/-- **The `p = 2` escape realisation with two fields.**  See the module docstring: `Λ` is the
orthogonality field, `Λ ⊔ L₂` the escape field, and the orthogonality of the class of the first
element is the hypothesis `horth`. -/
theorem mu2EscapeTwoField (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K Λ L₂ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] [FiniteDimensional k L₂] [IsGalois k L₂]
    (hKΛ : K ≤ Λ) (hKL₂ : K ≤ L₂)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (hζK' : IsPrimitiveRoot (⟨ζ, hζK⟩ : ↥K) 2)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, Work.SSGRoute.gesKConj K A B → A = B)
    (hTcov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (B.valuation (2 : Ω) < 1 ∨
        (∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ Λ.fixingSubgroup) ∨
        (∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ L₂.fixingSubgroup)) →
      ∃ A ∈ T, Work.SSGRoute.gesKConj K A B)
    (g : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hg : ∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, g (x * y) = g x + g y)
    (hgc : SSGRoute.IsLocConstOn K.fixingSubgroup g)
    (h : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hh : ∀ A ∈ T, ∀ x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      ∀ y ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A (x * y) = h A x + h A y)
    (hhc : ∀ A ∈ T, ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      ∀ x ∈ U, x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup → h A x = 0)
    (hgram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → g σ = 0)
    (hginf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → g c = 0)
    (horth₁ : ∀ A ∈ T,
      (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A σ = 0) ∨
      (∀ χ : (Ω ≃ₐ[k] Ω) → ZMod 2,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
        (∀ σ ∈ Λ.fixingSubgroup, χ σ = 0) →
        ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, χ σ = 0) ∨
      ((∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → h A σ = 0) ∧
        ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod 2,
          (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
          (∀ σ ∈ Λ.fixingSubgroup, χ σ = 0) →
          ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → χ σ = 0))
    (horth₂ : ∀ A ∈ T,
      (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, g σ + h A σ = 0) ∨
      (∀ χ : (Ω ≃ₐ[k] Ω) → ZMod 2,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
        (∀ σ ∈ L₂.fixingSubgroup, χ σ = 0) →
        ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, χ σ = 0) ∨
      ((∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → g σ + h A σ = 0) ∧
        ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod 2,
          (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
          (∀ σ ∈ L₂.fixingSubgroup, χ σ = 0) →
          ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → χ σ = 0))
    (hsplit : ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod 2,
      (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
      (∀ σ ∈ (Λ ⊔ L₂ : IntermediateField k Ω).fixingSubgroup, χ σ = 0) →
      ∃ χ₁ χ₂ : (Ω ≃ₐ[k] Ω) → ZMod 2,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ₁ (x * y) = χ₁ x + χ₁ y) ∧
        (∀ σ ∈ Λ.fixingSubgroup, χ₁ σ = 0) ∧
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ₂ (x * y) = χ₂ x + χ₂ y) ∧
        (∀ σ ∈ L₂.fixingSubgroup, χ₂ σ = 0) ∧
        ∀ σ ∈ K.fixingSubgroup, χ σ = χ₁ σ + χ₂ σ)
    (horth : Work.SSGRoute.ZConstruction.TwoFieldOrthogonality (k := k) (Ω := Ω) K Λ L₂
      hKΛ hKL₂ ζ hζ hζK hζK') :
    ∃ (b : (↥K)ˣ) (Q : ValuationSubring Ω),
      SSGRoute.IsFinPlace k Q ∧ SSGRoute.IsSplitIn k (Λ ⊔ L₂) Q ∧
      (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A Q) ∧
      (∀ A ∈ T, ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
        Work.SSGRoute.nodeKummerCochar K ζ hζK hζ b σ = g σ + h A σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → Work.SSGRoute.nodeKummerCochar K ζ hζK hζ b c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) →
        (¬ Work.SSGRoute.gesKConj K Q B) →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ →
          Work.SSGRoute.nodeKummerCochar K ζ hζK hζ b σ = 0) := by
  classical
  haveI hNumK : NumberField ↥K := NumberField.of_module_finite k ↥K
  -- (a) the totally positive first element realising the datum at `T`
  obtain ⟨a, ha, hapos⟩ :=
    Work.SSGRoute.ZDataTwo.firstElement_totallyPositive k Ω K ⟨ζ, hζK⟩ hζK' T hTfin hTdisj g hg hgc
      h hh hhc
  -- ## 0. the primes `T'` of `↥K` below the places of `T`
  let primeBelow : (A : {A // A ∈ T}) → NK.Chebotarev.PrimeIdeal ↥K :=
    fun A => (GrunwaldEscapeCore.exists_primeIdeal_of_comap_ne_top K A.1 (hTfin A.1 A.2)).choose
  have hprimeBelow : ∀ A : {A // A ∈ T},
      A.1.comap (algebraMap ↥K Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K (primeBelow A) :=
    fun A => (GrunwaldEscapeCore.exists_primeIdeal_of_comap_ne_top K A.1
      (hTfin A.1 A.2)).choose_spec
  let T' : Finset (NK.Chebotarev.PrimeIdeal ↥K) := T.attach.image primeBelow
  have hTbelow : ∀ A ∈ T, ∃ 𝔭 ∈ T',
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
    intro B hB htop
    apply hB
    refine le_antisymm le_top ?_
    intro x _
    have h1 : algebraMap ↥K Ω (algebraMap k ↥K x) ∈ B := by
      rw [← ValuationSubring.mem_comap, htop]
      exact trivial
    rwa [← IsScalarTower.algebraMap_apply k ↥K Ω] at h1
  -- the places over `2` lie in the classes of `T` (`hTcov`), hence over `T'`
  have hT'p : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → B.valuation (2 : Ω) < 1 →
      ∃ 𝔭 ∈ T', B.comap (algebraMap ↥K Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 := by
    intro B hB hpB
    obtain ⟨A, hA, hconj⟩ := hTcov B hB (Or.inl hpB)
    obtain ⟨𝔭, h𝔭T', h𝔭A⟩ := hTbelow A hA
    obtain ⟨τ, hτ, hτA⟩ := hconj
    refine ⟨𝔭, h𝔭T', ?_⟩
    rw [← h𝔭A, ← hτA]
    have hcoe : ⇑((IntermediateField.fixingSubgroupEquiv K) ⟨τ, hτ⟩) = ⇑τ := funext fun _ => rfl
    rw [(GrunwaldEscapeCore.gesSmulEqOfCoeEq K hcoe A).symm]
    exact Commons.NumberTheory.NumberField.Valuation.comap_smul_algebraMap A _
  -- ## 1. the field `N' = baseChange K (Λ ⊔ L₂)` over `↥K`  (the *escape* field)
  have hKΛL : K ≤ (Λ ⊔ L₂ : IntermediateField k Ω) := le_trans hKΛ le_sup_left
  let N' : IntermediateField ↥K Ω := EscapeCoreLib.baseChange K (Λ ⊔ L₂) hKΛL
  have hN' : (N' : Set Ω) = ((Λ ⊔ L₂ : IntermediateField k Ω) : Set Ω) := by
    ext x
    exact EscapeCoreLib.mem_baseChange K (Λ ⊔ L₂) hKΛL
  haveI hN'fdk : FiniteDimensional k ↥N' :=
    EscapeCoreLib.finiteDimensional_baseChange K (Λ ⊔ L₂) hKΛL
  haveI hN'fd : FiniteDimensional ↥K ↥N' := Module.Finite.of_restrictScalars_finite k ↥K ↥N'
  haveI hN'gal : IsGalois ↥K ↥N' := EscapeCoreLib.isGalois_baseChange K (Λ ⊔ L₂) hKΛL
  haveI hN'nf : NumberField ↥N' := NumberField.of_module_finite ↥K ↥N'
  -- ## 2. the class field `M` of the narrow modulus `U' = narrowGesU ↥K 2 T' ⊔ C_↥K²`
  let U' : Subgroup (IdeleClassGroup ↥K) :=
    Work.SSGRoute.H9.narrowGesU ↥K 2 T' ⊔
      Work.SSGRoute.EscapeCoreLib.pPowSubgroup 2 (IdeleClassGroup ↥K)
  have hU'fin : U'.FiniteIndex :=
    Work.SSGRoute.step4_y_escape_v2.finiteIndex_of_le le_sup_left
      (Work.SSGRoute.H9.narrowGesU_finiteIndex (K := ↥K) 2 T')
  have hU'open : IsOpen (U' : Set (IdeleClassGroup ↥K)) :=
    Work.SSGRoute.step4_y_escape_v2.isOpen_of_le_isOpen le_sup_left
      (Work.SSGRoute.H9.isOpen_narrowGesU 2 Nat.prime_two (K := ↥K) T')
  obtain ⟨M, hMfd, hMgal, hMnf, hMcomm, hMnorm⟩ :=
    GrunwaldEscapeCore.exists_abelian_classField_inside K U' hU'fin hU'open
  haveI : FiniteDimensional ↥K M := hMfd
  haveI : IsGalois ↥K M := hMgal
  haveI : NumberField ↥M := hMnf
  haveI : IsMulCommutative (↥M ≃ₐ[↥K] ↥M) := hMcomm
  -- ## 3. the orthogonality, from the hypothesis (the two-field narrow orthogonality)
  have horth_mem : IdeleClassGroup.mk ↥K
      (NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart (K := ↥K) T' a)) ∈
      U' ⊔ Idele.normClassSubgroup ↥K ↥N' := by
    rw [← hMnorm]
    exact horth T hTfin hTdisj hTcov g hg hgc hgram hginf h hh hhc horth₁ horth₂ hsplit T' hTbelow
      hT'above M hMnorm N' hN' a ha hapos
  -- ## 4. the escape prime, split in the *escape* field `Λ ⊔ L₂`
  obtain ⟨Q, 𝔮, hQfin, hQsplit, h𝔮T', hQnotT, hQcomap, hQmem⟩ :=
    GrunwaldEscapeCore.escape_prime_orthogonality K M U' hMnorm (Λ ⊔ L₂) N' hKΛL hN'
      T hTfin T' hTbelow
      (IdeleClassGroup.mk ↥K (NK.NUV2.RouteB.RayModulus.fracIdele
        (Work.SSGRoute.tFreePart (K := ↥K) T' a))) horth_mem
  -- ## 5. the fractional ideal `𝔵 = 𝔡 · (𝔮)` of the corrected element
  let 𝔡 : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) ↥K :=
    Work.SSGRoute.tFreePart T' a
  let 𝔵 : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) ↥K :=
    𝔡 * (NK.HeckeL.ideleOfPrime ↥K 𝔮).idealOf
  have hcount𝔮 : ∀ q, FractionalIdeal.count ↥K q (NK.HeckeL.ideleOfPrime ↥K 𝔮).idealOf =
      (if q = 𝔮 then 1 else 0) := by
    intro q
    rw [NK.GlobalCFT.Idele.count_idealOf]
    show NK.GlobalCFT.Idele.exp q (NK.GlobalCFT.IdeleClassGroup.ideleOfFun ↥K
      (fun q' => if q' = 𝔮 then 1 else 0) _) = _
    rw [NK.GlobalCFT.IdeleClassGroup.exp_ideleOfFun]
  have hcount𝔡 : ∀ q, FractionalIdeal.count ↥K q 𝔡 =
      (if q ∈ T' then 0 else FractionalIdeal.count ↥K q
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          (a : ↥K))) := by
    intro q
    rw [Work.SSGRoute.tFreePart_count]
    by_cases hq : q ∈ T'
    · rw [Work.SSGRoute.tFreeExp_of_mem T' a hq, if_pos hq]
    · rw [Work.SSGRoute.tFreeExp_of_not_mem T' a hq, if_neg hq,
        ← Idele.idealOf_principalIdele, Idele.count_idealOf]
  have h𝔡0 : 𝔡 ≠ 0 := by
    change Work.SSGRoute.tFreePart T' a ≠ 0
    exact Idele.idealOf_ne_zero _
  have hcount𝔵 : ∀ q, FractionalIdeal.count ↥K q 𝔵 =
      FractionalIdeal.count ↥K q 𝔡 + (if q = 𝔮 then 1 else 0) := by
    intro q
    change FractionalIdeal.count ↥K q (𝔡 * (NK.HeckeL.ideleOfPrime ↥K 𝔮).idealOf) =
      FractionalIdeal.count ↥K q 𝔡 + (if q = 𝔮 then 1 else 0)
    rw [FractionalIdeal.count_mul ↥K q h𝔡0 (Idele.idealOf_ne_zero _), hcount𝔮 q]
  have h𝔵T : ∀ 𝔭 ∈ T', FractionalIdeal.count ↥K 𝔭 𝔵 = 0 := by
    intro 𝔭 h𝔭
    have h𝔭𝔮 : 𝔭 ≠ 𝔮 := fun hEq => h𝔮T' (hEq ▸ h𝔭)
    rw [hcount𝔵 𝔭, if_neg h𝔭𝔮, add_zero, hcount𝔡 𝔭, if_pos h𝔭]
  have h𝔵div : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      𝔭 ∉ T' → 𝔭 ≠ 𝔮 → FractionalIdeal.count ↥K 𝔭 𝔵 =
        FractionalIdeal.count ↥K 𝔭
          (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
            (a : ↥K)) := by
    intro 𝔭 h𝔭T h𝔭𝔮
    rw [hcount𝔵 𝔭, if_neg h𝔭𝔮, add_zero, hcount𝔡 𝔭, if_neg h𝔭T]
  have h𝔵𝔮 : FractionalIdeal.count ↥K 𝔮 𝔵 =
      FractionalIdeal.count ↥K 𝔮
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          (a : ↥K)) + 1 := by
    rw [hcount𝔵 𝔮, if_pos rfl, hcount𝔡 𝔮, if_neg h𝔮T']
  have hfrac𝔮 : NK.NUV2.RouteB.RayModulus.fracIdele
      ((NK.HeckeL.ideleOfPrime ↥K 𝔮).idealOf) = NK.HeckeL.ideleOfPrime ↥K 𝔮 := by
    rw [NK.NUV2.RouteB.RayModulus.fracIdele_idealOf]
    refine (NK.HeckeL.Basic.IdeleFun.congr _ _ ?_).trans rfl
    funext q
    show NK.GlobalCFT.Idele.exp q (NK.GlobalCFT.IdeleClassGroup.ideleOfFun ↥K
      (fun q' => if q' = 𝔮 then 1 else 0) _) = _
    rw [NK.GlobalCFT.IdeleClassGroup.exp_ideleOfFun]
  have hmem : IdeleClassGroup.mk ↥K (NK.NUV2.RouteB.RayModulus.fracIdele 𝔵) ∈ U' := by
    have hfrac : NK.NUV2.RouteB.RayModulus.fracIdele 𝔵 =
        NK.NUV2.RouteB.RayModulus.fracIdele 𝔡 * NK.HeckeL.ideleOfPrime ↥K 𝔮 := by
      rw [show 𝔵 = 𝔡 * (NK.HeckeL.ideleOfPrime ↥K 𝔮).idealOf from rfl,
        NK.NUV2.RouteB.RayModulus.fracIdele_mul h𝔡0 (Idele.idealOf_ne_zero _), hfrac𝔮]
    have hC : IdeleClassGroup.mk ↥K (NK.NUV2.RouteB.RayModulus.fracIdele 𝔡) =
        IdeleClassGroup.mk ↥K (NK.NUV2.RouteB.RayModulus.fracIdele
          (Work.SSGRoute.tFreePart T' a)) := rfl
    rw [hfrac, map_mul, hC]
    simpa only [mul_comm] using hQmem
  -- ## 6. the narrow correction at the escape prime
  obtain ⟨b, hagree, hesc, hinv⟩ :=
    Work.SSGRoute.H9.correctionFromPrime_narrow k Ω K ⟨ζ, hζK⟩ hζK' T hTfin T' hTbelow hT'p a hapos
      𝔵 h𝔵T 𝔮 h𝔵div h𝔵𝔮 hmem
  -- ## 7. the assembly
  refine ⟨b, Q, hQfin, hQsplit, hQnotT, ?_, ?_, ?_⟩
  · -- the prescribed local datum at `T`
    intro A hA σ hσ
    have hσK : σ ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp hσ).2
    show ZSplit.nodeKummerCocharZMod K ζ hζK hζ b σ = g σ + h A σ
    rw [ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK) (hζ := hζ)
      (β := b) hσK]
    have hto : (IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσK⟩ =
        Work.SSGRoute.gesLocalToGalK K ⟨σ, hσ⟩ := rfl
    rw [hto, hagree A hA ⟨σ, hσ⟩]
    exact (ha A hA ⟨σ, hσ⟩).symm
  · -- the involutions of `G_K`
    intro c hc hc2
    show ZSplit.nodeKummerCocharZMod K ζ hζK hζ b c = 0
    rw [ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK) (hζ := hζ)
      (β := b) hc]
    have hto : (IntermediateField.fixingSubgroupEquiv K) ⟨c, hc⟩ =
        Work.SSGRoute.gesGalKOfFixing K c hc := rfl
    rw [hto]
    exact hinv c hc hc2
  · -- unramified outside the classes of `T` and of `Q`
    intro B hBfin hBnotT hBnotQ σ hσ hI
    show ZSplit.nodeKummerCocharZMod K ζ hζK hζ b σ = 0
    rw [ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK) (hζ := hζ)
      (β := b) hσ]
    have hto : (IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩ =
        Work.SSGRoute.gesGalKOfFixing K σ hσ := rfl
    rw [hto]
    refine hesc B hBfin ?_ ?_ σ hσ hI
    · intro 𝔭 h𝔭 heq
      obtain ⟨A, hA, hAcomap⟩ := hT'above 𝔭 h𝔭
      have hcomapK : A.comap (algebraMap ↥K Ω) = B.comap (algebraMap ↥K Ω) := by
        rw [hAcomap, heq]
      exact hBnotT A hA (Work.SSGRoute.exists_mem_fixingSubgroup_smul_eq_of_comap_eq K
        (hcomapK_ne_top (hTfin A hA)) hcomapK)
    · intro heq
      have hcomapK : Q.comap (algebraMap ↥K Ω) = B.comap (algebraMap ↥K Ω) := by
        rw [hQcomap, heq]
      exact hBnotQ (Work.SSGRoute.exists_mem_fixingSubgroup_smul_eq_of_comap_eq K
        (hcomapK_ne_top hQfin) hcomapK)

end Work.SSGRoute.ZConstruction
