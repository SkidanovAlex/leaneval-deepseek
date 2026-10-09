import Mathlib
import Submission.Work.SSGRoute.ZDataTwo.Mu2EscapeStep
import Submission.Work.SSGRoute.ZDataTwo.Mu2CorrectionConfinement
import Submission.Work.SSGRoute.ZDataTwo.SignAdjustment
import Submission.Work.SSGRoute.ZDataTwo.gesEscapeTrivialPairTwo
import Submission.Work.SSGRoute.H9.NarrowMu2
import Submission.Work.SSGRoute.H9.NarrowOpen
import Submission.Work.SSGRoute.H9.NarrowFiniteIndex
import Submission.Work.SSGRoute.H9.NarrowCorrection
import Submission.Work.H9Narrow.orthogonality_narrow_L2K
import Submission.Work.SSGRoute.GrunwaldEscapeCore.escape_prime_orthogonality
import Submission.Work.SSGRoute.step4_y_escape_v2.GesUFacts
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.H9

open _root_.SSGRoute
open scoped Pointwise
open NumberField IsDedekindDomain
open NK.GlobalCFT

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 800000

/-- **The trichotomy used by the (narrow) orthogonality, from the two-disjunct hypothesis.**  If
at a place `A ∈ T` either the local datum `h A` vanishes on the whole local group, or `A` splits
completely in `N`, then the same place satisfies the trichotomy of
`Work.H9Narrow.orthogonality_narrow_L2K`: the second case hands the local group to the fixing
subgroup of `N`, so every additive character vanishing there vanishes on the local group. -/
lemma horth_trichotomy_of_split {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K N : IntermediateField k Ω) (T : Finset (ValuationSubring Ω))
    (h : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod 2)
    (horth : ∀ A ∈ T,
      (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A σ = 0) ∨
      SSGRoute.IsSplitIn k N A) :
    ∀ A ∈ T,
      (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A σ = 0) ∨
      (∀ χ : (Ω ≃ₐ[k] Ω) → ZMod 2,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
        (∀ σ ∈ N.fixingSubgroup, χ σ = 0) →
        ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, χ σ = 0) ∨
      ((∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → h A σ = 0) ∧
        ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod 2,
          (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
          (∀ σ ∈ N.fixingSubgroup, χ σ = 0) →
          ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → χ σ = 0) := by
  intro A hA
  rcases horth A hA with h1 | h2
  · exact Or.inl h1
  · refine Or.inr (Or.inl ?_)
    intro χ _ hχN σ hσ
    exact hχN σ (h2 (Subgroup.mem_inf.mp hσ).1)

theorem mu2EscapeCorrection_proved (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, Work.SSGRoute.gesKConj K A B → A = B)
    (hTcov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (B.valuation (2 : Ω) < 1 ∨
        ∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ N.fixingSubgroup) →
      ∃ A ∈ T, Work.SSGRoute.gesKConj K A B)
    (g : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hg : ∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, g (x * y) = g x + g y)
    (hgc : SSGRoute.IsLocConstOn K.fixingSubgroup g)
    (hgram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) → ¬ SSGRoute.IsSplitIn k N B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → g σ = 0)
    (h : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hh : ∀ A ∈ T, ∀ x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      ∀ y ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A (x * y) = h A x + h A y)
    (hhc : ∀ A ∈ T, ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      ∀ x ∈ U, x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup → h A x = 0)
    (horth : ∀ A ∈ T,
      (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A σ = 0) ∨ SSGRoute.IsSplitIn k N A)
    (hinertia : ∀ A ∈ T, ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ →
      g σ + h A σ = 0)
    (hginf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → g c = 0)
    (hhinf : ∀ A ∈ T, ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → h A c = 0) :
    ∀ a : (↥K)ˣ,
      (∀ A ∈ T, ∀ σ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
        g (σ : Ω ≃ₐ[k] Ω) + h A (σ : Ω ≃ₐ[k] Ω) =
          Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ a
            (Work.SSGRoute.gesLocalToGalK K σ)) →
      ∃ (Q : ValuationSubring Ω) (b : (↥K)ˣ),
        SSGRoute.IsFinPlace k Q ∧ SSGRoute.IsSplitIn k N Q ∧
        (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A Q) ∧
        (∀ A ∈ T, ∀ σ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
          Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ b
              (Work.SSGRoute.gesLocalToGalK K σ) =
            Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ a
              (Work.SSGRoute.gesLocalToGalK K σ)) ∧
        (∀ (c : Ω ≃ₐ[k] Ω) (hc : c ∈ K.fixingSubgroup), c ^ 2 = 1 →
          Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ b
            (Work.SSGRoute.gesGalKOfFixing K c hc) = 0) ∧
        (∀ (B : ValuationSubring Ω), SSGRoute.IsFinPlace k B →
          (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) →
          (¬ Work.SSGRoute.gesKConj K Q B) →
          ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup), SSGRoute.IsInertia k B σ →
            Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ b
              (Work.SSGRoute.gesGalKOfFixing K σ hσ) = 0) := by
  intro a ha
  classical
  haveI hAlgClosed : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  haveI hNumK : NumberField ↥K := NumberField.of_module_finite k ↥K
  -- ## A. the sign adjustment: replace `a` by `a * s`, which kills the involutions
  obtain ⟨s, hs0, hspos⟩ :=
    Work.SSGRoute.ZDataTwo.signAdjustment_mu2 k Ω K ζ hζ T hTfin a
  set a' : (↥K)ˣ := a * s with ha'def
  have ha'_local : ∀ A ∈ T, ∀ σ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
      g (σ : Ω ≃ₐ[k] Ω) + h A (σ : Ω ≃ₐ[k] Ω) =
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ a'
          (Work.SSGRoute.gesLocalToGalK K σ) := by
    intro A hA σ
    have hadd := Work.SSGRoute.ZConstruction.kummerCharZMod_add (p := 2) (K := K) (Ω := Ω)
      (ζ := ζ) (hζ := hζ) a s (Work.SSGRoute.gesLocalToGalK K σ)
    rw [ha'def, hadd, hs0 A hA σ, add_zero]
    exact ha A hA σ
  have hapos : ∀ (c : Ω ≃ₐ[k] Ω) (hc : c ∈ K.fixingSubgroup), c ^ 2 = 1 →
      Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ a'
        (Work.SSGRoute.gesGalKOfFixing K c hc) = 0 := by
    intro c hc hc2
    rw [ha'def]
    exact hspos c hc hc2
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
  have hT'p : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → B.valuation (2 : Ω) < 1 →
      ∃ 𝔭 ∈ T',
        B.comap (algebraMap ↥K Ω) =
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
  -- ## 1. the field `N' = baseChange K N` over `↥K`
  let N' : IntermediateField ↥K Ω := EscapeCoreLib.baseChange K N hKN
  have hN' : (N' : Set Ω) = (N : Set Ω) := by
    ext x
    exact EscapeCoreLib.mem_baseChange K N hKN
  haveI hN'fdk : FiniteDimensional k ↥N' := EscapeCoreLib.finiteDimensional_baseChange K N hKN
  haveI hN'fd : FiniteDimensional ↥K ↥N' :=
    Module.Finite.of_restrictScalars_finite k ↥K ↥N'
  haveI hN'gal : IsGalois ↥K ↥N' := EscapeCoreLib.isGalois_baseChange K N hKN
  haveI hN'nf : NumberField ↥N' := NumberField.of_module_finite ↥K ↥N'
  -- ## 2. the class field `M` of `U' = narrowGesU ↥K 2 T' ⊔ C_↥K²`
  let U' : Subgroup (IdeleClassGroup ↥K) :=
    Work.SSGRoute.H9.narrowGesU ↥K 2 T' ⊔
      Work.SSGRoute.EscapeCoreLib.pPowSubgroup 2 (IdeleClassGroup ↥K)
  obtain ⟨M, hMfd, hMgal, hMnf, hMcomm, hMnorm⟩ :=
    GrunwaldEscapeCore.exists_abelian_classField_inside K U'
      (Work.SSGRoute.step4_y_escape_v2.finiteIndex_of_le (H := Work.SSGRoute.H9.narrowGesU ↥K 2 T')
        (K := U') le_sup_left (Work.SSGRoute.H9.narrowGesU_finiteIndex 2 T'))
      (Work.SSGRoute.step4_y_escape_v2.isOpen_of_le_isOpen
        (H := Work.SSGRoute.H9.narrowGesU ↥K 2 T') (K := U') le_sup_left
        (Work.SSGRoute.H9.isOpen_narrowGesU 2 (by norm_num) T'))
  haveI : FiniteDimensional ↥K M := hMfd
  haveI : IsGalois ↥K M := hMgal
  haveI : NumberField ↥M := hMnf
  haveI : IsMulCommutative (↥M ≃ₐ[↥K] ↥M) := hMcomm
  -- ## 3. the (narrow) orthogonality, in the surviving case `L₂ = K`
  let 𝔡 : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) ↥K :=
    Work.SSGRoute.tFreePart T' a'
  have horth_mem : IdeleClassGroup.mk ↥K (NK.NUV2.RouteB.RayModulus.fracIdele 𝔡) ∈
      U' ⊔ Idele.normClassSubgroup ↥K ↥N' := by
    have hraw := Work.H9Narrow.orthogonality_narrow_L2K k Ω K ζ hζ N hKN T hTfin hTdisj hTcov
      g hg hgc hgram hginf h hh hhc (horth_trichotomy_of_split K N T h horth) hinertia
      T' hTbelow hT'above M hMnorm N' hN' a' ha'_local hapos
    rw [hMnorm] at hraw
    exact hraw
  -- ## 4. the escape prime, `Q` split completely in `N`
  obtain ⟨Q, 𝔮, hQfin, hQsplit, h𝔮T', hQnotT, hQcomap, hQmem⟩ :=
    GrunwaldEscapeCore.escape_prime_orthogonality K M U' hMnorm N N' hKN hN' T hTfin T' hTbelow
      (IdeleClassGroup.mk ↥K (NK.NUV2.RouteB.RayModulus.fracIdele 𝔡)) horth_mem
  -- ## 5. the fractional ideal `𝔵 = 𝔡 · (𝔮)`
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
          (a' : ↥K))) := by
    intro q
    rw [Work.SSGRoute.tFreePart_count]
    by_cases hq : q ∈ T'
    · rw [Work.SSGRoute.tFreeExp_of_mem T' a' hq, if_pos hq]
    · rw [Work.SSGRoute.tFreeExp_of_not_mem T' a' hq, if_neg hq,
        ← Idele.idealOf_principalIdele, Idele.count_idealOf]
  have h𝔡0 : 𝔡 ≠ 0 := by
    change Work.SSGRoute.tFreePart T' a' ≠ 0
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
            (a' : ↥K)) := by
    intro 𝔭 h𝔭T h𝔭𝔮
    rw [hcount𝔵 𝔭, if_neg h𝔭𝔮, add_zero, hcount𝔡 𝔭, if_neg h𝔭T]
  have h𝔵𝔮 : FractionalIdeal.count ↥K 𝔮 𝔵 =
      FractionalIdeal.count ↥K 𝔮
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          (a' : ↥K)) + 1 := by
    rw [hcount𝔵 𝔮, if_pos rfl, hcount𝔡 𝔮, if_neg h𝔮T']
  -- ## 6. the membership of `𝔵` in `U'`
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
          (Work.SSGRoute.tFreePart T' a')) :=
      rfl
    rw [hfrac, map_mul, hC]
    simpa only [mul_comm] using hQmem
  -- ## 7. the correction, with the narrow read-off
  obtain ⟨b, hagree, hesc, hinv⟩ :=
    Work.SSGRoute.H9.correctionFromPrime_narrow k Ω K ζ hζ T hTfin T' hTbelow hT'p a' hapos 𝔵
      h𝔵T 𝔮 h𝔵div h𝔵𝔮 hmem
  -- ## 8. the assembly
  refine ⟨Q, b, hQfin, hQsplit, hQnotT, ?_, ?_, ?_⟩
  · -- the prescribed local datum at `T`
    intro A hA σ
    rw [hagree A hA σ, ← ha'_local A hA σ]
    exact ha A hA σ
  · -- the correction kills the involutions
    intro c hc hc2
    exact hinv c hc hc2
  · -- unramified outside the classes of `T` and of `Q`
    intro B hBfin hBnotT hBnotQ σ hσ hI
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

end Work.SSGRoute.H9
