import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.GrunwaldEscapeCore.Vocab
import Submission.Work.SSGRoute.GrunwaldEscapeCore.escape_vocab
import Submission.Work.SSGRoute.GrunwaldEscapeCore.orthogonality_L2K
import Submission.Work.SSGRoute.GrunwaldEscapeCore.escape_prime_orthogonality
import Submission.Work.SSGRoute.GrunwaldEscapeCore.gesEscapePrimeSplit
import Submission.Work.SSGRoute.GrunwaldEscapeCore.gesCorrectionFromPrime
import Submission.Work.SSGRoute.EscapeCoreLib.baseChange_over_K
import Submission.Work.SSGRoute.step4_y_escape_v2.GesUFacts
import Submission.Work.SSGRoute.step4_y_escape_v2.CorrectionSupPow
import Submission.Work.SSGRoute.step4_y_escape_v2.Orthogonality
import Submission.Work.SSGRoute.step4_y_escape_v2.RayClass
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The escape correction (the arithmetic core of Grünwald with escape)

This module proves `Work.SSGRoute.GrunwaldEscapeCore.escape_correction`: given an element
`a ∈ Kˣ` whose Kummer character realises the local datum `g + h A` at every place of `T`, there is

* a finite place `Q` of `Ω`, completely split in `N`, not `K`-conjugate to any element of `T`;
* an element `b ∈ Kˣ` with the *same* local data at `T` (so its Kummer character realises the same
  datum), whose Kummer character vanishes on the inertia of every place outside the
  `K`-conjugates of `T` and of `Q`.

The route is the design's, and is **self-contained**: it does not pass through the general node N2
(`GrunwaldEscapeCore/core.lean`), whose correction statement is FALSE as frozen (see
`Submission/Work/SSGRoute/COUNTEREXAMPLE_N2_grunwald_escape_relative.md`).  Concretely:

1. `U' := gesU ↥K p T' ⊔ C_↥K^p` is an open finite-index subgroup of `C_↥K`, and `M` is its abelian
   class field inside `Ω` (`exists_abelian_classField_inside`);
2. **the orthogonality** `mk (fracIdele (tFreePart T' a)) ∈ U' ⊔ N_{N'/↥K}C_{N'}` for
   `N' = baseChange K N`, proved in `GrunwaldEscapeCore/orthogonality_L2K.lean`
   (`orthogonality_L2K`, axiom-clean).  This is the surviving true case `L₂ = K` of the general
   node: with `L₂ = K` the second orthogonality hypothesis of the general node is vacuous and the
   second disjunct of the first is exactly `IsSplitIn k N A`;
3. the escape prime with the membership `mk(ideleOfPrime 𝔮) · x ∈ U'` and `Q` split completely in
   `N` (`GrunwaldEscapeCore/escape_prime_orthogonality.lean`, axiom-clean);
4. reading off `𝔵 = 𝔡·(𝔮)` gives `b := a/γ` with the required properties
   (`step4_y_escape_v2.correctionFromPrime_supPow`, axiom-clean).
-/

namespace Work.SSGRoute.GrunwaldEscapeCore

open _root_.SSGRoute
open scoped Pointwise
open NumberField IsDedekindDomain
open NK.GlobalCFT

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 800000

theorem escape_correction (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (hKimag : p = 2 → ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → c = 1)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, Work.SSGRoute.gesKConj K A B → A = B)
    (hTcov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (B.valuation (p : Ω) < 1 ∨
        (∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ N.fixingSubgroup)) →
      ∃ A ∈ T, Work.SSGRoute.gesKConj K A B)
    (g : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hg : ∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, g (x * y) = g x + g y)
    (hgc : SSGRoute.IsLocConstOn K.fixingSubgroup g)
    (hgram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) → ¬ SSGRoute.IsSplitIn k N B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → g σ = 0)
    (h : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p)
    (hh : ∀ A ∈ T, ∀ x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      ∀ y ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A (x * y) = h A x + h A y)
    (hhc : ∀ A ∈ T, ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      ∀ x ∈ U, x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup → h A x = 0)
    (horth : ∀ A ∈ T,
      (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A σ = 0) ∨
      SSGRoute.IsSplitIn k N A)
    (a : (↥K)ˣ)
    (ha : ∀ A ∈ T, ∀ σ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
      g (σ : Ω ≃ₐ[k] Ω) + h A (σ : Ω ≃ₐ[k] Ω) =
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ a
          (Work.SSGRoute.gesLocalToGalK K σ)) :
    ∃ (Q : ValuationSubring Ω) (b : (↥K)ˣ),
      SSGRoute.IsFinPlace k Q ∧ SSGRoute.IsSplitIn k N Q ∧
      (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A Q) ∧
      (∀ A ∈ T, ∀ σ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
        g (σ : Ω ≃ₐ[k] Ω) + h A (σ : Ω ≃ₐ[k] Ω) =
          Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ b
            (Work.SSGRoute.gesLocalToGalK K σ)) ∧
      (∀ (B : ValuationSubring Ω), SSGRoute.IsFinPlace k B →
        (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) → ¬ Work.SSGRoute.gesKConj K Q B →
        ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup), SSGRoute.IsInertia k B σ →
          Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ b
            (Work.SSGRoute.gesGalKOfFixing K σ hσ) = 0) := by
  classical
  haveI hNumK : NumberField ↥K := NumberField.of_module_finite k ↥K
  -- ## 0. the primes `T'` of `↥K` below the places of `T`
  let primeBelow : (A : {A // A ∈ T}) → NK.Chebotarev.PrimeIdeal ↥K :=
    fun A => (exists_primeIdeal_of_comap_ne_top K A.1 (hTfin A.1 A.2)).choose
  have hprimeBelow : ∀ A : {A // A ∈ T},
      A.1.comap (algebraMap ↥K Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K (primeBelow A) :=
    fun A => (exists_primeIdeal_of_comap_ne_top K A.1 (hTfin A.1 A.2)).choose_spec
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
  -- the places over `p` lie in the classes of `T` (`hTcov`), so they lie over `T'`
  have hT'p : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → B.valuation (p : Ω) < 1 →
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
    rw [(gesSmulEqOfCoeEq K hcoe A).symm]
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
  -- ## 2. the class field `M` of `U' = gesU ↥K p T' ⊔ C_↥K^p`
  let U' : Subgroup (IdeleClassGroup ↥K) :=
    GrunwaldEscapeCore.gesU ↥K p T' ⊔ EscapeCoreLib.pPowSubgroup p (IdeleClassGroup ↥K)
  obtain ⟨M, hMfd, hMgal, hMnf, hMcomm, hMnorm⟩ :=
    exists_abelian_classField_inside K U'
      (Work.SSGRoute.step4_y_escape_v2.finiteIndex_gesU_sup_pPow (p := p) (K := ↥K) T')
      (Work.SSGRoute.step4_y_escape_v2.isOpen_gesU_sup_pPow p T')
  haveI : FiniteDimensional ↥K M := hMfd
  haveI : IsGalois ↥K M := hMgal
  haveI : NumberField ↥M := hMnf
  haveI : IsMulCommutative (↥M ≃ₐ[↥K] ↥M) := hMcomm
  -- ## 3. the orthogonality, in the surviving case `L₂ = K`
  let 𝔡 : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) ↥K :=
    Work.SSGRoute.tFreePart T' a
  have horth_mem : IdeleClassGroup.mk ↥K (NK.NUV2.RouteB.RayModulus.fracIdele 𝔡) ∈
      U' ⊔ Idele.normClassSubgroup ↥K ↥N' := by
    have hraw := orthogonality_L2K p hp k Ω K ζ hζ hKimag N hKN T hTfin hTdisj hTcov g hg hgc
      hgram h hh hhc horth T' hTbelow hT'above M hMnorm N' hN' a ha
    rw [hMnorm] at hraw
    exact hraw
  -- ## 4. the escape prime, `Q` split completely in `N`
  obtain ⟨Q, 𝔮, hQfin, hQsplit, h𝔮T', hQnotT, hQcomap, hQmem⟩ :=
    escape_prime_orthogonality K M U' hMnorm N N' hKN hN' T hTfin T' hTbelow
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
  have h𝔵𝔮 : 𝔮 ∉ T' → FractionalIdeal.count ↥K 𝔮 𝔵 =
      FractionalIdeal.count ↥K 𝔮
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          (a : ↥K)) + 1 := by
    intro h𝔮T
    rw [hcount𝔵 𝔮, if_pos rfl, hcount𝔡 𝔮, if_neg h𝔮T]
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
        IdeleClassGroup.mk ↥K (NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart T' a)) :=
      rfl
    rw [hfrac, map_mul, hC]
    simpa only [mul_comm] using hQmem
  -- ## 7. the correction
  obtain ⟨b, hagree, hesc⟩ :=
    Work.SSGRoute.step4_y_escape_v2.correctionFromPrime_supPow p k Ω K ζ hζ T hTfin T' hTbelow
      hT'p a 𝔵 h𝔵T 𝔮 h𝔵div h𝔵𝔮 hmem
  refine ⟨Q, b, hQfin, hQsplit, hQnotT, ?_, ?_⟩
  · intro A hA σ
    rw [← hagree A hA σ]
    exact ha A hA σ
  · intro B hBfin hBnotT hBnotQ σ hσ hI
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

end Work.SSGRoute.GrunwaldEscapeCore
