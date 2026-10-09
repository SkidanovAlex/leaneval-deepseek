import Mathlib
import Submission.Work.SSGRoute.ZDataTwo.mu2KummerFirstElement
import Submission.Work.SSGRoute.GrunwaldEscapeCore.gesCorrectionFromPrime
import Submission.Work.SSGRoute.GrunwaldEscapeCore.gesEscapePrimeSplit
import Submission.Work.SSGRoute.ZSplit.SWFourOddKummer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataTwo

open _root_.SSGRoute
open NumberField IsDedekindDomain
open scoped Pointwise

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-- **Grünwald with escape, the case `L₁ = L₂ = K`, with no hypothesis on the involutions.**

This is `Work.SSGRoute.GrunwaldEscapeCore.gesEscapeTrivialPair` with its hypothesis
`hKimag : p = 2 → ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → c = 1` deleted: the odd-`p` escape lane
carries it, but it is *false* at `p = 2` whenever `K` has a quadratic subextension, and the proof
of `gesEscapeTrivialPair` never uses it.  The only place where it entered was the call to the
first-element theorem, and here the hypothesis-free version
`Work.SSGRoute.GrunwaldEscapeCore.kummerFirstElement_noImag`
(`Submission/Work/SSGRoute/ZDataTwo/mu2KummerFirstElement.lean`) is used instead.

Given a finite set `T` of finite places of `Ω` (one place per `K`-prime) covering the places above
`p`, and additive, locally constant data `h A` on the local groups `decomp k A ⊓ G_K` (`A ∈ T`),
there are an additive, locally constant `z : G_k → ZMod p` realising the data at every `A ∈ T` and a
finite place `Q`, completely split in `K` over `k`, not `K`-conjugate to any element of `T`, such
that `z` vanishes on the inertia of every finite place `B` that is neither `K`-conjugate to some
`A ∈ T` nor to `Q`. -/
theorem gesEscapeTrivialPairTwo (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, Work.SSGRoute.gesKConj K A B → A = B)
    (hTcov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → B.valuation (p : Ω) < 1 →
      ∃ A ∈ T, Work.SSGRoute.gesKConj K A B)
    (h : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p)
    (hh : ∀ A ∈ T, ∀ x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      ∀ y ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A (x * y) = h A x + h A y)
    (hhc : ∀ A ∈ T, ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      ∀ x ∈ U, x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup → h A x = 0) :
    ∃ (z : (Ω ≃ₐ[k] Ω) → ZMod p) (Q : ValuationSubring Ω),
      SSGRoute.IsFinPlace k Q ∧ SSGRoute.IsSplitIn k K Q ∧
      (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A Q) ∧
      (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, z (x * y) = z x + z y) ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ A ∈ T, ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, z σ = h A σ) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) →
        ¬ Work.SSGRoute.gesKConj K Q B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) := by
  classical
  haveI hNumK : NumberField ↥K := NumberField.of_module_finite k ↥K
  set ζK : ↥K := ⟨ζ, hζK⟩ with hζKdef
  have hζK' : IsPrimitiveRoot ζK p := ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ
  -- ## 0. The primes of `↥K` below the places of `T`
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
  -- ## 1. The `K`-prime of a finite place of `Ω`
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
  have hT'p : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → B.valuation (p : Ω) < 1 →
      ∃ 𝔭 ∈ T',
        B.comap (algebraMap ↥K Ω) =
          IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 := by
    intro B hB hp
    obtain ⟨A, hA, τ, hτ, hτA⟩ := hTcov B hB hp
    obtain ⟨𝔭, h𝔭T', h𝔭A⟩ := hT'below A hA
    refine ⟨𝔭, h𝔭T', ?_⟩
    rw [← h𝔭A, ← hτA]
    have hcoe : ⇑((IntermediateField.fixingSubgroupEquiv K) ⟨τ, hτ⟩) = ⇑τ := funext fun _ => rfl
    rw [(Work.SSGRoute.GrunwaldEscapeCore.gesSmulEqOfCoeEq K hcoe A).symm]
    exact Commons.NumberTheory.NumberField.Valuation.comap_smul_algebraMap A _
  -- ## 2. Grünwald + Kummer: the first element `a` (no hypothesis on the involutions)
  obtain ⟨a, ha⟩ :=
    Work.SSGRoute.GrunwaldEscapeCore.kummerFirstElement_noImag p k Ω K ζK hζK' T hTfin hTdisj
      (0 : (Ω ≃ₐ[k] Ω) → ZMod p) (fun x hx y hy => by simp)
      ⟨⊤, by rw [Subgroup.coe_top]; exact isOpen_univ, fun g hg u hu huH => rfl⟩ h hh hhc
  -- ## 3. The `T'`-free part of the divisor of `a`
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
  -- ## 4. Čebotarev: the escape prime
  obtain ⟨Q, 𝔮, hQfin, hQsplit, h𝔮T', hQcomap, hQnotT, hclass⟩ :=
    Work.SSGRoute.GrunwaldEscapeCore.gesEscapePrimeSplit p k Ω K T' T hTfin hT'below
      (NK.GlobalCFT.IdeleClassGroup.mk ↥K (NK.NUV2.RouteB.RayModulus.fracIdele 𝔡))
  -- ## 5. The fractional ideal `𝔵 = 𝔡 · (𝔮)`
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
      Work.SSGRoute.GrunwaldEscapeCore.gesU ↥K p T' := by
    have hfrac : NK.NUV2.RouteB.RayModulus.fracIdele 𝔵 =
        NK.NUV2.RouteB.RayModulus.fracIdele 𝔡 * NK.HeckeL.ideleOfPrime ↥K 𝔮 := by
      rw [NK.NUV2.RouteB.RayModulus.fracIdele_mul (NK.GlobalCFT.Idele.idealOf_ne_zero y𝔡)
        (NK.GlobalCFT.Idele.idealOf_ne_zero (NK.HeckeL.ideleOfPrime ↥K 𝔮)), hfrac𝔮]
    rw [hfrac, map_mul]
    simpa only [mul_comm] using hclass
  -- ## 6. The correction: an element with the same local data and one escape prime
  obtain ⟨b, hagree, hunr⟩ :=
    Work.SSGRoute.GrunwaldEscapeCore.gesCorrectionFromPrime p k Ω K ζK hζK' T hTfin T' hT'below
      hT'p a 𝔵 h𝔵T 𝔮 h𝔵div h𝔵𝔮 hmem
  -- ## 7. The class realising the datum
  refine ⟨ZSplit.nodeKummerCocharZMod K ζ hζK hζ b, Q, hQfin, hQsplit, hQnotT, ?_, ?_, ?_, ?_⟩
  · exact ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ b
  · exact ZSplit.nodeKummerCocharZMod_locConst K ζ hζK hζ b
  · intro A hA σ hσ
    have hσK : (σ : Ω ≃ₐ[k] Ω) ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp hσ).2
    rw [ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK) (hζ := hζ) (β := b) hσK]
    have hto : (IntermediateField.fixingSubgroupEquiv K) ⟨(σ : Ω ≃ₐ[k] Ω), hσK⟩ =
        Work.SSGRoute.gesLocalToGalK K ⟨σ, hσ⟩ := rfl
    rw [hto, ← hagree A hA ⟨σ, hσ⟩]
    simpa using (ha A hA ⟨σ, hσ⟩).symm
  · intro B hB hnotT hnotQ σ hσ hI
    rw [ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK) (hζ := hζ) (β := b) hσ]
    have hto : (IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩ =
        Work.SSGRoute.gesGalKOfFixing K σ hσ := rfl
    rw [hto]
    refine hunr B hB ?_ ?_ σ hσ hI
    · intro 𝔭 h𝔭 heq
      obtain ⟨A, hA, hAcomap⟩ := hT'above 𝔭 h𝔭
      have hcomapK : A.comap (algebraMap ↥K Ω) = B.comap (algebraMap ↥K Ω) := by
        rw [hAcomap, heq]
      exact hnotT A hA (Work.SSGRoute.exists_mem_fixingSubgroup_smul_eq_of_comap_eq K
        (hcomapK_ne_top (hTfin A hA)) hcomapK)
    · intro heq
      have hcomapK : Q.comap (algebraMap ↥K Ω) = B.comap (algebraMap ↥K Ω) := by
        rw [hQcomap, heq]
      exact hnotQ (Work.SSGRoute.exists_mem_fixingSubgroup_smul_eq_of_comap_eq K
        (hcomapK_ne_top hQfin) hcomapK)

end Work.SSGRoute.ZDataTwo
