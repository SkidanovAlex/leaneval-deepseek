import Mathlib
import Submission.Work.SSGRoute.GrunwaldEscapeCore.Vocab
import Submission.Work.SSGRoute.ZConstruction.localKummerDictionary
import Submission.Work.SSGRoute.step4_y_escape_v2.Orthogonality
import Submission.Work.SSGRoute.step4_y_escape_v2.GesUFacts
import Submission.Work.SSGRoute.GrunwaldEscapeCore.escape_prime_orthogonality
import Submission.Work.SSGRoute.step4_y_escape_v2.CorrectionSupPow
import Submission.Work.SSGRoute.GrunwaldEscapeCore.grunwald_kummer_first_element
import Submission.Work.SSGRoute.GrunwaldEscapeCore.gesCorrectionFromPrime
import Submission.Work.SSGRoute.GrunwaldEscapeCore.escape_vocab
import Submission.Work.SSGRoute.N2v2.orthogonality_hsplit_proved
import Submission.Work.SSGRoute.EscapeCoreLib.baseChange_over_K
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! # FORK of `GrunwaldEscapeCore.grunwald_escape_correction_hsplit` (my own copy)

This is a verbatim copy of `Submission/Work/SSGRoute/GrunwaldEscapeCore/grunwald_escape_correction_hsplit.lean`
made by the prover of `z_realisation_of_grunwald_v2`, with two changes:

* the theorem is renamed `correction_v3_hsplit` (the original is owned by the escape lane);
* the single `SetLike.ext` in its proof is replaced by `Set.ext`, because in the current
  environment `SetLike.ext` instantiates its `SetLike` argument on `Set Ω` itself and fails to
  synthesize (`failed to synthesize instance SetLike (Set Ω) ?m`), which is why the original file
  no longer elaborates.  With `Set.ext` the proof goes through.

Everything else -- the statement, the proof, the namespace -- is the lane's, whose only gap is
`GrunwaldEscapeCore.orthogonality_hsplit`. -/


/-!
# The Grünwald escape correction, with the `hsplit` repair

This is the statement of `GrunwaldEscapeCore.grunwald_escape_correction` with the extra hypothesis
`hsplit` (every additive `χ` on `K.fixingSubgroup` killing `(L₁ ⊔ L₂).fixingSubgroup` is
`χ₁ + χ₂` with `χᵢ` killing `Lᵢ.fixingSubgroup`), which makes the orthogonality
`Art(𝔡) ∈ Gal(M/(M ⊓ (L₁ ⊔ L₂)))` true — see `NOTE_hsplit_orthogonality_correct.md` for the
closing argument and `step4_y_escape_v2/OrthogonalityV2.lean` for the un-repaired (false) version.

The proof is the assembly of `step4_y_escape_v2/CorrectionAssembly.lean` with the orthogonality
`orthogonality_v2` replaced by the `hsplit` form `orthogonality_hsplit`:

* `grunwald_kummer_first_element` — a single `a ∈ Kˣ` realising the datum;
* `orthogonality_hsplit` — the arithmetic core: `[𝔡] ∈ U' · N_{N'/↥K}C_{N'}`;
* `escapePrime_of_orthogonality` — the escape prime `Q` (completely split in `L₁ ⊔ L₂`) and the
  membership `[𝔮]·[𝔡] ∈ U'`;
* `correctionFromPrime_supPow` — the reading-off, producing `b ∈ Kˣ`.
-/

namespace Work.SSGRoute.GrunwaldEscapeCore

open NumberField
open NK.GlobalCFT
open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

theorem correction_v3_hsplit (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (hKimag : p = 2 → ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → c = 1)
    (L₁ L₂ : IntermediateField k Ω) [FiniteDimensional k L₁] [IsGalois k L₁]
    [FiniteDimensional k L₂] [IsGalois k L₂] (hKL₁ : K ≤ L₁) (hKL₂ : K ≤ L₂)
    (hsplit : ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
      (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
      (∀ δ ∈ (L₁ ⊔ L₂).fixingSubgroup, χ δ = 0) →
      ∃ χ₁ χ₂ : (Ω ≃ₐ[k] Ω) → ZMod p,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ₁ (x * y) = χ₁ x + χ₁ y) ∧
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ₂ (x * y) = χ₂ x + χ₂ y) ∧
        (∀ δ ∈ L₁.fixingSubgroup, χ₁ δ = 0) ∧
        (∀ δ ∈ L₂.fixingSubgroup, χ₂ δ = 0) ∧
        (∀ x ∈ K.fixingSubgroup, χ x = χ₁ x + χ₂ x))
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, Work.SSGRoute.gesKConj K A B → A = B)
    (hTcov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (B.valuation (p : Ω) < 1 ∨
        (∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ L₁.fixingSubgroup) ∨
        (∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ L₂.fixingSubgroup)) →
      ∃ A ∈ T, Work.SSGRoute.gesKConj K A B)
    (g : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hg : ∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, g (x * y) = g x + g y)
    (hgc : SSGRoute.IsLocConstOn K.fixingSubgroup g)
    (hgram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) → ¬ SSGRoute.IsSplitIn k L₁ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → g σ = 0)
    (h : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p)
    (hh : ∀ A ∈ T, ∀ x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      ∀ y ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A (x * y) = h A x + h A y)
    (hhc : ∀ A ∈ T, ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      ∀ x ∈ U, x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup → h A x = 0)
    (horth₁ : ∀ A ∈ T,
      (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A σ = 0) ∨
      (∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
        (∀ σ ∈ L₁.fixingSubgroup, χ σ = 0) →
        ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, χ σ = 0) ∨
      ((∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → h A σ = 0) ∧
        ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
          (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
          (∀ σ ∈ L₁.fixingSubgroup, χ σ = 0) →
          ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → χ σ = 0))
    (horth₂ : ∀ A ∈ T,
      (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, g σ + h A σ = 0) ∨
      (∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
        (∀ σ ∈ L₂.fixingSubgroup, χ σ = 0) →
        ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, χ σ = 0) ∨
      ((∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → g σ + h A σ = 0) ∧
        ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
          (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
          (∀ σ ∈ L₂.fixingSubgroup, χ σ = 0) →
          ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → χ σ = 0))
    (a : (↥K)ˣ)
    (ha : ∀ A ∈ T, ∀ σ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
      g (σ : Ω ≃ₐ[k] Ω) + h A (σ : Ω ≃ₐ[k] Ω) =
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ a
          (Work.SSGRoute.gesLocalToGalK K σ)) :
    ∃ (Q : ValuationSubring Ω) (b : (↥K)ˣ),
      SSGRoute.IsFinPlace k Q ∧ SSGRoute.IsSplitIn k (L₁ ⊔ L₂) Q ∧
      (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A Q) ∧
      (∀ A ∈ T, ∀ σ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ b
            (Work.SSGRoute.gesLocalToGalK K σ) =
          Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ a
            (Work.SSGRoute.gesLocalToGalK K σ)) ∧
      (∀ (B : ValuationSubring Ω), SSGRoute.IsFinPlace k B →
        (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) → ¬ Work.SSGRoute.gesKConj K Q B →
        ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup), SSGRoute.IsInertia k B σ →
          Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ b
            (Work.SSGRoute.gesGalKOfFixing K σ hσ) = 0) := by
  classical
  haveI hNumK : NumberField ↥K := NumberField.of_module_finite k ↥K
  -- ## 0. the primes of `↥K` below the places of `T`
  let primeBelow : (A : {A // A ∈ T}) → NK.Chebotarev.PrimeIdeal ↥K :=
    fun A => (Work.SSGRoute.GrunwaldEscapeCore.exists_primeIdeal_of_comap_ne_top K A.1
      (hTfin A.1 A.2)).choose
  have hprimeBelow : ∀ A : {A // A ∈ T},
      A.1.comap (algebraMap ↥K Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K (primeBelow A) :=
    fun A => (Work.SSGRoute.GrunwaldEscapeCore.exists_primeIdeal_of_comap_ne_top K A.1
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
  -- the places over `p` lie in the classes of `T` (`hTcov`), hence over `T'`
  have hT'p : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → B.valuation (p : Ω) < 1 →
      ∃ 𝔭 ∈ T',
        B.comap (algebraMap ↥K Ω) =
          IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 := by
    intro B hB hp
    obtain ⟨A, hA, hconj⟩ := hTcov B hB (Or.inl hp)
    obtain ⟨𝔭, h𝔭T', h𝔭A⟩ := hTbelow A hA
    obtain ⟨τ, hτ, hτA⟩ := hconj
    refine ⟨𝔭, h𝔭T', ?_⟩
    rw [← h𝔭A, ← hτA]
    have hcoe : ⇑((IntermediateField.fixingSubgroupEquiv K) ⟨τ, hτ⟩) = ⇑τ := funext fun _ => rfl
    rw [(Work.SSGRoute.GrunwaldEscapeCore.gesSmulEqOfCoeEq K hcoe A).symm]
    exact Commons.NumberTheory.NumberField.Valuation.comap_smul_algebraMap A _
  -- ## 1. Grünwald + Kummer: the first element `a`
  obtain ⟨a', ha'⟩ := Work.SSGRoute.GrunwaldEscapeCore.grunwald_kummer_first_element p k Ω K ζ hζ
    hKimag T hTfin hTdisj g hg hgc h hh hhc
  -- ## 2. the field `N' = L₁ ⊔ L₂` over `↥K`
  have hKsup : K ≤ L₁ ⊔ L₂ := hKL₁.trans le_sup_left
  let N' : IntermediateField ↥K Ω := Work.SSGRoute.EscapeCoreLib.baseChange K (L₁ ⊔ L₂) hKsup
  have hN'set : (N' : Set Ω) = ((L₁ ⊔ L₂ : IntermediateField k Ω) : Set Ω) :=
    Set.ext (fun _ => Work.SSGRoute.EscapeCoreLib.mem_baseChange K (L₁ ⊔ L₂) hKsup)
  haveI hN'fin : FiniteDimensional k ↥N' :=
    Work.SSGRoute.EscapeCoreLib.finiteDimensional_baseChange K (L₁ ⊔ L₂) hKsup
  haveI : FiniteDimensional ↥K N' := FiniteDimensional.right k ↥K ↥N'
  haveI : IsGalois ↥K N' :=
    Work.SSGRoute.EscapeCoreLib.isGalois_baseChange K (L₁ ⊔ L₂) hKsup
  haveI hNumN' : NumberField ↥N' := NumberField.of_module_finite ↥K ↥N'
  -- ## 3. the class field `M` of `U' = gesU ↥K p T' ⊔ C_↥K^p`
  let U' : Subgroup (NK.GlobalCFT.IdeleClassGroup ↥K) :=
    Work.SSGRoute.GrunwaldEscapeCore.gesU ↥K p T' ⊔
      Work.SSGRoute.EscapeCoreLib.pPowSubgroup p (NK.GlobalCFT.IdeleClassGroup ↥K)
  obtain ⟨M, hMfd, hMgal, hMnf, hMcomm, hMnorm⟩ :=
    Work.SSGRoute.GrunwaldEscapeCore.exists_abelian_classField_inside K U'
      (Work.SSGRoute.step4_y_escape_v2.finiteIndex_gesU_sup_pPow p T')
      (Work.SSGRoute.step4_y_escape_v2.isOpen_gesU_sup_pPow p T')
  haveI : FiniteDimensional ↥K M := hMfd
  haveI : IsGalois ↥K M := hMgal
  haveI : NumberField ↥M := hMnf
  haveI : IsMulCommutative (↥M ≃ₐ[↥K] ↥M) := hMcomm
  -- ## 4. the orthogonality (the `hsplit` repair of the arithmetic core)
  -- the delegated form of `hsplit` lists the five conjuncts in a different order
  have hsplit' : ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
      (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
      (∀ δ ∈ (L₁ ⊔ L₂).fixingSubgroup, χ δ = 0) →
      ∃ χ₁ χ₂ : (Ω ≃ₐ[k] Ω) → ZMod p,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ₁ (x * y) = χ₁ x + χ₁ y) ∧
        (∀ σ ∈ L₁.fixingSubgroup, χ₁ σ = 0) ∧
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ₂ (x * y) = χ₂ x + χ₂ y) ∧
        (∀ σ ∈ L₂.fixingSubgroup, χ₂ σ = 0) ∧
        ∀ σ ∈ K.fixingSubgroup, χ σ = χ₁ σ + χ₂ σ := by
    intro χ hχ hχ0
    obtain ⟨χ₁, χ₂, hadd1, hadd2, hk1, hk2, hsum⟩ := hsplit χ hχ hχ0
    exact ⟨χ₁, χ₂, hadd1, hk1, hadd2, hk2, hsum⟩
  let 𝔡 : FractionalIdeal (nonZeroDivisors (𝓞 ↥K)) ↥K := Work.SSGRoute.tFreePart T' a'
  have horth : NK.GlobalCFT.IdeleClassGroup.mk ↥K
      (NK.NUV2.RouteB.RayModulus.fracIdele 𝔡) ∈
      U' ⊔ NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥N' :=
    Work.SSGRoute.N2v2.orthogonality_hsplit_proved p k Ω K ζ hζ hKimag L₁ L₂ hKL₁ hKL₂
      T hTfin hTdisj hTcov g hg hgc hgram h hh hhc horth₁ horth₂ hsplit' T' hTbelow hT'above
      N' hN'set a' ha'
  -- ## 5. the escape prime with the membership
  let xC : NK.GlobalCFT.IdeleClassGroup ↥K :=
    NK.GlobalCFT.IdeleClassGroup.mk ↥K (NK.NUV2.RouteB.RayModulus.fracIdele 𝔡)
  obtain ⟨Q, 𝔮, hQfin, hQsomeSplit, h𝔮T', hQnotT, hQcomap, hmember⟩ :=
    Work.SSGRoute.GrunwaldEscapeCore.escape_prime_orthogonality K M U' hMnorm (L₁ ⊔ L₂) N'
      hKsup hN'set T hTfin T' hTbelow xC horth
  -- ## 6. the fractional ideal `𝔵 = 𝔡 · (𝔮)`
  let 𝔵 : FractionalIdeal (nonZeroDivisors (𝓞 ↥K)) ↥K :=
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
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 ↥K)) (a' : ↥K))) := by
    intro q
    rw [Work.SSGRoute.tFreePart_count]
    by_cases hq : q ∈ T'
    · rw [Work.SSGRoute.tFreeExp_of_mem T' a' hq, if_pos hq]
    · rw [Work.SSGRoute.tFreeExp_of_not_mem T' a' hq, if_neg hq,
        ← Idele.idealOf_principalIdele, Idele.count_idealOf]
  have hcount𝔵 : ∀ q, FractionalIdeal.count ↥K q 𝔵 =
      FractionalIdeal.count ↥K q 𝔡 + (if q = 𝔮 then 1 else 0) := by
    intro q
    rw [show 𝔵 = Idele.idealOf (Work.SSGRoute.tFreeIdle T' a') *
          (NK.HeckeL.ideleOfPrime ↥K 𝔮).idealOf from rfl,
      FractionalIdeal.count_mul ↥K q (NK.GlobalCFT.Idele.idealOf_ne_zero _)
        (NK.GlobalCFT.Idele.idealOf_ne_zero _),
      hcount𝔮 q,
      show 𝔡 = Idele.idealOf (Work.SSGRoute.tFreeIdle T' a') from rfl]
  have h𝔵T : ∀ 𝔭 ∈ T', FractionalIdeal.count ↥K 𝔭 𝔵 = 0 := by
    intro 𝔭 h𝔭
    have h𝔭𝔮 : 𝔭 ≠ 𝔮 := fun hEq => h𝔮T' (hEq ▸ h𝔭)
    rw [hcount𝔵 𝔭, if_neg h𝔭𝔮, add_zero, hcount𝔡 𝔭, if_pos h𝔭]
  have h𝔵div : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥K),
      𝔭 ∉ T' → 𝔭 ≠ 𝔮 → FractionalIdeal.count ↥K 𝔭 𝔵 =
        FractionalIdeal.count ↥K 𝔭
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 ↥K)) (a' : ↥K)) := by
    intro 𝔭 h𝔭T h𝔭𝔮
    rw [hcount𝔵 𝔭, if_neg h𝔭𝔮, add_zero, hcount𝔡 𝔭, if_neg h𝔭T]
  have h𝔵𝔮 : 𝔮 ∉ T' → FractionalIdeal.count ↥K 𝔮 𝔵 =
      FractionalIdeal.count ↥K 𝔮
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 ↥K)) (a' : ↥K)) + 1 := by
    intro h𝔮T
    rw [hcount𝔵 𝔮, if_pos rfl, hcount𝔡 𝔮, if_neg h𝔮T]
  -- ## 7. the membership of `𝔵`
  have hfrac𝔮 : NK.NUV2.RouteB.RayModulus.fracIdele
      ((NK.HeckeL.ideleOfPrime ↥K 𝔮).idealOf) = NK.HeckeL.ideleOfPrime ↥K 𝔮 := by
    rw [NK.NUV2.RouteB.RayModulus.fracIdele_idealOf]
    refine (NK.HeckeL.Basic.IdeleFun.congr _ _ ?_).trans rfl
    funext q
    show NK.GlobalCFT.Idele.exp q (NK.GlobalCFT.IdeleClassGroup.ideleOfFun ↥K
      (fun q' => if q' = 𝔮 then 1 else 0) _) = _
    rw [NK.GlobalCFT.IdeleClassGroup.exp_ideleOfFun]
  have hmem : NK.GlobalCFT.IdeleClassGroup.mk ↥K
      (NK.NUV2.RouteB.RayModulus.fracIdele 𝔵) ∈ U' := by
    have hfrac : NK.NUV2.RouteB.RayModulus.fracIdele 𝔵 =
        NK.NUV2.RouteB.RayModulus.fracIdele 𝔡 * NK.HeckeL.ideleOfPrime ↥K 𝔮 := by
      rw [show 𝔵 = Idele.idealOf (Work.SSGRoute.tFreeIdle T' a') *
            (NK.HeckeL.ideleOfPrime ↥K 𝔮).idealOf from rfl,
        NK.NUV2.RouteB.RayModulus.fracIdele_mul (NK.GlobalCFT.Idele.idealOf_ne_zero _)
          (NK.GlobalCFT.Idele.idealOf_ne_zero _), hfrac𝔮,
        show 𝔡 = Idele.idealOf (Work.SSGRoute.tFreeIdle T' a') from rfl]
    have hC : NK.GlobalCFT.IdeleClassGroup.mk ↥K
        (NK.NUV2.RouteB.RayModulus.fracIdele 𝔡) = xC := rfl
    rw [hfrac, map_mul, hC]
    simpa only [mul_comm] using hmember
  -- ## 8. the correction
  obtain ⟨b, hagree, hesc⟩ :=
    Work.SSGRoute.step4_y_escape_v2.correctionFromPrime_supPow p k Ω K ζ hζ T hTfin T' hTbelow
      hT'p a' 𝔵 h𝔵T 𝔮 h𝔵div h𝔵𝔮 hmem
  refine ⟨Q, b, hQfin, hQsomeSplit, hQnotT, ?_, ?_⟩
  · intro A hA σ
    exact (hagree A hA σ).symm.trans ((ha' A hA σ).symm.trans (ha A hA σ))
  · intro B hBfin hBnotT hBnotQ σ hσ hI
    refine hesc B hBfin ?_ ?_ σ hσ hI
    · intro 𝔭 h𝔭 heq
      obtain ⟨A, hA, hAcomap⟩ := hT'above 𝔭 h𝔭
      have hcomapK : A.comap (algebraMap ↥K Ω) = B.comap (algebraMap ↥K Ω) := by
        rw [hAcomap, heq]
      exact hBnotT A hA (exists_mem_fixingSubgroup_smul_eq_of_comap_eq K
        (hcomapK_ne_top (hTfin A hA)) hcomapK)
    · intro heq
      have hcomapK : Q.comap (algebraMap ↥K Ω) = B.comap (algebraMap ↥K Ω) := by
        rw [hQcomap, heq]
      exact hBnotQ (exists_mem_fixingSubgroup_smul_eq_of_comap_eq K
        (hcomapK_ne_top hQfin) hcomapK)

end Work.SSGRoute.GrunwaldEscapeCore
