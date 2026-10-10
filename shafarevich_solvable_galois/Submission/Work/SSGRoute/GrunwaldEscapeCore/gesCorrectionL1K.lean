import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.GrunwaldEscapeCore.L1Korth.alpha_fixes_L1K
import Submission.Work.GrunwaldEscapeCore.grunwald_escape_relative_L1K
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The escape correction at `L₁ = K`, in Kummer-character form

The proof assembles the correction step from four pieces of the workspace (all axiom-clean):

1. **the class-field data** (`SSG8Escape.class_field_data_ssg8`): for the open finite-index subgroup
   `U' = gesU_{T'} ⊔ (p-th powers)` of `C_↥K` there is a finite abelian `M / ↥K` inside `Ω` with
   `N_{M/↥K}C_M = U'`, together with the idèlic Artin map `art` with kernel
   `N_{M/↥K}𝕀_M ⊔ ↥Kˣ` and the Frobenius normalisation at every unramified prime;
2. **the orthogonality** (`Work.GrunwaldEscapeCore.L1Korth.alpha_fixes_L1K`): the Artin symbol
   `α = art(𝔡)` of the `T'`-free part `𝔡 = tFreePart T' a` of the divisor of `a` fixes `M ⊓ L`
   pointwise — this is where the two disjuncts of `horth` and the Kummer dictionary are consumed;
3. **the escape realisation** (`Work.GrunwaldEscapeCore.escape_L1K_of_alpha_fixes`): from the
   orthogonality it produces the additive, locally constant class `z` agreeing with the datum `h`
   on the local groups of `T` at a place `Q` split in `L` and outside the `↥K`-classes of `T`, with
   `z` unramified away from the classes of `T` and of `Q`;
4. **Kummer theory over `↥K`** (`ZSplit.exists_kummerCocharZMod_of_additive_locConst`): every
   additive, locally constant class on `K.fixingSubgroup` is the Kummer character of an element of
   `↥Kˣ` — this turns `z` into the honest element `b` of the statement, which is the *only* place
   where the `b`-form (rather than the additive `z`-form) of the correction is used.
-/

namespace Work.SSGRoute.GrunwaldEscapeCore

open scoped Pointwise

/-- **The Kummer correspondence for additive, locally constant classes on `K.fixingSubgroup`.**
Every additive class `z` on `K.fixingSubgroup` which is locally constant is the Kummer character of
some `β ∈ ↥Kˣ`, evaluated at the level-`K` automorphisms `gesGalKOfFixing`.

This is `Work.SSGRoute.ZSplit.exists_kummerCocharZMod_of_additive_locConst` transported to the
`↥K`-side (the two definitions of the level-`K` automorphism of an element of `K.fixingSubgroup`,
`ZSplit.nodeKummerCocharZMod_apply`'s `fixingSubgroupEquiv` and `gesGalKOfFixing`, are equal by
`rfl`). -/
theorem exists_gesKummerCharZMod_of_additive_locConst (p : ℕ) [Fact p.Prime] (k Ω : Type)
    [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (z : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hz : ∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, z (x * y) = z x + z y)
    (hzc : SSGRoute.IsLocConstOn K.fixingSubgroup z) :
    ∃ β : (↥K)ˣ, ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup),
      z σ = Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ β
        (Work.SSGRoute.gesGalKOfFixing K σ hσ) := by
  -- the primitive `p`-th root of unity, viewed in `Ω`
  set ζΩ : Ω := (ζ : Ω) with hζΩdef
  have hζΩK : ζΩ ∈ K := ζ.2
  have hζΩ : IsPrimitiveRoot ζΩ p :=
    hζ.map_of_injective (algebraMap ↥K Ω).injective
  obtain ⟨β, hβ⟩ :=
    Work.SSGRoute.ZSplit.exists_kummerCocharZMod_of_additive_locConst
      p k Ω K ζΩ hζΩK hζΩ z hz hzc
  refine ⟨β, ?_⟩
  intro σ hσ
  rw [hβ σ hσ,
    Work.SSGRoute.ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζΩ) (hζK := hζΩK)
      (hζ := hζΩ) (β := β) hσ]
  rfl

theorem gesCorrectionL1K (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (hKimag : p = 2 → ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → c = 1)
    (L : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L] (hKL : K ≤ L)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, Work.SSGRoute.gesKConj K A B → A = B)
    (hTcov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (B.valuation (p : Ω) < 1 ∨
        (∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ L.fixingSubgroup)) →
      ∃ A ∈ T, Work.SSGRoute.gesKConj K A B)
    (h : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p)
    (hh : ∀ A ∈ T, ∀ x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      ∀ y ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A (x * y) = h A x + h A y)
    (hhc : ∀ A ∈ T, ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      ∀ x ∈ U, x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup → h A x = 0)
    (horth : ∀ A ∈ T,
      (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A σ = 0) ∨
      (∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
        (∀ σ ∈ L.fixingSubgroup, χ σ = 0) →
        ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, χ σ = 0))
    (a : (↥K)ˣ)
    (ha : ∀ A ∈ T, ∀ σ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
      h A (σ : Ω ≃ₐ[k] Ω) =
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ a
          (Work.SSGRoute.gesLocalToGalK K σ)) :
    ∃ (Q : ValuationSubring Ω) (b : (↥K)ˣ),
      SSGRoute.IsFinPlace k Q ∧ SSGRoute.IsSplitIn k L Q ∧
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
  -- ## the `↥K`-primes below the places of `T`
  let primeBelow : (A : {A // A ∈ T}) → NK.Chebotarev.PrimeIdeal ↥K :=
    fun A => (GrunwaldEscapeCore.exists_primeIdeal_of_comap_ne_top K A.1 (hTfin A.1 A.2)).choose
  have hprimeBelow : ∀ A : {A // A ∈ T},
      A.1.comap (algebraMap ↥K Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K (primeBelow A) :=
    fun A => (GrunwaldEscapeCore.exists_primeIdeal_of_comap_ne_top K A.1 (hTfin A.1 A.2)).choose_spec
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
  -- ## the class-field data of `U' = gesU_{T'} ⊔ (p-th powers)`
  obtain ⟨M, hfdM, hgalM, hnfM, hcommM, art, hM, hker, hfrob⟩ :=
    SSG8Escape.class_field_data_ssg8 p k Ω K T'
  haveI : FiniteDimensional ↥K M := hfdM
  haveI : IsGalois ↥K M := hgalM
  haveI : NumberField ↥M := hnfM
  haveI : IsMulCommutative (↥M ≃ₐ[↥K] ↥M) := hcommM
  -- ## the orthogonality: the Artin symbol of `𝔡` fixes `M ⊓ L`
  set α : ↥M ≃ₐ[↥K] ↥M :=
    art (NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart (K := ↥K) T' a)) with hαdef
  have hαfix : ∀ x : ↥M, ((x : Ω) ∈ L) → α x = x :=
    Work.GrunwaldEscapeCore.L1Korth.alpha_fixes_L1K p k Ω K ζ hζ hKimag L hKL T hTfin T'
      hTbelow hT'above (fun A hA B hB h => hTdisj A hA B hB h)
      (fun B hB h => hTcov B hB h) h hh hhc horth a ha M hM art hker hfrob α rfl
  -- ## the escape realisation, in the additive (`z`) form
  set ζΩ : Ω := (ζ : Ω) with hζΩdef
  have hζΩK : ζΩ ∈ K := ζ.2
  have hζΩ : IsPrimitiveRoot ζΩ p :=
    hζ.map_of_injective (algebraMap ↥K Ω).injective
  obtain ⟨z, Q, hQfin, hQsplit, hQnotT, hzadd, hzloc, hzpres, hzunr⟩ :=
    Work.GrunwaldEscapeCore.escape_L1K_of_alpha_fixes p k Ω K ζΩ hζΩ hζΩK hKimag L hKL T hTfin
      (fun A hA B hB h => hTdisj A hA B hB h) (fun B hB h => hTcov B hB h) h hh hhc horth a ha
      T' hTbelow hT'above M hM art hker hfrob α rfl hαfix
  -- ## Kummer theory: `z` is the Kummer character of an element of `↥Kˣ`
  obtain ⟨b, hb⟩ := exists_gesKummerCharZMod_of_additive_locConst p k Ω K ζ hζ z hzadd hzloc
  refine ⟨Q, b, hQfin, hQsplit, ?_, ?_, ?_⟩
  · -- `Q` is not `↥K`-conjugate to any element of `T`
    intro A hA hconj
    obtain ⟨τ, hτ, hτQ⟩ := hconj
    exact hQnotT A hA τ hτ hτQ
  · -- `b` and `a` have the same Kummer character on the local groups of `T`
    intro A hA σ
    have hσK : (σ : Ω ≃ₐ[k] Ω) ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp σ.2).2
    have hzb : Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ b
        (Work.SSGRoute.gesLocalToGalK K σ) = z (σ : Ω ≃ₐ[k] Ω) := by
      have h1 := hb (σ : Ω ≃ₐ[k] Ω) hσK
      have h2 : Work.SSGRoute.gesGalKOfFixing K (σ : Ω ≃ₐ[k] Ω) hσK =
          Work.SSGRoute.gesLocalToGalK K σ := rfl
      rw [h2] at h1
      exact h1.symm
    rw [hzb, hzpres A hA σ σ.2]
    exact ha A hA σ
  · -- `b` is unramified away from the classes of `T` and of the escape place `Q`
    intro B hB hnotT hnotQ σ hσ hI
    have hzb : Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ b
        (Work.SSGRoute.gesGalKOfFixing K σ hσ) = z σ := (hb σ hσ).symm
    rw [hzb]
    exact hzunr B hB (fun A hA τ hτ hτA => hnotT A hA ⟨τ, hτ, hτA⟩)
      (fun τ hτ hτQ => hnotQ ⟨τ, hτ, hτQ⟩) σ hσ hI

end Work.SSGRoute.GrunwaldEscapeCore
