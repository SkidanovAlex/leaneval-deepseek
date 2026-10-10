import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSG8Escape.class_field_data_ssg8
import Submission.Work.SSG8Escape.escape_prime_ssg8
import Submission.Work.SSGRoute.SSG8Escape.ChebotarevDensityInput
import Submission.Work.SSGRoute.myv2.Heart
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open scoped Pointwise
open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

/-! Guidance from the project lead (the requester):

Shafarevich Step 4, N2 fix (lead design, ssg8/n2_0001/VERDICT.md). The original grunwald_escape_relative was FALSE; v2 adds hsplit: every additive χ on G_K killing G_{L₁⊔L₂} equals χ₁ + χ₂ with χ_i killing G_{L_i}. -/

/-- Grünwald with escape (rank one, `μ_p ⊆ K`), in a pairing-free relative form.

Splitting (`hsplit`): every `ZMod p`-character of `Gal(L₁L₂/K)` is the sum of a character of
`Gal(L₁/K)` and a character of `Gal(L₂/K)`.  Without `hsplit` the statement is false (see
`COUNTEREXAMPLE_N2_grunwald_escape_relative.md`).  `hsplit` holds trivially when `L₁ = K` or
`L₂ = K`, and holds whenever `Gal(L₂/K)` is abelian of exponent `p`
(`additive_split_of_abelian_exponent`).

Conclusion: a global class `z` with the prescribed local data at `T`.  Outside `T`, `z` is ramified
at the `G_K`-conjugates of a single place `Q` at most, and `Q` splits completely in `L₁ ⊔ L₂`. -/
theorem grunwald_escape_relative_v2 (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (hKimag : p = 2 → ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → c = 1)
    (L₁ L₂ : IntermediateField k Ω) [FiniteDimensional k L₁] [IsGalois k L₁]
    [FiniteDimensional k L₂] [IsGalois k L₂] (hKL₁ : K ≤ L₁) (hKL₂ : K ≤ L₂)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, (∃ τ ∈ K.fixingSubgroup, τ • A = B) → A = B)
    (hTcov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (B.valuation (p : Ω) < 1 ∨
        (∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ L₁.fixingSubgroup) ∨
        (∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ L₂.fixingSubgroup)) →
      ∃ A ∈ T, ∃ τ ∈ K.fixingSubgroup, τ • A = B)
    (g : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hg : ∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, g (x * y) = g x + g y)
    (hgc : SSGRoute.IsLocConstOn K.fixingSubgroup g)
    (hgram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ T, ∀ τ ∈ K.fixingSubgroup, τ • A ≠ B) → ¬ SSGRoute.IsSplitIn k L₁ B →
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
    (hsplit : ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
      (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
      (∀ σ ∈ (L₁ ⊔ L₂).fixingSubgroup, χ σ = 0) →
      ∃ χ₁ χ₂ : (Ω ≃ₐ[k] Ω) → ZMod p,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ₁ (x * y) = χ₁ x + χ₁ y) ∧
        (∀ σ ∈ L₁.fixingSubgroup, χ₁ σ = 0) ∧
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ₂ (x * y) = χ₂ x + χ₂ y) ∧
        (∀ σ ∈ L₂.fixingSubgroup, χ₂ σ = 0) ∧
        ∀ σ ∈ K.fixingSubgroup, χ σ = χ₁ σ + χ₂ σ) :
    ∃ (z : (Ω ≃ₐ[k] Ω) → ZMod p) (Q : ValuationSubring Ω),
      SSGRoute.IsFinPlace k Q ∧ SSGRoute.IsSplitIn k (L₁ ⊔ L₂) Q ∧
      (∀ A ∈ T, ∀ τ ∈ K.fixingSubgroup, τ • A ≠ Q) ∧
      (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, z (x * y) = z x + z y) ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ A ∈ T, ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, z σ = g σ + h A σ) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ T, ∀ τ ∈ K.fixingSubgroup, τ • A ≠ B) →
        (∀ τ ∈ K.fixingSubgroup, τ • Q ≠ B) →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) := by
  classical
  haveI hAlgClosed : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  haveI hNumK : NumberField ↥K := NumberField.of_module_finite k ↥K
  -- the primitive `p`-th root of unity, as an element of `↥K`
  set ζK : ↥K := ⟨ζ, hζK⟩ with hζKdef
  have hζK' : IsPrimitiveRoot ζK p :=
    ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ
  -- ## 0. the primes of `↥K` below the places of `T`
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
  have hT'below : ∀ 𝔭 ∈ T', ∃ A ∈ T,
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
    intro B hB hp
    obtain ⟨A, hA, τ, hτ, hτA⟩ := hTcov B hB (Or.inl hp)
    obtain ⟨𝔭, h𝔭T', h𝔭A⟩ := hTbelow A hA
    refine ⟨𝔭, h𝔭T', ?_⟩
    rw [← h𝔭A, ← hτA]
    have hcoe : ⇑((IntermediateField.fixingSubgroupEquiv K) ⟨τ, hτ⟩) = ⇑τ := funext fun _ => rfl
    rw [(GrunwaldEscapeCore.gesSmulEqOfCoeEq K hcoe A).symm]
    exact Commons.NumberTheory.NumberField.Valuation.comap_smul_algebraMap A _
  -- ## 1. Grünwald: the element `a ∈ Kˣ` realising the datum at `T`
  obtain ⟨a, ha⟩ :=
    GrunwaldEscapeCore.grunwald_kummer_first_element p k Ω K ζK hζK' hKimag T hTfin
      (fun A hA B hB hconj => hTdisj A hA B hB hconj)
      g hg hgc h hh hhc
  -- ## 2. the class field data of `U_p` over `↥K`
  obtain ⟨M, hfdM, hgalM, hnfM, hcommM, art, hM, hker, hfrob⟩ :=
    SSG8Escape.class_field_data_ssg8 p k Ω K T'
  haveI : FiniteDimensional ↥K M := hfdM
  haveI : IsGalois ↥K M := hgalM
  haveI : NumberField ↥M := hnfM
  haveI : IsMulCommutative (↥M ≃ₐ[↥K] ↥M) := hcommM
  -- ## 3. the orthogonality: `art(𝔡)` is trivial on `M ⊓ (L₁ ⊔ L₂)`
  let α : ↥M ≃ₐ[↥K] ↥M :=
    art (NK.NUV2.RouteB.RayModulus.fracIdele (tFreePart (K := ↥K) T' a))
  have hαfix : ∀ x : ↥M, ((x : Ω) ∈ (L₁ ⊔ L₂ : IntermediateField k Ω)) → α x = x :=
    Work.SSGRoute.N2v2.alpha_fixes_inf_ssg8_hsplit p k Ω K ζK hζK' hKimag L₁ L₂ hKL₁ hKL₂ T
      hTfin T' hTbelow hT'below (fun A hA B hB hconj => hTdisj A hA B hB hconj) hTcov g hg hgc
      hgram h hh hhc horth₁ horth₂ hsplit a ha M hM art hker hfrob α rfl
  -- ## 4. the escape prime
  have hc : NK.Reconstruct.ChebotarevDensityInput k Ω :=
    Work.SSG8Escape.chebotarevDensityInput_general k Ω
  obtain ⟨Q, 𝔮, hQfin, hQsplit, h𝔮T', _h𝔮unr, hQ𝔮, hQnotT, hmem⟩ :=
    SSG8Escape.escape_prime_ssg8 p k Ω K ζK hζK' hKimag L₁ L₂ hKL₁ hKL₂ T hTfin T' hTbelow
      hT'below (fun A hA B hB hconj => hTdisj A hA B hB hconj) hTcov g hg hgc hgram h hh hhc
      horth₁ horth₂ a ha hc M hM (fun x y => mul_comm' x y) art hker hfrob α rfl hαfix
  -- ## 5. the correction: `b ∈ Kˣ` with the same local data but ramified only over `T'` and `𝔮`
  obtain ⟨b, hagree, hesc⟩ :=
    SSG8Escape.correction_ssg8 p k Ω K ζK hζK' T hTfin T' hTbelow hT'p a 𝔮 h𝔮T' hmem
  -- ## 6. the class `z` and the clauses of the conclusion
  refine ⟨ZSplit.nodeKummerCocharZMod K ζ hζK hζ b, Q, hQfin, hQsplit, ?_, ?_, ?_, ?_, ?_⟩
  · -- `Q` is not `↥K`-conjugate to any element of `T`
    intro A hA τ hτ hτA
    exact hQnotT A hA τ hτ hτA
  · -- additivity on `G_K`
    exact ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ b
  · -- local constancy
    exact ZSplit.nodeKummerCocharZMod_locConst K ζ hζK hζ b
  · -- the local datum at `T`
    intro A hA σ hσ
    have hσK : σ ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp hσ).2
    rw [ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK) (hζ := hζ)
      (β := b) hσK]
    have hto : (IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσK⟩ =
        Work.SSGRoute.gesLocalToGalK K ⟨σ, hσ⟩ := rfl
    rw [hto, ← hagree A hA ⟨σ, hσ⟩]
    exact (ha A hA ⟨σ, hσ⟩).symm
  · -- unramified outside the classes of `T` and of `Q`
    intro B hB hnotT hnotQ σ hσ hI
    rw [ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK) (hζ := hζ)
      (β := b) hσ]
    have hto : (IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩ =
        Work.SSGRoute.gesGalKOfFixing K σ hσ := rfl
    rw [hto]
    refine hesc B hB ?_ ?_ σ hσ hI
    · -- `B` does not lie over a prime of `T'`
      intro 𝔭 h𝔭 h𝔭eq
      obtain ⟨A, hA, hAeq⟩ := hT'below 𝔭 h𝔭
      have hcomap : B.comap (algebraMap ↥K Ω) = A.comap (algebraMap ↥K Ω) := by
        rw [h𝔭eq, hAeq]
      obtain ⟨τ, hτ, hτA⟩ :=
        (exists_mem_fixingSubgroup_smul_eq_iff_comap_eq (B := A) (Q := B) K
          (hTfin A hA)).mpr hcomap
      exact hnotT A hA τ hτ hτA
    · -- `B` does not lie over the prime `𝔮` of `Q`
      intro h𝔮eq
      have hcomap : B.comap (algebraMap ↥K Ω) = Q.comap (algebraMap ↥K Ω) := by
        rw [h𝔮eq, hQ𝔮]
      obtain ⟨τ, hτ, hτQ⟩ :=
        (exists_mem_fixingSubgroup_smul_eq_iff_comap_eq (B := Q) (Q := B) K hQfin).mpr hcomap
      exact hnotQ τ hτ hτQ


end Work.SSGRoute
