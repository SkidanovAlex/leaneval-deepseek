import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.GrunwaldEscapeCore.L1KAssembly
import Submission.Work.SSGRoute.grunwald_escape_relative_v2
import Submission.Work.SSGRoute.GrunwaldEscapeCore.grunwald_kummer_first_element
import Submission.Work.SSGRoute.GrunwaldEscapeCore.gesCorrectionFromPrime
import Submission.Work.SSGRoute.GrunwaldEscapeCore.Vocab
import Submission.Work.SSGRoute.ZSplit.FrobeniusValue
import Submission.Work.SSGRoute.ZSplit.SWFourOddKummer
import Submission.Work.SSG8Escape.class_field_data_ssg8
import Submission.Work.SSG8Escape.escape_prime_ssg8
import Submission.Work.SSG8Escape.correction_ssg8
import Submission.Work.SSGRoute.SSG8Escape.ChebotarevDensityInput
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GrunwaldEscapeCore

open scoped Pointwise
open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-- **The escape realisation at `L₁ = K`, `g = 0`, from the orthogonality.**

This is the assembly half of the escape-form Grünwald theorem in the case `L₁ = K`: given the
Grünwald element `a ∈ ↥Kˣ` realising the datum `h` at `T`, the class field `M` of
`U' = gesUPow ↥K p T'` with its idèlic Artin map `art`, and the **orthogonality** hypothesis
`hαfix` (the Artin symbol `α = art(𝔡)` of the `T'`-free part `𝔡 = tFreePart T' a` of the divisor of
`a` fixes everything of `M` lying in `L`), it produces the global additive class `z` agreeing with
the datum at `T`, together with the escape place `Q` split in `L`, outside the classes of `T`.

The two arithmetic inputs are the already proved
`SSG8Escape.escape_prime_ssg8` (Čebotarev, the escape place with the idèle-class membership
`[𝔮]·[𝔡] ∈ U'`) and `SSG8Escape.correction_ssg8` (reading off: the corrected element `b ∈ ↥Kˣ` with
the same local data at `T` and `p ∣ v_B(b)` outside the classes of `T` and `Q`); `z` is the Kummer
character of `b` (`ZSplit.nodeKummerCocharZMod`). -/
theorem escape_L1K_of_alpha_fixes (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (hKimag : p = 2 → ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → c = 1)
    (L : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L] (hKL : K ≤ L)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, (∃ τ ∈ K.fixingSubgroup, τ • A = B) → A = B)
    (hTcov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (B.valuation (p : Ω) < 1 ∨
        (∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ L.fixingSubgroup)) →
      ∃ A ∈ T, ∃ τ ∈ K.fixingSubgroup, τ • A = B)
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
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p
          (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) a
          (Work.SSGRoute.gesLocalToGalK K σ))
    (T' : Finset (NK.Chebotarev.PrimeIdeal ↥K))
    (hTbelow : ∀ A ∈ T, ∃ 𝔭 ∈ T', A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (hT'above : ∀ 𝔭 ∈ T', ∃ A ∈ T, A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (M : IntermediateField ↥K Ω) [FiniteDimensional ↥K M] [IsGalois ↥K M] [NumberField ↥M]
    [IsMulCommutative (↥M ≃ₐ[↥K] ↥M)]
    (hM : NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥M =
      Work.SSGRoute.SSG8Escape.gesUPow ↥K p T')
    (art : NK.GlobalCFT.Idele ↥K →* (↥M ≃ₐ[↥K] ↥M))
    (hker : art.ker = NK.GlobalCFT.Idele.normImage ↥K ↥M ⊔
      NK.GlobalCFT.Idele.principalSubgroup ↥K)
    (hfrob : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥K,
      NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥M) 𝔮 →
      art (NK.HeckeL.ideleOfPrime ↥K 𝔮) = NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥M) 𝔮)
    (α : ↥M ≃ₐ[↥K] ↥M)
    (hα : art (NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart (K := ↥K) T' a))
      = α)
    (hαfix : ∀ x : ↥M, ((x : Ω) ∈ L) → α x = x) :
    ∃ (z : (Ω ≃ₐ[k] Ω) → ZMod p) (Q : ValuationSubring Ω),
      SSGRoute.IsFinPlace k Q ∧ SSGRoute.IsSplitIn k L Q ∧
      (∀ A ∈ T, ∀ τ ∈ K.fixingSubgroup, τ • A ≠ Q) ∧
      (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, z (x * y) = z x + z y) ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ A ∈ T, ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, z σ = h A σ) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ T, ∀ τ ∈ K.fixingSubgroup, τ • A ≠ B) →
        (∀ τ ∈ K.fixingSubgroup, τ • Q ≠ B) →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) := by
  classical
  haveI hNumK : NumberField ↥K := NumberField.of_module_finite k ↥K
  have hsup : (K ⊔ L : IntermediateField k Ω) = L := sup_eq_right.mpr hKL
  set ζK : ↥K := ⟨ζ, hζK⟩ with hζKdef
  have hζK' : IsPrimitiveRoot ζK p :=
    Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ
  -- the zero global datum, in the form used by the escape/correction interfaces
  let g : (Ω ≃ₐ[k] Ω) → ZMod p := 0
  have hg : ∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, g (x * y) = g x + g y := by
    intro x _ y _
    simp [g]
  have hgc : SSGRoute.IsLocConstOn K.fixingSubgroup g :=
    ⟨⊤, isOpen_univ, by intro x _ u _ _; simp [g]⟩
  have hgram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ T, ∀ τ ∈ K.fixingSubgroup, τ • A ≠ B) → ¬ SSGRoute.IsSplitIn k K B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → g σ = 0 := by
    intro B _ _ _ σ _ _
    simp [g]
  have ha' : ∀ A ∈ T, ∀ σ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
      g (σ : Ω ≃ₐ[k] Ω) + h A (σ : Ω ≃ₐ[k] Ω) =
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p hζK' a
          (Work.SSGRoute.gesLocalToGalK K σ) := by
    intro A hA σ
    have h1 := ha A hA σ
    rw [h1]
    simp [g]
  -- the covering hypothesis with the (impossible) `L₁ = K` disjunct
  have hTcov' : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (B.valuation (p : Ω) < 1 ∨
        (∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ K.fixingSubgroup) ∨
        (∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ L.fixingSubgroup)) →
      ∃ A ∈ T, ∃ τ ∈ K.fixingSubgroup, τ • A = B := by
    intro B hB hcase
    rcases hcase with hv | ⟨σ, hσK, -, hσnot⟩ | hcase
    · exact hTcov B hB (Or.inl hv)
    · exact absurd hσK hσnot
    · exact hTcov B hB (Or.inr hcase)
  -- the two orthogonality hypotheses for the escape place: the first is automatic at `L₁ = K`
  have horth₁' : ∀ A ∈ T,
      (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A σ = 0) ∨
      (∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
        (∀ σ ∈ K.fixingSubgroup, χ σ = 0) →
        ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, χ σ = 0) ∨
      ((∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → h A σ = 0) ∧
        ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
          (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
          (∀ σ ∈ K.fixingSubgroup, χ σ = 0) →
          ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → χ σ = 0) :=
    fun A _ => Or.inr (Or.inl (fun χ _ hχ0 σ hσ => hχ0 σ hσ.2))
  have horth₂' : ∀ A ∈ T,
      (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, g σ + h A σ = 0) ∨
      (∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
        (∀ σ ∈ L.fixingSubgroup, χ σ = 0) →
        ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, χ σ = 0) ∨
      ((∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → g σ + h A σ = 0) ∧
        ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
          (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
          (∀ σ ∈ L.fixingSubgroup, χ σ = 0) →
          ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → χ σ = 0) := by
    intro A hA
    rcases horth A hA with hzero | hχ
    · refine Or.inl (fun σ hσ => ?_)
      rw [hzero σ hσ]
      simp [g]
    · exact Or.inr (Or.inl hχ)
  -- the orthogonality at the level `M`, transported from `L` to `K ⊔ L = L`
  have hαfixK : ∀ x : ↥M, ((x : Ω) ∈ (K ⊔ L : IntermediateField k Ω)) → α x = x := by
    intro x hx
    exact hαfix x (by rwa [hsup] at hx)
  -- the places over `p` lie over `T'`
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
    rw [(Work.SSGRoute.GrunwaldEscapeCore.gesSmulEqOfCoeEq K hcoe A).symm]
    exact Commons.NumberTheory.NumberField.Valuation.comap_smul_algebraMap A _
  -- the escape place `Q`, with the idèle-class membership `[𝔮]·[𝔡] ∈ U'`
  have hc : NK.Reconstruct.ChebotarevDensityInput k Ω :=
    Work.SSG8Escape.chebotarevDensityInput_general k Ω
  obtain ⟨Q, 𝔮, hQfin, hQsplit, h𝔮T', _h𝔮unr, hQ𝔮, hQnotT, hmem⟩ :=
    Work.SSG8Escape.escape_prime_ssg8 p k Ω K ζK hζK' hKimag K L le_rfl hKL T hTfin T' hTbelow
      hT'above (fun A hA B hB hconj => hTdisj A hA B hB hconj) hTcov' g hg hgc hgram h hh hhc
      horth₁' horth₂' a ha' hc M hM (fun x y => mul_comm' x y) art hker hfrob α hα hαfixK
  -- the corrected element `b`
  obtain ⟨b, hagree, hesc⟩ :=
    Work.SSG8Escape.correction_ssg8 p k Ω K ζK hζK' T hTfin T' hTbelow hT'p a 𝔮 h𝔮T' hmem
  -- the global class `z` and the clauses of the conclusion
  refine ⟨Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b, Q, hQfin, ?_, hQnotT, ?_, ?_, ?_, ?_⟩
  · rwa [hsup] at hQsplit
  · exact Work.SSGRoute.ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ b
  · exact Work.SSGRoute.ZSplit.nodeKummerCocharZMod_locConst K ζ hζK hζ b
  · intro A hA σ hσ
    have hσK : σ ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp hσ).2
    rw [Work.SSGRoute.ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK) (hζ := hζ)
      (β := b) hσK]
    have hto : (IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσK⟩ =
        Work.SSGRoute.gesLocalToGalK K ⟨σ, hσ⟩ := rfl
    rw [hto, ← hagree A hA ⟨σ, hσ⟩]
    exact (ha A hA ⟨σ, hσ⟩).symm
  · intro B hB hnotT hnotQ σ hσ hI
    rw [Work.SSGRoute.ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK) (hζ := hζ)
      (β := b) hσ]
    have hto : (IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩ =
        Work.SSGRoute.gesGalKOfFixing K σ hσ := rfl
    rw [hto]
    refine hesc B hB ?_ ?_ σ hσ hI
    · intro 𝔭 h𝔭 h𝔭eq
      obtain ⟨A, hA, hAeq⟩ := hT'above 𝔭 h𝔭
      have hcomap : B.comap (algebraMap ↥K Ω) = A.comap (algebraMap ↥K Ω) := by
        rw [h𝔭eq, hAeq]
      obtain ⟨τ, hτ, hτA⟩ :=
        (Work.SSGRoute.exists_mem_fixingSubgroup_smul_eq_iff_comap_eq (B := A) (Q := B) K
          (hTfin A hA)).mpr hcomap
      exact hnotT A hA τ hτ hτA
    · intro h𝔮eq
      have hcomap : B.comap (algebraMap ↥K Ω) = Q.comap (algebraMap ↥K Ω) := by
        rw [h𝔮eq, hQ𝔮]
      obtain ⟨τ, hτ, hτQ⟩ :=
        (Work.SSGRoute.exists_mem_fixingSubgroup_smul_eq_iff_comap_eq (B := Q) (Q := B) K hQfin).mpr hcomap
      exact hnotQ τ hτ hτQ

/-- **The escape realisation of Grünwald–Wang at `L₁ = K`, `g = 0`.**

This is the specialisation of the corrected escape statement
`Work.SSGRoute.grunwald_escape_relative_v2` to the case in which the first auxiliary field is `K`
itself and the global datum `g` vanishes; it is the only case needed by the Step-4 escape
(`ssg8_ges_zmod`).

Concretely we apply the general (proved) statement with `L₁ := K`, `L₂ := L` and `g := 0`.  The
hypotheses translate as follows:

* `K ⊔ L = L`, so the conclusion's `IsSplitIn k (K ⊔ L) Q` is `IsSplitIn k L Q`;
* the `hsplit` hypothesis is witnessed by `χ₁ := 0`, `χ₂ := χ` (and `(K ⊔ L).fixingSubgroup =
  L.fixingSubgroup`);
* the first orthogonality `horth₁` is automatic at `L₁ = K` (a `χ` vanishing on all of
  `K.fixingSubgroup` vanishes on `decomp k A ⊓ K.fixingSubgroup`);
* the second orthogonality `horth₂` is the two-disjunct `horth` of the statement (with `g = 0`);
* the second disjunct of `hTcov` at `L₁ = K` is contradictory. -/
theorem grunwald_escape_relative_L1K (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (hKimag : p = 2 → ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → c = 1)
    (L : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L] (hKL : K ≤ L)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, (∃ τ ∈ K.fixingSubgroup, τ • A = B) → A = B)
    (hTcov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (B.valuation (p : Ω) < 1 ∨
        (∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ L.fixingSubgroup)) →
      ∃ A ∈ T, ∃ τ ∈ K.fixingSubgroup, τ • A = B)
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
        ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, χ σ = 0)) :
    ∃ (z : (Ω ≃ₐ[k] Ω) → ZMod p) (Q : ValuationSubring Ω),
      SSGRoute.IsFinPlace k Q ∧ SSGRoute.IsSplitIn k L Q ∧
      (∀ A ∈ T, ∀ τ ∈ K.fixingSubgroup, τ • A ≠ Q) ∧
      (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, z (x * y) = z x + z y) ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ A ∈ T, ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, z σ = h A σ) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ T, ∀ τ ∈ K.fixingSubgroup, τ • A ≠ B) →
        (∀ τ ∈ K.fixingSubgroup, τ • Q ≠ B) →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) := by
  classical
  have hsup : (K ⊔ L : IntermediateField k Ω) = L := sup_eq_right.mpr hKL
  -- the global datum is zero
  let g : (Ω ≃ₐ[k] Ω) → ZMod p := 0
  -- the covering hypothesis, with the (impossible) `L₁ = K` disjunct
  have hTcov' : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (B.valuation (p : Ω) < 1 ∨
        (∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ K.fixingSubgroup) ∨
        (∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ L.fixingSubgroup)) →
      ∃ A ∈ T, ∃ τ ∈ K.fixingSubgroup, τ • A = B := by
    intro B hB hcase
    rcases hcase with hv | ⟨σ, hσK, -, hσnot⟩ | hcase
    · exact hTcov B hB (Or.inl hv)
    · exact absurd hσK hσnot
    · exact hTcov B hB (Or.inr hcase)
  have hg' : ∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, g (x * y) = g x + g y := by
    intro x _ y _
    simp [g]
  have hgc' : SSGRoute.IsLocConstOn K.fixingSubgroup g :=
    ⟨⊤, isOpen_univ, by intro x _ u _ _; simp [g]⟩
  have hgram' : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ T, ∀ τ ∈ K.fixingSubgroup, τ • A ≠ B) → ¬ SSGRoute.IsSplitIn k K B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → g σ = 0 := by
    intro B _ _ _ σ _ _
    simp [g]
  -- the first orthogonality is automatic at `L₁ = K`
  have horth₁' : ∀ A ∈ T,
      (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A σ = 0) ∨
      (∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
        (∀ σ ∈ K.fixingSubgroup, χ σ = 0) →
        ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, χ σ = 0) ∨
      ((∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → h A σ = 0) ∧
        ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
          (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
          (∀ σ ∈ K.fixingSubgroup, χ σ = 0) →
          ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → χ σ = 0) :=
    fun A _ => Or.inr (Or.inl (fun χ _ hχ0 σ hσ => hχ0 σ hσ.2))
  -- the given two-disjunct `horth` supplies the second orthogonality
  have horth₂' : ∀ A ∈ T,
      (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, g σ + h A σ = 0) ∨
      (∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
        (∀ σ ∈ L.fixingSubgroup, χ σ = 0) →
        ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, χ σ = 0) ∨
      ((∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → g σ + h A σ = 0) ∧
        ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
          (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
          (∀ σ ∈ L.fixingSubgroup, χ σ = 0) →
          ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → χ σ = 0) := by
    intro A hA
    rcases horth A hA with hzero | hχ
    · exact Or.inl (fun σ hσ => by rw [hzero σ hσ]; exact zero_add 0)
    · exact Or.inr (Or.inl hχ)
  -- the splitting hypothesis: `χ = 0 + χ`, and `(K ⊔ L).fixingSubgroup = L.fixingSubgroup`
  have hsplit' : ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
      (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
      (∀ σ ∈ (K ⊔ L : IntermediateField k Ω).fixingSubgroup, χ σ = 0) →
      ∃ χ₁ χ₂ : (Ω ≃ₐ[k] Ω) → ZMod p,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ₁ (x * y) = χ₁ x + χ₁ y) ∧
        (∀ σ ∈ K.fixingSubgroup, χ₁ σ = 0) ∧
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ₂ (x * y) = χ₂ x + χ₂ y) ∧
        (∀ σ ∈ L.fixingSubgroup, χ₂ σ = 0) ∧
        ∀ σ ∈ K.fixingSubgroup, χ σ = χ₁ σ + χ₂ σ := by
    intro χ hχadd hχ0
    refine ⟨0, χ, ?_, ?_, hχadd, ?_, ?_⟩
    · intro x _ y _; simp
    · intro σ _; simp
    · intro σ hσ
      exact hχ0 σ (by rw [hsup]; exact hσ)
    · intro σ _; simp
  obtain ⟨z, Q, hQfin, hQsplit, hQnotT, hzadd, hzloc, hzpres, hzunr⟩ :=
    Work.SSGRoute.grunwald_escape_relative_v2 p k Ω K ζ hζ hζK hKimag
      K L le_rfl hKL T hTfin hTdisj
      (hTcov := hTcov') (hsplit := hsplit') (g := g) (hg := hg') (hgc := hgc')
      (hgram := hgram') (horth₁ := horth₁') (horth₂ := horth₂')
      (h := h) (hh := hh) (hhc := hhc)
  refine ⟨z, Q, hQfin, ?_, hQnotT, hzadd, hzloc, ?_, ?_⟩
  · rw [hsup] at hQsplit
    exact hQsplit
  · intro A hA σ hσ
    have := hzpres A hA σ hσ
    simpa [g] using this
  · intro B hB hnotT hnotQ σ hσ hI
    exact hzunr B hB hnotT hnotQ σ hσ hI

end Work.GrunwaldEscapeCore
