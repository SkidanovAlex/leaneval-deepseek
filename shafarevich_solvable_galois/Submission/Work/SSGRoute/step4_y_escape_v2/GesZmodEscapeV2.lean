import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.grunwald_distinct_defs
import Submission.Work.SSGRoute.grunwald_escape_support_E
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `ges_zmod_escape_v2`: escape-form Grünwald at the level `↥K`, `ZMod p`-valued

The statement below is *verbatim* the statement of
`Work.SSGRoute.ges_grunwald_escape_support_zmod`
(`Submission/Work/SSGRoute/grunwald_escape_support_E.lean`), which is the assembled node N3 of the
Step-4 design.

## The route of this file (independent of the `hsplit` / `myv2.Heart` lane)

The general escape-form Grünwald statement with a non-trivial pair `(L₁, L₂)` is **false** as
stated with the trichotomy `horth₁`/`horth₂` (see
`Submission/Work/SSGRoute/COUNTEREXAMPLE_N2_grunwald_escape_relative.md`).  Only the specialisation
`L₁ = K`, `g = 0`, `L₂ = L` is used by Step 4 of Shafarevich's theorem — and that is exactly the
situation of the lemma below (`hsupp` is the two-disjunct `horth` at `L₁ = K`, `g = 0`).

The proof assembled here avoids the false general form and goes through the *L₁ = K* orthogonality,
which is now on disk and axiom-clean:

* `Work.GrunwaldEscapeCore.L1Korth.alpha_fixes_L1K`
  (`Submission/Work/GrunwaldEscapeCore/L1Korth/alpha_fixes_L1K.lean`, proved, no `sorry`,
  axioms `propeq, Classical.choice, Quot.sound`): the Artin symbol `α = art(fracIdele (tFreePart T' a))`
  of the `T'`-free part of the Grünwald element fixes pointwise the elements of the class field `M`
  of `gesUPow ↥K p T'` that lie in `L`;
* `Work.GrunwaldEscapeCore.escape_L1K_of_alpha_fixes`
  (`Submission/Work/GrunwaldEscapeCore/grunwald_escape_relative_L1K.lean`, proved, axiom-clean):
  given that orthogonality, the escape prime `Q` (`SSG8Escape.escape_prime_ssg8`) and the reading-off
  (`SSG8Escape.correction_ssg8`) produce the global additive class `z` with the prescribed local data;
* the class field data come from `Work.SSG8Escape.class_field_data_ssg8`, the first element `a` from
  `Work.SSGRoute.GrunwaldEscapeCore.grunwald_kummer_first_element`.

`Work.SSGRoute.ges_smul_form_L1K_v4` below is that assembly; `ges_zmod_escape_v2` is the transport of
its conclusion from `K.fixingSubgroup` to `Gal(ℚ̄/↥K)` along `IntermediateField.fixingSubgroupEquiv K`
(verbatim the transport of `ges_grunwald_escape_support_E.ges_grunwald_escape_support_zmod`).
-/

open scoped Pointwise
open NumberField IsDedekindDomain

namespace Work.SSGRoute

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

/-- **Grünwald with escape**, case `L₁ = K`, `g = 0`, assembled from the axiom-clean
`L₁ = K` orthogonality `Work.GrunwaldEscapeCore.L1Korth.alpha_fixes_L1K`.

Verbatim the statement of `Work.SSGRoute.ges_smul_form_L1K`
(`Submission/Work/SSGRoute/grunwald_escape_support_E.lean`). -/
theorem ges_smul_form_L1K_v4 (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
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
        ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, χ σ = 0)) :
    ∃ (z : (Ω ≃ₐ[k] Ω) → ZMod p) (Q : ValuationSubring Ω),
      SSGRoute.IsFinPlace k Q ∧ SSGRoute.IsSplitIn k L Q ∧
      (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A Q) ∧
      (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, z (x * y) = z x + z y) ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ A ∈ T, ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, z σ = h A σ) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) → ¬ Work.SSGRoute.gesKConj K Q B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) := by
  classical
  haveI hAlgClosed : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  haveI hNumK : NumberField ↥K := NumberField.of_module_finite k ↥K
  -- ## 0. the primitive `p`-th root of unity, as an element of `↥K`
  set ζK : ↥K := ⟨ζ, hζK⟩ with hζKdef
  have hζK' : IsPrimitiveRoot ζK p :=
    ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ
  -- ## 1. the primes of `↥K` below the places of `T`
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
  -- ## 2. the Grünwald element `a ∈ ↥Kˣ` realising the datum at `T`
  obtain ⟨a, ha⟩ :=
    GrunwaldEscapeCore.grunwald_kummer_first_element p k Ω K ζK hζK' hKimag T hTfin hTdisj
      (fun _ => 0) (fun x _ y _ => by simp)
      ⟨⊤, by rw [Subgroup.coe_top]; exact isOpen_univ, fun x _ u _ _ => rfl⟩
      h hh hhc
  -- ## 3. the class field data of `U_p = gesUPow ↥K p T'` over `↥K`
  obtain ⟨M, hfdM, hgalM, hnfM, hcommM, art, hM, hker, hfrob⟩ :=
    SSG8Escape.class_field_data_ssg8 p k Ω K T'
  haveI : FiniteDimensional ↥K M := hfdM
  haveI : IsGalois ↥K M := hgalM
  haveI : NumberField ↥M := hnfM
  haveI : IsMulCommutative (↥M ≃ₐ[↥K] ↥M) := hcommM
  -- ## 4. the orthogonality (the axiom-clean `L₁ = K` case)
  let α : ↥M ≃ₐ[↥K] ↥M :=
    art (NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart (K := ↥K) T' a))
  have hαfix : ∀ x : ↥M, ((x : Ω) ∈ L) → α x = x :=
    Work.GrunwaldEscapeCore.L1Korth.alpha_fixes_L1K p k Ω K ζK hζK' hKimag L hKL T hTfin T'
      hTbelow hT'above hTdisj hTcov h hh hhc horth a (fun A hA σ => by simpa using ha A hA σ)
      M hM art hker hfrob α rfl
  -- ## 5. the escape assembly
  obtain ⟨z, Q, hQfin, hQsplit, hQT, hzadd, hzloc, hzpres, hzunr⟩ :=
    Work.GrunwaldEscapeCore.escape_L1K_of_alpha_fixes p k Ω K ζ hζ hζK hKimag L hKL T hTfin
      hTdisj hTcov h hh hhc horth a (fun A hA σ => by simpa using ha A hA σ) T' hTbelow hT'above M
      hM art hker hfrob α rfl hαfix
  refine ⟨z, Q, hQfin, hQsplit, (fun A hA hconj => ?_), hzadd, hzloc, hzpres, (fun B hB hnotT hnotQ σ hσ hI => ?_)⟩
  · obtain ⟨τ, hτ, hτQ⟩ := hconj
    exact hQT A hA τ hτ hτQ
  · exact hzunr B hB (fun A hA τ hτ hτB => hnotT A hA ⟨τ, hτ, hτB⟩)
      (fun τ hτ hτQ => hnotQ ⟨τ, hτ, hτQ⟩) σ hσ hI

/-- **`ges_zmod_escape_v2`**: the `ZMod p`-valued escape-form Grünwald theorem over `↥K`, transported
from `ges_smul_form_L1K_v4` to `Gal(ℚ̄/↥K)`. -/
theorem ges_zmod_escape_v2 (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K]
    (ζ : SSGRoute.QBar) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (hKimag : p = 2 → ∀ c : SSGRoute.GalQ, c ^ 2 = 1 → c ∈ K.fixingSubgroup → c = 1)
    (L : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ L] [IsGalois ℚ L] (hKL : K ≤ L)
    (T : Finset (ValuationSubring SSGRoute.QBar))
    (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace ↥K A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, SSGRoute.IsConjPlace ↥K A B → A = B)
    (hTcov : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ↥K B →
      (B.valuation (p : SSGRoute.QBar) < 1 ∨ SSGRoute.IsRamifiedIn ↥K (overK K L hKL) B) →
      ∃ A ∈ T, SSGRoute.IsConjPlace ↥K A B)
    (f : ValuationSubring SSGRoute.QBar → (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) → ZMod p)
    (hf : ∀ A ∈ T, ∀ x ∈ SSGRoute.decomp ↥K A, ∀ y ∈ SSGRoute.decomp ↥K A,
      f A (x * y) = f A x + f A y)
    (hfc : ∀ A ∈ T, ∃ U : Subgroup (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar),
      IsOpen (U : Set (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar)) ∧
      ∀ x ∈ U, x ∈ SSGRoute.decomp ↥K A → f A x = 0)
    (hsupp : ∀ A ∈ T, (∀ δ ∈ SSGRoute.decomp ↥K A, f A δ = 0) ∨
      ∀ χ : (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) → ZMod p,
        (∀ x y : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar, χ (x * y) = χ x + χ y) →
        (∀ δ ∈ (overK K L hKL).fixingSubgroup, χ δ = 0) →
        ∀ δ ∈ SSGRoute.decomp ↥K A, χ δ = 0) :
    ∃ ε : (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) → ZMod p,
      (∀ x y : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar, ε (x * y) = ε x + ε y) ∧
      SSGRoute.IsLocConstOn (⊤ : Subgroup (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar)) ε ∧
      (∀ A ∈ T, ∀ δ ∈ SSGRoute.decomp ↥K A, ε δ = f A δ) ∧
      (∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ↥K B →
        (∀ A ∈ T, ¬ SSGRoute.IsConjPlace ↥K A B) → ¬ SSGRoute.IsSplitIn ℚ L B →
        ∀ δ : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar, SSGRoute.IsInertia ↥K B δ → ε δ = 0) := by
  classical
  haveI hGalK : IsGalois ℚ K := IsGalois.mk
  haveI hAlgQ : IsAlgClosure ℚ SSGRoute.QBar := AlgebraicClosure.instIsAlgClosure ℚ
  obtain ⟨z, Q, _hQfin, hQsplit, _hQT, hzadd, hzloc, hzpres, hzunr⟩ :=
    @ges_smul_form_L1K_v4 p (inferInstance : Fact p.Prime) ℚ SSGRoute.QBar
      (inferInstance : Field ℚ) (inferInstance : NumberField ℚ)
      (inferInstance : Field SSGRoute.QBar) (inferInstance : Algebra ℚ SSGRoute.QBar)
      (inferInstance : IsAlgClosure ℚ SSGRoute.QBar)
      K (inferInstance : FiniteDimensional ℚ K) hGalK
      ζ hζ hζK
      (fun hp c hc hc2 => hKimag hp c hc2 hc)
      L (inferInstance : FiniteDimensional ℚ L) (inferInstance : IsGalois ℚ L) hKL
      T
      (fun A hA => (local_transport_isFinPlace K A).mp (hTfin A hA))
      (fun A hA B hB hconj => hTdisj A hA B hB ((ges_isConjPlace_iff K A B).mpr hconj))
      (fun B hB hcase => by
        have hcase' : B.valuation (p : SSGRoute.QBar) < 1 ∨
            SSGRoute.IsRamifiedIn ↥K (overK K L hKL) B := by
          rcases hcase with h | h
          · exact Or.inl h
          · obtain ⟨σ, hσ, hI, hσnot⟩ := h
            exact Or.inr ((ges_isRamifiedIn_overK_iff K L hKL B).mpr ⟨σ, hσ, hI, hσnot⟩)
        obtain ⟨A, hA, hconj⟩ := hTcov B ((local_transport_isFinPlace K B).mpr hB) hcase'
        exact ⟨A, hA, (ges_isConjPlace_iff K A B).mp hconj⟩)
      (gesLocalDatum K f)
      (fun A hA => gesLocalDatum_add K f A (hf A hA))
      (fun A hA => by
        obtain ⟨U₀, hU₀open, hU₀⟩ := hfc A hA
        obtain ⟨U, hUopen, hUpull⟩ := ges_openSubgroup_pullback K U₀ hU₀open
        refine ⟨U, hUopen, ?_⟩
        intro x hxU hxmem
        rw [gesLocalDatum_apply K f A x hxmem.2]
        exact hU₀ _ (hUpull ⟨x, hxmem.2⟩ hxU)
          (ges_decomp_of_mem_gal K A x hxmem.2 hxmem.1))
      (fun A hA => by
        rcases hsupp A hA with hzero | hχ
        · left
          intro σ hσ
          rw [gesLocalDatum_apply K f A σ hσ.2]
          exact hzero _ (ges_decomp_of_mem_gal K A σ hσ.2 hσ.1)
        · right
          intro χ hχadd hχkill σ hσ
          obtain ⟨χ', hχ'add, hχ'kill, hχ'val⟩ := ges_transfer_chi K L hKL χ hχadd hχkill
          have h3 := hχ χ' hχ'add hχ'kill
            ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ.2⟩)
            (ges_decomp_of_mem_gal K A σ hσ.2 hσ.1)
          rw [hχ'val ⟨σ, hσ.2⟩] at h3
          exact h3)
  -- the escape place `Q` is split completely in `L`
  have hQsplitL : SSGRoute.IsSplitIn ℚ L Q := hQsplit
  refine ⟨fun x => z (↑((IntermediateField.fixingSubgroupEquiv K).symm x) : SSGRoute.GalQ),
    ?_, ?_, ?_, ?_⟩
  · intro x y
    have h1 : (↑((IntermediateField.fixingSubgroupEquiv K).symm (x * y)) : SSGRoute.GalQ)
        = (↑((IntermediateField.fixingSubgroupEquiv K).symm x) : SSGRoute.GalQ) *
          (↑((IntermediateField.fixingSubgroupEquiv K).symm y) : SSGRoute.GalQ) := by
      rw [map_mul]
      rfl
    show z (↑((IntermediateField.fixingSubgroupEquiv K).symm (x * y)) : SSGRoute.GalQ)
      = z (↑((IntermediateField.fixingSubgroupEquiv K).symm x) : SSGRoute.GalQ)
        + z (↑((IntermediateField.fixingSubgroupEquiv K).symm y) : SSGRoute.GalQ)
    rw [h1]
    exact hzadd _ ((IntermediateField.fixingSubgroupEquiv K).symm x).2 _
      ((IntermediateField.fixingSubgroupEquiv K).symm y).2
  · exact ges_isLocConstOn_transport K hzloc
  · intro A hA δ hδ
    have hmem : (↑((IntermediateField.fixingSubgroupEquiv K).symm δ) : SSGRoute.GalQ)
        ∈ SSGRoute.decomp ℚ A ⊓ K.fixingSubgroup :=
      ⟨ges_decomp_of_mem K A δ hδ, ((IntermediateField.fixingSubgroupEquiv K).symm δ).2⟩
    have h1 : z (↑((IntermediateField.fixingSubgroupEquiv K).symm δ) : SSGRoute.GalQ)
        = gesLocalDatum K f A
          (↑((IntermediateField.fixingSubgroupEquiv K).symm δ) : SSGRoute.GalQ) := by
      have h2 := hzpres A hA
        (↑((IntermediateField.fixingSubgroupEquiv K).symm δ) : SSGRoute.GalQ) hmem
      simpa using h2
    show z (↑((IntermediateField.fixingSubgroupEquiv K).symm δ) : SSGRoute.GalQ) = f A δ
    rw [h1, gesLocalDatum_apply K f A _ ((IntermediateField.fixingSubgroupEquiv K).symm δ).2,
      ges_apply_symm K δ]
  · intro B hBfin hBconj hBsplit δ hδI
    have hnotT : ∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B := by
      intro A hA hconj
      exact hBconj A hA ((ges_isConjPlace_iff K A B).mpr hconj)
    have hnotQ : ¬ Work.SSGRoute.gesKConj K Q B := by
      rintro ⟨τ, hτ, hτQ⟩
      exact hBsplit (ges_isSplitIn_smul L Q B τ hτQ hQsplitL)
    exact hzunr B ((local_transport_isFinPlace K B).mp hBfin) hnotT hnotQ
      (↑((IntermediateField.fixingSubgroupEquiv K).symm δ) : SSGRoute.GalQ)
      ((IntermediateField.fixingSubgroupEquiv K).symm δ).2
      (ges_isInertia_of_mem K B δ hδI)

end Work.SSGRoute
