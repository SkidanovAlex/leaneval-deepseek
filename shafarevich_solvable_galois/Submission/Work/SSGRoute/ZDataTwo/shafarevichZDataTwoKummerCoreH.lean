import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ZSplit.FrobeniusValue
import Submission.Work.SSG8Escape.escape_prime_ssg8
import Submission.Work.SSG8Escape.class_field_data_ssg8
import Submission.Work.SSGRoute.ZConstruction.exists_abelianArtin_localFactors
import Submission.Work.SSGRoute.ZDataTwo.ThreeHalves
import Submission.Work.SSGRoute.ZDataTwo.mu2EscapeRealisationH
import Submission.Work.SSGRoute.ZDataTwo.mu2ThreeHalves

namespace Work.SSGRoute.ZDataTwo

open scoped Pointwise

theorem shafarevichZDataTwoKummerCoreH (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (2 : Ω) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (2 : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0) :
    ∃ b : (↥K)ˣ,
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B →
          nodeKummerCochar K ζ hζK hζ b σ = y σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → nodeKummerCochar K ζ hζK hζ b c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ →
          nodeKummerCochar K ζ hζK hζ b σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
        (∃ σ, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧
          nodeKummerCochar K ζ hζK hζ b σ ≠ 0) →
        ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q →
          (¬ ∃ τ ∈ K.fixingSubgroup, τ • B = Q) →
          ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup, nodeKummerCochar K ζ hζK hζ b τ = 0) := by
  classical
  obtain ⟨Pset, b, hPfin, hPsplit, hPnotS, hagree, hinv, hconf, hconj⟩ :=
    mu2ThreeHalves k Ω K Λ hKΛ ζ hζ hζK S hSfin hSdisj hSram y hy hyc hyS hyT hy0 hyinf
      (fun T hTfin hTdisj hTcov g hg hgc hgram h hh hhc horth hinertia hginf hhhinf =>
        mu2EscapeRealisationH k Ω K Λ hKΛ ζ hζ hζK T hTfin hTdisj hTcov g hg hgc hgram
          h hh hhc horth hinertia hginf hhhinf)
  exact kummerCore_of_three_halves K Λ hKΛ ζ hζ hζK S Pset hPfin hPsplit hPnotS y b
    hagree hinv hconf hconj

end Work.SSGRoute.ZDataTwo

/-!
# The `p = 2`-applicable escape prime (with the unused `hKimag` deleted)

`Work.SSG8Escape.escape_prime_ssg8` is the Čebotarev step of the Grünwald-with-escape correction: it
produces a prime `Q`, completely split in `L₁ ⊔ L₂`, outside the `G_K`-classes of `T`, realising a
prescribed class in `U_p = gesU_K(p,T')`.  Its statement carries the hypothesis

`hKimag : p = 2 → ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → c = 1`

which is *false* at `p = 2` whenever `K` has a real place — but the proof of that theorem never
mentions `hKimag` (it is a copy of the odd-`p` binder).  The statement below is that theorem with the
binder deleted; it is the escape prime the `p = 2` branch of Schmidt--Wingberg §4 needs (the odd-`p`
lane can supply `hKimag`, the `p = 2` lane cannot).
-/

namespace Work.SSG8Escape

open scoped Pointwise
open NumberField IsDedekindDomain
open NK.GlobalCFT
open Work.SSGRoute

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-- **The escape prime, with no hypothesis on the involutions of `G_K`, for an arbitrary
finite-index open modulus `V ≤ C_↥K`.**

Identical to `Work.SSG8Escape.escape_prime_ssg8` with the (unused) hypothesis
`hKimag : p = 2 → ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → c = 1` removed — so that it applies at
`p = 2` — and with its hard-coded modulus `gesUPow ↥K p T'` replaced by an *arbitrary* subgroup
`V ≤ C_↥K` supplied together with `hM : N_{M/↥K} C_M = V`.  The `p = 2` narrow-modulus route takes
`V = narrowGesU ↥K 2 T' ⊔ C_↥K²`, which is what makes the correcting class of
`Work.SSGRoute.H9.correctionFromPrime_narrow` totally positive; only the Artin-data clauses of the
class field `M` and the orthogonality `hαfix` are hypotheses here, so the conclusion is purely a
Čebotarev/class-field-theory statement about `V`. -/
theorem escape_prime_ssg8_noImag (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (L₁ L₂ : IntermediateField k Ω) [FiniteDimensional k L₁] [IsGalois k L₁]
    [FiniteDimensional k L₂] [IsGalois k L₂] (hKL₁ : K ≤ L₁) (hKL₂ : K ≤ L₂)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (T' : Finset (NK.Chebotarev.PrimeIdeal ↥K))
    (hTbelow : ∀ A ∈ T, ∃ 𝔭 ∈ T', A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (hT'below : ∀ 𝔭 ∈ T', ∃ A ∈ T, A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
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
    (a : (↥K)ˣ)
    (ha : ∀ A ∈ T, ∀ σ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
      g (σ : Ω ≃ₐ[k] Ω) + h A (σ : Ω ≃ₐ[k] Ω) =
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ a
          (Work.SSGRoute.gesLocalToGalK K σ))
    (hc : NK.Reconstruct.ChebotarevDensityInput k Ω)
    (M : IntermediateField ↥K Ω) [FiniteDimensional ↥K M] [IsGalois ↥K M] [NumberField ↥M]
    (V : Subgroup (NK.GlobalCFT.IdeleClassGroup ↥K))
    (hM : NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥M = V)
    (hcomm : ∀ a b : (↥M ≃ₐ[↥K] ↥M), a * b = b * a)
    (art : NK.GlobalCFT.Idele ↥K →* (↥M ≃ₐ[↥K] ↥M))
    (hker : art.ker = NK.GlobalCFT.Idele.normImage ↥K ↥M ⊔ NK.GlobalCFT.Idele.principalSubgroup ↥K)
    (hfrob : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥K,
      NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥M) 𝔮 →
      art (NK.HeckeL.ideleOfPrime ↥K 𝔮) = NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥M) 𝔮)
    (α : ↥M ≃ₐ[↥K] ↥M)
    (hα : art (NK.NUV2.RouteB.RayModulus.fracIdele
      (Work.SSGRoute.tFreePart (K := ↥K) T' a)) = α)
    (hαfix : ∀ x : ↥M, ((x : Ω) ∈ (L₁ ⊔ L₂)) → α x = x) :
    ∃ (Q : ValuationSubring Ω) (𝔮 : NK.Chebotarev.PrimeIdeal ↥K),
      SSGRoute.IsFinPlace k Q ∧ SSGRoute.IsSplitIn k (L₁ ⊔ L₂) Q ∧ 𝔮 ∉ T' ∧
      NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥M) 𝔮 ∧
      Q.comap (algebraMap ↥K Ω) = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔮 ∧
      (∀ A ∈ T, ∀ τ ∈ K.fixingSubgroup, τ • A ≠ Q) ∧
      NK.GlobalCFT.IdeleClassGroup.mk ↥K (NK.HeckeL.ideleOfPrime ↥K 𝔮) *
        NK.GlobalCFT.IdeleClassGroup.mk ↥K
          (NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart (K := ↥K) T' a)) ∈
        V := by
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  haveI : Normal k Ω := IsAlgClosure.normal k Ω
  -- `α⁻¹` also fixes `M ⊓ (L₁ ⊔ L₂)` pointwise
  have hα'inv : ∀ x : ↥M, ((x : Ω) ∈ (L₁ ⊔ L₂)) → α⁻¹ x = x := by
    intro x hx
    have h := hαfix x hx
    have h2 : α⁻¹ x = α⁻¹ (α x) := (congrArg (fun y => α⁻¹ y) h).symm
    rw [h2]
    exact α.symm_apply_apply x
  have hKΛ : K ≤ L₁ ⊔ L₂ := le_trans hKL₁ le_sup_left
  haveI hfdΛ : FiniteDimensional k ↥(L₁ ⊔ L₂) := IntermediateField.finiteDimensional_sup L₁ L₂
  haveI hgalΛ : IsGalois k ↥(L₁ ⊔ L₂) := inferInstance
  -- ### Step 1: a finite Galois extension of `k` containing `K`, `M` and `L₁ ⊔ L₂`
  let Mk : IntermediateField k Ω := M.restrictScalars k
  have hMk : (Mk : Set Ω) = (M : Set Ω) := IntermediateField.coe_restrictScalars k (E := M)
  haveI hfdMk : FiniteDimensional k Mk := by
    haveI : FiniteDimensional k ↥M := FiniteDimensional.trans k ↥K ↥M
    exact ‹FiniteDimensional k ↥M›
  obtain ⟨L, hLd, hLg, hKL, hMLk, hΛL⟩ :=
    EscapeCoreLib.exists_finiteDimensional_galois_superset K Mk (L₁ ⊔ L₂)
  haveI : FiniteDimensional k L := hLd
  haveI : IsGalois k L := hLg
  have hMLset : ∀ x : Ω, x ∈ M → x ∈ L := fun x hx => hMLk (by
    show x ∈ (Mk : Set Ω); rw [hMk]; exact hx)
  -- ### Step 2: transport `M` and `L₁ ⊔ L₂` into the `↥K`-extension `LK`
  let LK : IntermediateField ↥K Ω := EscapeCoreLib.baseChange K L hKL
  haveI htow_k_LK_Ω : IsScalarTower k ↥LK Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI htow_k_K_LK : IsScalarTower k ↥K ↥LK := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsGalois k ↥LK := IsGalois.of_algEquiv (EscapeCoreLib.baseChangeAlgEquiv K L hKL)
  haveI : IsGalois ↥K LK := EscapeCoreLib.isGalois_baseChange K L hKL
  haveI : FiniteDimensional k ↥LK := EscapeCoreLib.finiteDimensional_baseChange K L hKL
  haveI : FiniteDimensional ↥K ↥LK := Module.Finite.of_restrictScalars_finite k ↥K ↥LK
  let NKf : IntermediateField ↥K Ω := EscapeCoreLib.baseChange K (L₁ ⊔ L₂) hKΛ
  haveI : IsGalois ↥K NKf := EscapeCoreLib.isGalois_baseChange K (L₁ ⊔ L₂) hKΛ
  haveI : FiniteDimensional k ↥NKf := EscapeCoreLib.finiteDimensional_baseChange K (L₁ ⊔ L₂) hKΛ
  haveI : FiniteDimensional ↥K ↥NKf := Module.Finite.of_restrictScalars_finite k ↥K ↥NKf
  have hMLK : M ≤ LK := fun x hx => (EscapeCoreLib.mem_baseChange K L hKL).mpr (hMLk (by
    show x ∈ (Mk : Set Ω); rw [hMk]; exact hx))
  have hNKLK : NKf ≤ LK := fun x hx =>
    (EscapeCoreLib.mem_baseChange K L hKL).mpr (hΛL ((EscapeCoreLib.mem_baseChange K (L₁ ⊔ L₂) hKΛ).mp hx))
  let ML : IntermediateField ↥K ↥LK := M.comap (IsScalarTower.toAlgHom ↥K ↥LK Ω)
  let NLc : IntermediateField ↥K ↥LK := NKf.comap (IsScalarTower.toAlgHom ↥K ↥LK Ω)
  haveI : IsGalois ↥K ML := EscapeCoreLib.isGalois_comap_of_le_over K LK M hMLK
  haveI : IsGalois ↥K NLc := EscapeCoreLib.isGalois_comap_of_le_over K LK NKf hNKLK
  haveI : FiniteDimensional ↥K ↥ML :=
    FiniteDimensional.of_injective (EscapeCoreLib.comapAlgEquiv K LK M hMLK).symm.toLinearEquiv.toLinearMap
      (EscapeCoreLib.comapAlgEquiv K LK M hMLK).symm.injective
  haveI : FiniteDimensional ↥K ↥NLc :=
    FiniteDimensional.of_injective (EscapeCoreLib.comapAlgEquiv K LK NKf hNKLK).symm.toLinearEquiv.toLinearMap
      (EscapeCoreLib.comapAlgEquiv K LK NKf hNKLK).symm.injective
  -- ### Step 3: extend `α⁻¹` to a `↥K`-automorphism of `LK` fixing `NLc`
  let e := EscapeCoreLib.comapAlgEquiv K LK M hMLK
  let α' : ↥ML ≃ₐ[↥K] ↥ML := e.symm.trans ((α⁻¹).trans e)
  have hα'fix : ∀ x : ↥ML, ((x : ↥LK) ∈ NLc) → (((α' x : ↥ML) : ↥LK)) = (x : ↥LK) := by
    intro x hx
    refine Subtype.ext ?_
    have hxN : ((x : ↥LK) : Ω) ∈ NKf := hx
    exact EscapeCoreLib.comapAlgEquiv_transport K LK M NKf hMLK (α⁻¹)
      (fun y hy => congrArg (fun z : ↥M => (z : Ω))
        (hα'inv y ((EscapeCoreLib.mem_baseChange K (L₁ ⊔ L₂) hKΛ).mp hy))) x hxN
  obtain ⟨g, hgML, hgNL⟩ :=
    EscapeCoreLib.exists_algEquiv_restrict_eq_of_fixing (K := ↥K) (L := ↥LK) ML NLc α' hα'fix
  -- ### Step 4: lift the `↥K`-automorphism of `LK` to a `k`-automorphism `τ` of `Ω`
  let gk : ↥LK ≃ₐ[k] ↥LK := g.restrictScalars k
  have hgk_apply : ∀ y : ↥LK, gk y = g y := fun y => rfl
  obtain ⟨τ, hτ⟩ := AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := ↥LK) (E := Ω) gk
  -- ### Step 5: `τ` acts as `α⁻¹` on `M` and fixes `L₁ ⊔ L₂`
  have hτN : SSGRoute.res k (L₁ ⊔ L₂) τ = 1 := by
    rw [show SSGRoute.res k (L₁ ⊔ L₂) τ = AlgEquiv.restrictNormalHom ↥(L₁ ⊔ L₂) τ from rfl,
      ← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker,
      IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hxL : x ∈ L := hΛL hx
    have hxLK : x ∈ LK := (EscapeCoreLib.mem_baseChange K L hKL).mpr hxL
    have hxNK : x ∈ NKf := (EscapeCoreLib.mem_baseChange K (L₁ ⊔ L₂) hKΛ).mpr hx
    have hxNL : (⟨x, hxLK⟩ : ↥LK) ∈ NLc := hxNK
    have hτx : τ x = (((gk ⟨x, hxLK⟩ : ↥LK)) : Ω) := by
      have h1 : ((((AlgEquiv.restrictNormalHom ↥LK τ)) ⟨x, hxLK⟩ : ↥LK) : Ω) = τ x :=
        AlgEquiv.restrictNormal_commutes τ ↥LK ⟨x, hxLK⟩
      have hy : (AlgEquiv.restrictNormalHom ↥LK τ) ⟨x, hxLK⟩ = gk ⟨x, hxLK⟩ :=
        congrArg (fun f => f ⟨x, hxLK⟩) hτ
      rw [← h1, hy]
    have hgx : (((g ⟨x, hxLK⟩ : ↥LK)) : Ω) = x := by
      have h := congrArg (fun (z : ↥LK) => (z : Ω)) (hgNL _ hxNL)
      simpa using h
    rw [hτx, hgk_apply, hgx]
  have hτM : ∀ x : ↥M, τ (x : Ω) = (((α⁻¹) x : ↥M) : Ω) := by
    intro x
    have hxL : (x : Ω) ∈ L := hMLset x x.2
    have hxLK : (x : Ω) ∈ LK := (EscapeCoreLib.mem_baseChange K L hKL).mpr hxL
    have hτx : τ (x : Ω) = (((gk ⟨(x : Ω), hxLK⟩ : ↥LK)) : Ω) := by
      have h1 : ((((AlgEquiv.restrictNormalHom ↥LK τ)) ⟨(x : Ω), hxLK⟩ : ↥LK) : Ω) = τ (x : Ω) :=
        AlgEquiv.restrictNormal_commutes τ ↥LK ⟨(x : Ω), hxLK⟩
      have hy : (AlgEquiv.restrictNormalHom ↥LK τ) ⟨(x : Ω), hxLK⟩ = gk ⟨(x : Ω), hxLK⟩ :=
        congrArg (fun f => f ⟨(x : Ω), hxLK⟩) hτ
      rw [← h1, hy]
    rw [hτx, hgk_apply]
    have hzx : (((e x : ↥ML)) : ↥LK) = ⟨(x : Ω), hxLK⟩ := by
      refine Subtype.ext ?_
      rw [EscapeCoreLib.comapAlgEquiv_coe]
    have hgval : (((g ⟨(x : Ω), hxLK⟩ : ↥LK)) : Ω) = ((((α' (e x) : ↥ML)) : ↥LK) : Ω) := by
      have h1 : g ⟨(x : Ω), hxLK⟩ = ((α' (e x) : ↥ML) : ↥LK) := by
        rw [← hzx]
        exact hgML (e x)
      exact congrArg (fun (z : ↥LK) => (z : Ω)) h1
    rw [hgval]
    have hα'x : α' (e x) = e ((α⁻¹) x) := by
      simp only [α', AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
    rw [hα'x]
    exact EscapeCoreLib.comapAlgEquiv_coe K LK M hMLK ((α⁻¹) x)
  have hτΛ : τ ∈ (L₁ ⊔ L₂).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have h1 : τ.restrictNormal ↥(L₁ ⊔ L₂) = 1 := by
      rw [show SSGRoute.res k (L₁ ⊔ L₂) τ = τ.restrictNormal ↥(L₁ ⊔ L₂) from rfl] at hτN
      exact hτN
    exact (AlgEquiv.restrictNormal_eq_one_iff (L₁ ⊔ L₂) τ).mp h1 x hx
  -- ### Step 6: the escape place
  obtain ⟨Q, pp, 𝔮, hQfin, hsplit, havoid, hQp, hpT, hQ𝔮, hunr, hF⟩ :=
    escapePlace_ssg8 k Ω K M (L₁ ⊔ L₂) L hKL hMLset hΛL hKΛ τ α⁻¹ hτM hτΛ hc T
  refine ⟨Q, 𝔮, hQfin, hsplit, ?_, hunr, hQ𝔮, ?_, ?_⟩
  · -- `𝔮 ∉ T'`
    intro h𝔮T'
    obtain ⟨A, hA, hA𝔮⟩ := hT'below 𝔮 h𝔮T'
    have h1 : A.comap (algebraMap k Ω) =
        (A.comap (algebraMap ↥K Ω)).comap (algebraMap k ↥K) :=
      (ValuationSubring.comap_comap A (algebraMap ↥K Ω) (algebraMap k ↥K)).symm
    have h2 : Q.comap (algebraMap k Ω) =
        (Q.comap (algebraMap ↥K Ω)).comap (algebraMap k ↥K) :=
      (ValuationSubring.comap_comap Q (algebraMap ↥K Ω) (algebraMap k ↥K)).symm
    have hcomap : A.comap (algebraMap k Ω) = Q.comap (algebraMap k Ω) := by
      rw [h1, h2, hA𝔮, hQ𝔮]
    exact hpT A hA (by rw [hcomap, hQp])
  · -- the `K`-conjugacy clause
    intro A hA τ' hτ' hτ'A
    exact havoid A hA ⟨τ', hτ'A⟩
  · -- the class membership
    exact EscapeCoreLib.memGesUOfIsFrobAtPrime (↥M) hcomm
      V hM art hker hfrob
      (NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart (K := ↥K) T' a))
      α hα 𝔮 hunr hF

end Work.SSG8Escape

namespace Work.SSG8Escape

open scoped Pointwise
open NumberField IsDedekindDomain
open NK.GlobalCFT

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

/-- **The class-field data of an arbitrary open finite-index modulus `V ≤ C_↥K`.**

`Work.SSG8Escape.class_field_data_ssg8` is the instance `V = gesUPow ↥K p T'` of this statement.
Stating it for an arbitrary open finite-index `V` is what the narrow (`p = 2`) route needs: with
`V = narrowGesU ↥K 2 T' ⊔ C_↥K²` the resulting class field `M` is the one to which
`Work.H9Narrow.orthogonality_narrow_L2K` and the escape prime
`Work.SSG8Escape.escape_prime_ssg8_noImag` (general modulus) are applied. -/
theorem class_field_data_general {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (V : Subgroup (IdeleClassGroup ↥K)) (hVfin : V.FiniteIndex)
    (hVopen : IsOpen (V : Set (IdeleClassGroup ↥K))) :
    ∃ (M : IntermediateField ↥K Ω) (_ : FiniteDimensional ↥K M) (_ : IsGalois ↥K M)
      (_ : NumberField ↥M) (_ : IsMulCommutative (↥M ≃ₐ[↥K] ↥M))
      (art : Idele ↥K →* (↥M ≃ₐ[↥K] ↥M)),
      Idele.normClassSubgroup ↥K ↥M = V ∧
      art.ker = Idele.normImage ↥K ↥M ⊔ Idele.principalSubgroup ↥K ∧
      (∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥K,
        NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥M) 𝔮 →
        art (NK.HeckeL.ideleOfPrime ↥K 𝔮) = NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥M) 𝔮) := by
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  obtain ⟨M, hfdM, hgalM, hnfM, hcommM, hnormM⟩ :=
    exists_abelian_classField_open (K := K) (U := V) hVfin hVopen
  haveI : FiniteDimensional ↥K M := hfdM
  haveI : IsGalois ↥K M := hgalM
  haveI : NumberField ↥M := hnfM
  haveI : IsMulCommutative (↥M ≃ₐ[↥K] ↥M) := hcommM
  obtain ⟨art : Idele ↥K →* (↥M ≃ₐ[↥K] ↥M), hartker, -, -, -, hartfrob, -⟩ :=
    Work.SSGRoute.ZConstruction.exists_abelianArtin_localFactors (K := ↥K) (L := ↥M)
      (fun a b => mul_comm' a b)
  exact ⟨M, hfdM, hgalM, hnfM, hcommM, art, hnormM, hartker, hartfrob⟩

end Work.SSG8Escape
