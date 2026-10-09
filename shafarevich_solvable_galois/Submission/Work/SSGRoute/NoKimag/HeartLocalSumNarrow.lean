import Mathlib
import Submission.Work.SSGRoute.N2v2.heart_chi1_part
import Submission.Work.SSGRoute.N2v2.heart_chi2_part
import Submission.Work.SSGRoute.N2v2.heart_gsum_vanishes
import Submission.Work.SSGRoute.NoKimag.HeartGsumNarrow
import Submission.Work.SSGRoute.H9.two_heart
import Submission.Work.SSGRoute.ZDataTwo.OrthTwoArchIn
import Submission.Work.SSGRoute.N2v2.exists_kummerChar_level
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The heart of the escape orthogonality

The two halves `heart_chi1_part` and `heart_chi2_part` have the same shape, so the heart is the
bookkeeping `χE = χE₁ · χE₂`: the characters `χEᵢ` are the descents of the Kummer characters of the
split elements `cᵢ` (`exists_kummerChar_level`), and the identity `χE = χE₁ * χE₂` follows from
`hsplitc` on the fixing subgroup together with the surjectivity of `AlgEquiv.restrictNormalHom`.
-/

open scoped Pointwise
open NumberField IsDedekindDomain
open NK.GlobalCFT

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.SSGRoute.N2v2

/-- **The heart of the escape orthogonality**: for the level `E` (abelian of exponent `p`) with its
local Artin factors `θ`, the sum over `T'` of the `χ_E`-values of the local factors of the Grünwald
element `a` vanishes. -/
theorem HeartLocalSumNarrow (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2)
    (L₁ L₂ : IntermediateField k Ω) [FiniteDimensional k L₁] [IsGalois k L₁]
    [FiniteDimensional k L₂] [IsGalois k L₂] (hKL₁ : K ≤ L₁) (hKL₂ : K ≤ L₂)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, _root_.SSGRoute.IsFinPlace k A)
    (T' : Finset (NK.Chebotarev.PrimeIdeal ↥K))
    (hTbelow : ∀ A ∈ T, ∃ 𝔭 ∈ T', A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (hT'above : ∀ 𝔭 ∈ T', ∃ A ∈ T, A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (hTcov : ∀ B : ValuationSubring Ω, _root_.SSGRoute.IsFinPlace k B →
      (B.valuation (2 : Ω) < 1 ∨
        (∃ σ ∈ K.fixingSubgroup, _root_.SSGRoute.IsInertia k B σ ∧ σ ∉ L₁.fixingSubgroup) ∨
        (∃ σ ∈ K.fixingSubgroup, _root_.SSGRoute.IsInertia k B σ ∧ σ ∉ L₂.fixingSubgroup)) →
      ∃ A ∈ T, ∃ τ ∈ K.fixingSubgroup, τ • A = B)
    (g : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hg : ∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, g (x * y) = g x + g y)
    (hgc : _root_.SSGRoute.IsLocConstOn K.fixingSubgroup g)
    (hginf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → g c = 0)
    (hgram : ∀ B : ValuationSubring Ω, _root_.SSGRoute.IsFinPlace k B →
      (∀ A ∈ T, ∀ τ ∈ K.fixingSubgroup, τ • A ≠ B) → ¬ _root_.SSGRoute.IsSplitIn k L₁ B →
      ∀ σ ∈ K.fixingSubgroup, _root_.SSGRoute.IsInertia k B σ → g σ = 0)
    (h : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hh : ∀ A ∈ T, ∀ x ∈ _root_.SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      ∀ y ∈ _root_.SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A (x * y) = h A x + h A y)
    (horth₁ : ∀ A ∈ T,
      (∀ σ ∈ _root_.SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A σ = 0) ∨
      (∀ χ : (Ω ≃ₐ[k] Ω) → ZMod 2,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
        (∀ σ ∈ L₁.fixingSubgroup, χ σ = 0) →
        ∀ σ ∈ _root_.SSGRoute.decomp k A ⊓ K.fixingSubgroup, χ σ = 0) ∨
      ((∀ σ ∈ K.fixingSubgroup, _root_.SSGRoute.IsInertia k A σ → h A σ = 0) ∧
        ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod 2,
          (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
          (∀ σ ∈ L₁.fixingSubgroup, χ σ = 0) →
          ∀ σ ∈ K.fixingSubgroup, _root_.SSGRoute.IsInertia k A σ → χ σ = 0))
    (horth₂ : ∀ A ∈ T,
      (∀ σ ∈ _root_.SSGRoute.decomp k A ⊓ K.fixingSubgroup, g σ + h A σ = 0) ∨
      (∀ χ : (Ω ≃ₐ[k] Ω) → ZMod 2,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
        (∀ σ ∈ L₂.fixingSubgroup, χ σ = 0) →
        ∀ σ ∈ _root_.SSGRoute.decomp k A ⊓ K.fixingSubgroup, χ σ = 0) ∨
      ((∀ σ ∈ K.fixingSubgroup, _root_.SSGRoute.IsInertia k A σ → g σ + h A σ = 0) ∧
        ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod 2,
          (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
          (∀ σ ∈ L₂.fixingSubgroup, χ σ = 0) →
          ∀ σ ∈ K.fixingSubgroup, _root_.SSGRoute.IsInertia k A σ → χ σ = 0))
    (a : (↥K)ˣ)
    (ha : ∀ A ∈ T, ∀ σ : ↥(_root_.SSGRoute.decomp k A ⊓ K.fixingSubgroup),
      g (σ : Ω ≃ₐ[k] Ω) + h A (σ : Ω ≃ₐ[k] Ω) =
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ a
          (Work.SSGRoute.gesLocalToGalK K σ))
    (E : IntermediateField ↥K Ω) [FiniteDimensional ↥K E] [IsGalois ↥K E]
    [IsMulCommutative (↥E ≃ₐ[↥K] ↥E)]
    (hexpE : ∀ σ : ↥E ≃ₐ[↥K] ↥E, σ ^ 2 = 1)
    (θ : (v : NK.GlobalCFT.Place ↥K) →
      (NK.GlobalCFT.Place.localField ↥K v)ˣ →* (↥E ≃ₐ[↥K] ↥E))
    (hθker : ∀ v, (θ v).ker = NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥E) v)
    (hθprod : ∀ (x : (↥K)ˣ) (s : Finset (NK.GlobalCFT.Place ↥K)),
      (∀ v, v ∉ s → θ v (NK.CFTLib.IdeleHasse.localImageAt v x) = 1) →
      NK.CFTLib.IdeleHasse.cprod (fun a b => mul_comm' a b) s
        (fun v => θ v (NK.CFTLib.IdeleHasse.localImageAt v x)) = 1)
    (hlift : ∀ (A : ValuationSubring Ω) (hA : _root_.SSGRoute.IsFinPlace k A)
      (𝔭 : NK.Chebotarev.PrimeIdeal ↥K),
      A.comap (algebraMap ↥K Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 →
      ∀ x : (↥K)ˣ, ∃ σ : Ω ≃ₐ[↥K] Ω, σ ∈ _root_.SSGRoute.decomp (k := ↥K) A ∧
        AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E σ =
          θ (NK.GlobalCFT.Place.ofFinite 𝔭)
            (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) x))
    (hunith : ∀ (A : ValuationSubring Ω) (hA : _root_.SSGRoute.IsFinPlace k A)
      (𝔭 : NK.Chebotarev.PrimeIdeal ↥K),
      A.comap (algebraMap ↥K Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 →
      ∀ u : (NK.GlobalCFT.Place.localField ↥K (NK.GlobalCFT.Place.ofFinite 𝔭))ˣ,
        u ∈ NK.GlobalCFT.Place.localUnits ↥K (NK.GlobalCFT.Place.ofFinite 𝔭) →
        ∃ σ : Ω ≃ₐ[↥K] Ω, _root_.SSGRoute.IsInertia k A (σ.restrictScalars k) ∧
          AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E σ =
            θ (NK.GlobalCFT.Place.ofFinite 𝔭) u)
    (hdiagLift : ∀ 𝔭 ∈ T', ∃ σ₀ : Ω ≃ₐ[↥K] Ω,
      ∀ (y : (↥K)ˣ), NK.LocalAnabelian.kummerField (K' := Ω) 2 y ≤ E →
      ∀ τ : Ω ≃ₐ[↥K] Ω,
        AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E τ =
          θ (NK.GlobalCFT.Place.ofFinite 𝔭)
            (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) y) →
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ y τ =
          Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ y σ₀)
    (hgE : ∀ σ : Ω ≃ₐ[↥K] Ω, σ ∈ E.fixingSubgroup → g (σ.restrictScalars k) = 0)
    (hFaE : NK.LocalAnabelian.kummerField (K' := Ω) 2 a ≤ E)
    (c : (↥K)ˣ) (hcE : NK.LocalAnabelian.kummerField (K' := Ω) 2 c ≤ E)
    (c₁ c₂ : (↥K)ˣ)
    (hc₁E : NK.LocalAnabelian.kummerField (K' := Ω) 2 c₁ ≤ E)
    (hc₂E : NK.LocalAnabelian.kummerField (K' := Ω) 2 c₂ ≤ E)
    (hc₁L : NK.LocalAnabelian.kummerField (K' := Ω) 2 c₁ ≤
      Work.SSGRoute.EscapeCoreLib.baseChange K L₁ hKL₁)
    (hc₂L : NK.LocalAnabelian.kummerField (K' := Ω) 2 c₂ ≤
      Work.SSGRoute.EscapeCoreLib.baseChange K L₂ hKL₂)
    (hsplitc : ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup),
      Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ c
          ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩)
        = Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ c₁
            ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩)
          + Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ c₂
            ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩))
    (χE : (↥E ≃ₐ[↥K] ↥E) →* Multiplicative (ZMod 2))
    (hχE : ∀ σ : Ω ≃ₐ[↥K] Ω,
      χE (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E σ) =
        Multiplicative.ofAdd
          (Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ c σ)) :
    ∑ 𝔭 ∈ T', (χE (θ (NK.GlobalCFT.Place.ofFinite 𝔭)
      (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) a))).toAdd
      = 0 := by
  classical
  -- the two descents
  obtain ⟨χE₁, hχE₁⟩ := exists_kummerChar_level 2 k Ω K ζ hζ E c₁ hc₁E
  obtain ⟨χE₂, hχE₂⟩ := exists_kummerChar_level 2 k Ω K ζ hζ E c₂ hc₂E
  -- the two-disjunct forms of `hTcov`
  have hTcov1 : ∀ B : ValuationSubring Ω, _root_.SSGRoute.IsFinPlace k B →
      (B.valuation (2 : Ω) < 1 ∨
        (∃ σ ∈ K.fixingSubgroup, _root_.SSGRoute.IsInertia k B σ ∧ σ ∉ L₁.fixingSubgroup)) →
      ∃ A ∈ T, ∃ τ ∈ K.fixingSubgroup, τ • A = B := by
    rintro B hB (h1 | ⟨σ, hσ, hinert, hnot⟩)
    · exact hTcov B hB (Or.inl h1)
    · exact hTcov B hB (Or.inr (Or.inl ⟨σ, hσ, hinert, hnot⟩))
  have hTcov2 : ∀ B : ValuationSubring Ω, _root_.SSGRoute.IsFinPlace k B →
      (B.valuation (2 : Ω) < 1 ∨
        (∃ σ ∈ K.fixingSubgroup, _root_.SSGRoute.IsInertia k B σ ∧ σ ∉ L₂.fixingSubgroup)) →
      ∃ A ∈ T, ∃ τ ∈ K.fixingSubgroup, τ • A = B := by
    rintro B hB (h1 | ⟨σ, hσ, hinert, hnot⟩)
    · exact hTcov B hB (Or.inl h1)
    · exact hTcov B hB (Or.inr (Or.inr ⟨σ, hσ, hinert, hnot⟩))
  -- the datum `g` is the Kummer character of a global unit `bg`
  obtain ⟨bg, hbg⟩ :=
    Work.SSGRoute.ZDataMup.KummerSurjectivity.kummerCharZMod_surjective_levelK 2 k Ω K ζ hζ g hg hgc
  -- the involutions condition gives the total positivity of `bg`, hence the archimedean input
  have hbginf : ∀ (c' : Ω ≃ₐ[k] Ω) (hc' : c' ∈ K.fixingSubgroup), c' ^ 2 = 1 →
      Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ bg
        (Work.SSGRoute.gesGalKOfFixing K c' hc') = 0 := by
    intro c' hc' hc'2
    have h1 : Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ bg
        (Work.SSGRoute.gesGalKOfFixing K c' hc') = g c' := (hbg c' hc').symm
    rw [h1]
    exact hginf c' hc' hc'2
  have harchbg : ∀ w : NumberField.InfinitePlace ↥K,
      NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofInfinite w) bg ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥E)
          (NK.GlobalCFT.Place.ofInfinite w) :=
    Work.SSGRoute.ZDataTwo.arch_localNorm_of_involution_condition k Ω K ζ hζ bg E hbginf
  -- the `χ₂`-part
  have h2 := Work.SSGRoute.N2v2.heart_chi2_part 2 k Ω K ζ hζ L₂ hKL₂ T hTfin T' hT'above g h horth₂ a ha
    E hexpE θ hlift hunith c₂ hc₂E hc₂L χE₂ hχE₂
  -- the `g`-sum
  have hgsum : ∑ 𝔭 ∈ T', (χE₁ (θ (NK.GlobalCFT.Place.ofFinite 𝔭)
      (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) bg))).toAdd
      = 0 :=
    Work.SSGRoute.N2v2.HeartGsumNarrow 2 k Ω K ζ hζ L₁ hKL₁ T hTfin T' hTbelow hTcov1 g hg hgc hgram
      E hexpE θ hθker hθprod hlift hunith hgE bg hbg harchbg c₁ hc₁E hc₁L χE₁ hχE₁
  -- the `χ₁`-part
  have h1 := Work.SSGRoute.N2v2.heart_two_sum 2 k Ω K ζ hζ L₁ hKL₁ T hTfin T' hTbelow hT'above hTcov1 g hg hgc
    hgram h hh horth₁ a ha E hexpE θ hlift hunith hdiagLift hgE hFaE
    bg hbg c₁ hc₁E hc₁L χE₁ hχE₁ hgsum
  -- the split of the character, per place
  have hsplit_sum : ∀ 𝔭 ∈ T',
      (χE (θ (NK.GlobalCFT.Place.ofFinite 𝔭)
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) a))).toAdd
      = (χE₁ (θ (NK.GlobalCFT.Place.ofFinite 𝔭)
          (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) a))).toAdd
        + (χE₂ (θ (NK.GlobalCFT.Place.ofFinite 𝔭)
          (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) a))).toAdd := by
    intro 𝔭 h𝔭
    obtain ⟨A, hAT, hAcomap⟩ := hT'above 𝔭 h𝔭
    obtain ⟨σ, hσdec, hσeq⟩ := hlift A (hTfin A hAT) 𝔭 hAcomap a
    have hσK : σ.restrictScalars k ∈ K.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact σ.commutes ⟨x, hx⟩
    have hσ1 : (χE (θ (NK.GlobalCFT.Place.ofFinite 𝔭)
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) a))).toAdd
        = Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ c σ := by
      rw [← hσeq, hχE σ]
      rfl
    have hσ2 : (χE₁ (θ (NK.GlobalCFT.Place.ofFinite 𝔭)
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) a))).toAdd
        = Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ c₁ σ := by
      rw [← hσeq, hχE₁ σ]
      rfl
    have hσ3 : (χE₂ (θ (NK.GlobalCFT.Place.ofFinite 𝔭)
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) a))).toAdd
        = Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ c₂ σ := by
      rw [← hσeq, hχE₂ σ]
      rfl
    rw [hσ1, hσ2, hσ3]
    rw [← fixingSubgroupEquiv_restrictScalars_apply K σ hσK]
    exact hsplitc (σ.restrictScalars k) hσK
  rw [Finset.sum_congr rfl hsplit_sum, Finset.sum_add_distrib, h1, h2, add_zero]

end Work.SSGRoute.N2v2
