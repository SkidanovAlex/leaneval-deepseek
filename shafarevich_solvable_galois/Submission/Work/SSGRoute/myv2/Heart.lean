import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.myv2.HeartMain
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The heart of the `N2` repair, with `hsplit`

Two equivalent formulations of the orthogonality of the escape-form Grünwald theorem, repaired by
the `hsplit` hypothesis (the `N2` fix, `ssg8/n2_0001/VERDICT.md`):

* `alpha_fixes_inf_ssg8_hsplit` — the field form: the Artin symbol `α = art(𝔡)` of the `T'`-free
  part of the divisor of the Grünwald element `a` fixes `M ⊓ (L₁ ⊔ L₂)` pointwise;
* `orthogonality_v2_hsplit` — the class-group form: `[𝔡] ∈ U' · N_{N/↥K}C_N`.
-/

open scoped Pointwise
open NumberField IsDedekindDomain
open NK.GlobalCFT

namespace Work.SSGRoute.N2v2

open _root_.SSGRoute
open Work.SSGRoute.SSG8Escape

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open Work.SSGRoute in
/-- **The orthogonality (field form) with `hsplit`.** -/
theorem alpha_fixes_inf_ssg8_hsplit (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (hKimag : p = 2 → ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → c = 1)
    (L₁ L₂ : IntermediateField k Ω) [FiniteDimensional k L₁] [IsGalois k L₁]
    [FiniteDimensional k L₂] [IsGalois k L₂] (hKL₁ : K ≤ L₁) (hKL₂ : K ≤ L₂)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (T' : Finset (NK.Chebotarev.PrimeIdeal ↥K))
    (hTbelow : ∀ A ∈ T, ∃ 𝔭 ∈ T', A.comap (algebraMap ↥K Ω) =
      HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (hT'above : ∀ 𝔭 ∈ T', ∃ A ∈ T, A.comap (algebraMap ↥K Ω) =
      HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
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
        ∀ σ ∈ K.fixingSubgroup, χ σ = χ₁ σ + χ₂ σ)
    (a : (↥K)ˣ)
    (ha : ∀ A ∈ T, ∀ σ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
      g (σ : Ω ≃ₐ[k] Ω) + h A (σ : Ω ≃ₐ[k] Ω) =
        kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ a
          (Work.SSGRoute.gesLocalToGalK K σ))
    (M : IntermediateField ↥K Ω) [FiniteDimensional ↥K M] [IsGalois ↥K M] [NumberField ↥M]
    [IsMulCommutative (↥M ≃ₐ[↥K] ↥M)]
    (hM : Idele.normClassSubgroup ↥K ↥M = gesUPow ↥K p T')
    (art : Idele ↥K →* (↥M ≃ₐ[↥K] ↥M))
    (hker : art.ker = Idele.normImage ↥K ↥M ⊔ Idele.principalSubgroup ↥K)
    (hfrob : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥K,
      NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥M) 𝔮 →
      art (NK.HeckeL.ideleOfPrime ↥K 𝔮) = NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥M) 𝔮)
    (α : ↥M ≃ₐ[↥K] ↥M)
    (hα : art (NK.NUV2.RouteB.RayModulus.fracIdele (tFreePart (K := ↥K) T' a)) = α) :
    ∀ x : ↥M, ((x : Ω) ∈ (L₁ ⊔ L₂)) → α x = x  := alpha_fixes_inf_hsplit_main p k Ω K ζ hζ hKimag L₁ L₂ hKL₁ hKL₂ T hTfin T' hTbelow hT'above
    hTdisj hTcov g hg hgc hgram h hh hhc horth₁ horth₂ hsplit a ha M hM art hker hfrob α hα

end Work.SSGRoute.N2v2
