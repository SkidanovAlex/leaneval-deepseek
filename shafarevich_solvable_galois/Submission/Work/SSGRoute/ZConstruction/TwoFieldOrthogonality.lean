import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ZVocab
import Submission.Work.SSGRoute.ZPlace
import Submission.Work.SSGRoute.ZSolves
import Submission.Work.SSGRoute.ZDataTwo.KummerCocharBase
import Submission.Work.SSGRoute.ZDataTwo.firstElementTotallyPositive
import Submission.Work.SSGRoute.H9.NarrowReadOff
import Submission.Work.SSGRoute.H9.NarrowCorrection
import Submission.Work.SSGRoute.H9.NarrowMu2
import Submission.Work.SSGRoute.H9.NarrowFiniteIndex
import Submission.Work.SSGRoute.step4_y_escape_v2.GesUFacts
import Submission.Work.SSGRoute.GrunwaldEscapeCore.escape_prime_orthogonality
import Submission.Work.SSGRoute.GrunwaldEscapeCore.gesCorrectionFromPrime
import Submission.Work.SSGRoute.ZConstruction.exists_finset_KConj_cover
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `p = 2` realisation with the escape field and the orthogonality field separated

`Work.SSGRoute.ZConstruction.mu2EscapeTwoField` (`ZConstruction/EscapeTwoField.lean`) is the `p = 2`
escape step in the shape the realisation needs: the orthogonality field `Λ` (the small field, at
which the correction blocks over `S₀ ∖ S` are split) and the escape field `Λ ⊔ L₂` (the big field,
in which the escape prime is split) are separated, and the orthogonality of the class of the first
element is an explicit hypothesis.

This file packages that hypothesis as the `Prop` `Work.SSGRoute.ZConstruction.TwoFieldOrthogonality`
(verbatim the *conclusion* of the two-field narrow orthogonality, with all its arguments as binders,
so that `Work.SSGRoute.NoKimag.OrthHsplitTwoNarrow` instantiates it directly) and proves the
realisation of Schmidt--Wingberg §4 at `p = 2`:

  `∃ yt, IsYRealisation 2 K (Λ ⊔ L₂) S S₀ (fun _ => ν) yt`

with `hKimag` nowhere: clause (6) comes from the total positivity of the escape element (the
involutions clause of `mu2EscapeTwoField`, hence of `H9.correctionFromPrime_narrow`), and the only
extra hypothesis on the datum is `hνinf : ∀ c ∈ K.fixingSubgroup, c² = 1 → ν c = 0` -- the node's
`hyinf` transported to `ν = ρ ∘ y`.  This is exactly the statement consumed by
`Work.SSGRoute.ZConstruction.auxRealisationGate_of_realisationTwo`, hence by
`Work.SSGRoute.shafarevich_z_construction_of_realisationGate`. -/

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute
open scoped Pointwise

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  [IsAlgClosed Ω]

/-! ## The orthogonality hypothesis, in the form in which the two-field narrow orthogonality
delivers it -/

/-- **The two-field narrow orthogonality of the `p = 2` escape, as a gate.**

This is the conclusion of `Work.SSGRoute.NoKimag.OrthHsplitTwoNarrow` (the two-field, narrow,
`hKimag`-free orthogonality) with all of its hypotheses as binders, so that the theorem instantiates
this `Prop` verbatim: `L₁ = Λ` is the orthogonality field, `L₂` the second field, and `N'` (called
`N` here) the copy over `↥K` of `Λ ⊔ L₂`. -/
def TwoFieldOrthogonality (K Λ L₂ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] [FiniteDimensional k L₂] [IsGalois k L₂]
    (hKΛ : K ≤ Λ) (hKL₂ : K ≤ L₂)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (hζK' : IsPrimitiveRoot (⟨ζ, hζK⟩ : ↥K) 2) : Prop :=
  ∀ (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, Work.SSGRoute.gesKConj K A B → A = B)
    (hTcov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (B.valuation (2 : Ω) < 1 ∨
        (∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ Λ.fixingSubgroup) ∨
        (∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ L₂.fixingSubgroup)) →
      ∃ A ∈ T, Work.SSGRoute.gesKConj K A B)
    (g : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hg : ∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, g (x * y) = g x + g y)
    (hgc : SSGRoute.IsLocConstOn K.fixingSubgroup g)
    (hgram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → g σ = 0)
    (hginf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → g c = 0)
    (h : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hh : ∀ A ∈ T, ∀ x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      ∀ y ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A (x * y) = h A x + h A y)
    (hhc : ∀ A ∈ T, ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      ∀ x ∈ U, x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup → h A x = 0)
    (horth₁ : ∀ A ∈ T,
      (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A σ = 0) ∨
      (∀ χ : (Ω ≃ₐ[k] Ω) → ZMod 2,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
        (∀ σ ∈ Λ.fixingSubgroup, χ σ = 0) →
        ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, χ σ = 0) ∨
      ((∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → h A σ = 0) ∧
        ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod 2,
          (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
          (∀ σ ∈ Λ.fixingSubgroup, χ σ = 0) →
          ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → χ σ = 0))
    (horth₂ : ∀ A ∈ T,
      (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, g σ + h A σ = 0) ∨
      (∀ χ : (Ω ≃ₐ[k] Ω) → ZMod 2,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
        (∀ σ ∈ L₂.fixingSubgroup, χ σ = 0) →
        ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, χ σ = 0) ∨
      ((∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → g σ + h A σ = 0) ∧
        ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod 2,
          (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
          (∀ σ ∈ L₂.fixingSubgroup, χ σ = 0) →
          ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → χ σ = 0))
    (hsplit : ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod 2,
      (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
      (∀ σ ∈ (Λ ⊔ L₂ : IntermediateField k Ω).fixingSubgroup, χ σ = 0) →
      ∃ χ₁ χ₂ : (Ω ≃ₐ[k] Ω) → ZMod 2,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ₁ (x * y) = χ₁ x + χ₁ y) ∧
        (∀ σ ∈ Λ.fixingSubgroup, χ₁ σ = 0) ∧
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ₂ (x * y) = χ₂ x + χ₂ y) ∧
        (∀ σ ∈ L₂.fixingSubgroup, χ₂ σ = 0) ∧
        ∀ σ ∈ K.fixingSubgroup, χ σ = χ₁ σ + χ₂ σ)
    (T' : Finset (NK.Chebotarev.PrimeIdeal ↥K))
    (hTbelow : ∀ A ∈ T, ∃ 𝔭 ∈ T', A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (hT'above : ∀ 𝔭 ∈ T', ∃ A ∈ T, A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (M : IntermediateField ↥K Ω) [FiniteDimensional ↥K M] [IsGalois ↥K M] [NumberField ↥M]
    (hMnorm : NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥M =
      Work.SSGRoute.H9.narrowGesU ↥K 2 T' ⊔
        Work.SSGRoute.EscapeCoreLib.pPowSubgroup 2 (NK.GlobalCFT.IdeleClassGroup ↥K))
    (N : IntermediateField ↥K Ω) [FiniteDimensional ↥K N] [IsGalois ↥K N] [NumberField ↥N]
    (hN : (N : Set Ω) = ((Λ ⊔ L₂ : IntermediateField k Ω) : Set Ω))
    (a : (↥K)ˣ)
    (ha : ∀ A ∈ T, ∀ σ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
      g (σ : Ω ≃ₐ[k] Ω) + h A (σ : Ω ≃ₐ[k] Ω) =
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ⟨ζ, hζK⟩) hζK' a
          (Work.SSGRoute.gesLocalToGalK K σ))
    (hapos : ∀ (c : Ω ≃ₐ[k] Ω) (hc : c ∈ K.fixingSubgroup), c ^ 2 = 1 →
      Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ⟨ζ, hζK⟩) hζK' a
        (Work.SSGRoute.gesGalKOfFixing K c hc) = 0),
    NK.GlobalCFT.IdeleClassGroup.mk ↥K (NK.NUV2.RouteB.RayModulus.fracIdele
        (Work.SSGRoute.tFreePart (K := ↥K) T' a)) ∈
      NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥M ⊔
        NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥N

end Work.SSGRoute.ZConstruction
