import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.NK.TameStructureDeep.Core
import Submission.NK.TameStructureDeep.Places
import Submission.NK.TameStructureDeep.Unramified
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open IsDedekindDomain.HeightOneSpectrum

namespace NK.TameStructureDeep

universe u

noncomputable section

/-- **The full residual from the reduced residual**, at a `𝔭`-adic completion with the *canonical*
residue characteristic `p = ringChar (ResidueField (𝒪_κ))`. -/
theorem tameRamificationCore_adicCompletion {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']
    (h : TameRamificationResidual
      (ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)))
      (NK.LocalStructure.residueCard K 𝔭) (𝔭.adicCompletion K) K') :
    TameRamificationCore
      (ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)))
      (NK.LocalStructure.residueCard K 𝔭) (𝔭.adicCompletion K) K' :=
  h.toCore (unramifiedQuotient_adicCompletion 𝔭) (exists_frobenius_adicCompletion 𝔭)

/-- **The full residual from the reduced residual**, for a residue characteristic `p` supplied
with its `CharP` datum (the two are the same datum, by `ringChar.eq`). -/
theorem tameRamificationCore_adicCompletion_of_charP {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K'] {p : ℕ}
    (hchar : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p)
    (h : TameRamificationResidual p (NK.LocalStructure.residueCard K 𝔭)
      (𝔭.adicCompletion K) K') :
    TameRamificationCore p (NK.LocalStructure.residueCard K 𝔭) (𝔭.adicCompletion K) K' := by
  have hp_eq : ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) = p := by
    rw [ringChar.eq_iff]
    exact hchar
  rw [← hp_eq] at h ⊢
  exact tameRamificationCore_adicCompletion 𝔭 h

end

section Boundary

variable {K : Type*} [Field K] [NumberField K]
variable {K' : Type*} [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **The local structure theorem at a place, from the reduced residual.**  The only per-place
hypotheses are the four remaining fields of the reduced residual and the residue-character
detector `NK.LocalTame.Zl2ResidueChar`. -/
theorem localStructureData_of_residual (A : NK.FrobeniusBridge.FinitePlaceOf K K') {p : ℕ}
    (hchar : CharP (IsLocalRing.ResidueField
      ((NK.TameData.primeBelow A).adicCompletionIntegers K)) p)
    (h : TameRamificationResidual p (NK.LocalStructure.residueCard K (NK.TameData.primeBelow A))
      (NK.FrobeniusBridge.localField A) (NK.FrobeniusBridge.localClosure A))
    (hZ : NK.LocalTame.Zl2ResidueChar p (NK.FrobeniusBridge.localField A)
      (NK.FrobeniusBridge.localClosure A)) :
    NK.ResidueFrob.LocalStructureData K K' A :=
  localStructureData_of A hchar
    (tameRamificationCore_adicCompletion_of_charP (NK.TameData.primeBelow A) hchar h) hZ

/-- **The local structure theorem at a place, from the two named classical inputs** of the reduced
residual: the Kummer-theoretic structure of the tame quotient (`TameQuotientKummer`,
NSW (7.5.7) Cor. + (12.1.8)) and the abelianised tame quotient (`TameAbelianisedQuotient`,
Shimizu 2.1), together with the residue-character detector. -/
theorem localStructureData_of_kummer (A : NK.FrobeniusBridge.FinitePlaceOf K K') {p : ℕ}
    (hchar : CharP (IsLocalRing.ResidueField
      ((NK.TameData.primeBelow A).adicCompletionIntegers K)) p)
    (h₁ : TameQuotientKummer p (NK.LocalStructure.residueCard K (NK.TameData.primeBelow A))
      (NK.FrobeniusBridge.localField A) (NK.FrobeniusBridge.localClosure A))
    (h₂ : TameAbelianisedQuotient p (NK.LocalStructure.residueCard K (NK.TameData.primeBelow A))
      (NK.FrobeniusBridge.localField A) (NK.FrobeniusBridge.localClosure A))
    (hZ : NK.LocalTame.Zl2ResidueChar p (NK.FrobeniusBridge.localField A)
      (NK.FrobeniusBridge.localClosure A)) :
    NK.ResidueFrob.LocalStructureData K K' A :=
  localStructureData_of_residual A hchar (TameRamificationResidual.ofKummerAndAbelianised h₁ h₂) hZ

/-- **The local structure theorem at every place, from the two named classical inputs at every
place**, with the canonical residue characteristic `residueCharAt A` and `q = residueCard K 𝔭`. -/
theorem localStructureData_of_kummer_all
    (h₁ : ∀ A : NK.FrobeniusBridge.FinitePlaceOf K K',
      TameQuotientKummer (residueCharAt A)
        (NK.LocalStructure.residueCard K (NK.TameData.primeBelow A))
        (NK.FrobeniusBridge.localField A) (NK.FrobeniusBridge.localClosure A))
    (h₂ : ∀ A : NK.FrobeniusBridge.FinitePlaceOf K K',
      TameAbelianisedQuotient (residueCharAt A)
        (NK.LocalStructure.residueCard K (NK.TameData.primeBelow A))
        (NK.FrobeniusBridge.localField A) (NK.FrobeniusBridge.localClosure A))
    (hZ : ∀ A : NK.FrobeniusBridge.FinitePlaceOf K K',
      NK.LocalTame.Zl2ResidueChar (residueCharAt A)
        (NK.FrobeniusBridge.localField A) (NK.FrobeniusBridge.localClosure A)) :
    ∀ A : NK.FrobeniusBridge.FinitePlaceOf K K', NK.ResidueFrob.LocalStructureData K K' A :=
  fun A => localStructureData_of_kummer A (charP_residueCharAt A) (h₁ A) (h₂ A) (hZ A)

/-- **The local structure theorem at every place, from the reduced residual at every place.** -/
theorem localStructureData_of_residuals
    (h : ∀ A : NK.FrobeniusBridge.FinitePlaceOf K K',
      TameRamificationResidual (residueCharAt A)
        (NK.LocalStructure.residueCard K (NK.TameData.primeBelow A))
        (NK.FrobeniusBridge.localField A) (NK.FrobeniusBridge.localClosure A))
    (hZ : ∀ A : NK.FrobeniusBridge.FinitePlaceOf K K',
      NK.LocalTame.Zl2ResidueChar (residueCharAt A)
        (NK.FrobeniusBridge.localField A) (NK.FrobeniusBridge.localClosure A)) :
    ∀ A : NK.FrobeniusBridge.FinitePlaceOf K K', NK.ResidueFrob.LocalStructureData K K' A :=
  fun A => localStructureData_of_residual A (charP_residueCharAt A) (h A) (hZ A)

end Boundary

end NK.TameStructureDeep
