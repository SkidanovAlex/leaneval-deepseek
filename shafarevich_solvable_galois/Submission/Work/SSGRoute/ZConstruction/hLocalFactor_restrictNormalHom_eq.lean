import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.Work.SSGRoute.ZConstruction.restrictMol_frobAtPrime
import Submission.Work.SSGRoute.ZDataMup.LTRecFamHonest.LocalFactor
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZConstruction

open Work.SSGRoute.ZDataMup.LTRecFamHonest

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

theorem hLocalFactor_restrictNormalHom_eq (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω] (A : ValuationSubring Ω) (hA : _root_.SSGRoute.IsFinPlace k A)
    (L M : IntermediateField ↥K Ω) [FiniteDimensional ↥K L] [IsGalois ↥K L]
    [FiniteDimensional ↥K M] [IsGalois ↥K M] (hLM : L ≤ M)
    (hcommM : ∀ a b : ↥M ≃ₐ[↥K] ↥M, a * b = b * a)
    (Φ : NK.GlobalCFT.Idele ↥K →* (↥M ≃ₐ[↥K] ↥M))
    (hΦker : Φ.ker = NK.GlobalCFT.Idele.normImage ↥K ↥M ⊔
      NK.GlobalCFT.Idele.principalSubgroup ↥K)
    (hΦfrob : ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥M) Q →
      Φ (NK.HeckeL.ideleOfPrime ↥K Q) = NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥M) Q)
    (Ψ : NK.GlobalCFT.Idele ↥K →* (↥L ≃ₐ[↥K] ↥L))
    (hΨker : Ψ.ker = NK.GlobalCFT.Idele.normImage ↥K ↥L ⊔
      NK.GlobalCFT.Idele.principalSubgroup ↥K)
    (hΨfrob : ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥L) Q →
      Ψ (NK.HeckeL.ideleOfPrime ↥K Q) = NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥L) Q)
    (ν : (↥K)ˣ) (x : ↥L) :
    ((Work.SSGRoute.ZDataMup.LTRecFamHonest.hLocalFactor (K := K) A hA M Φ ν)
        ⟨(x : Ω), hLM x.2⟩ : Ω) =
      ((Work.SSGRoute.ZDataMup.LTRecFamHonest.hLocalFactor (K := K) A hA L Ψ ν) x : Ω) := by
  classical
  -- ## Number-field and normal-field structures on the levels
  haveI hNumL : NumberField ↥L :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := ↥K) (K' := Ω) L
  haveI hNumM : NumberField ↥M :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := ↥K) (K' := Ω) M
  haveI hNΩ : Normal ↥K Ω := inferInstance
  haveI hNL : Normal ↥K ↥L := IsGalois.to_normal
  haveI hNM : Normal ↥K ↥M := IsGalois.to_normal
  -- ## The idèle at which both local factors are evaluated
  set z : NK.GlobalCFT.Idele ↥K :=
    NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite (hPrimeBelow (K := K) (A := A) hA))
      (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
        (NK.GlobalCFT.Place.ofFinite (hPrimeBelow (K := K) (A := A) hA)) ν) with hz
  have hLMF : Work.SSGRoute.ZDataMup.LTRecFamHonest.hLocalFactor (K := K) A hA M Φ ν =
      Φ z := rfl
  have hLLF : Work.SSGRoute.ZDataMup.LTRecFamHonest.hLocalFactor (K := K) A hA L Ψ ν =
      Ψ z := rfl
  -- ## The norm groups are nested
  have hNorm : NK.GlobalCFT.Idele.normImage ↥K ↥M ≤ NK.GlobalCFT.Idele.normImage ↥K ↥L := by
    letI : Algebra ↥L ↥M := (Subsemiring.inclusion hLM).toAlgebra
    haveI : IsScalarTower ↥K ↥L ↥M := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : FiniteDimensional ↥L ↥M := Module.Finite.right ↥K ↥L ↥M
    exact NK.NUV2.ARL.normImage_le_of_tower (K := ↥K) (L := ↥L) (M := ↥M)
  have hle : Φ.ker ≤ Ψ.ker := by
    rw [hΦker, hΨker]
    exact sup_le (le_trans hNorm le_sup_left) le_sup_right
  -- ## The map induced by `Ψ` on `Gal(M/↥K)`
  have hsurjΦ : Function.Surjective Φ :=
    Work.SSGRoute.ZDataMup.ArtinReciprocity.surjective_of_frobAtPrime_unramified hcommM Φ hΦfrob
  let eΦ : (NK.GlobalCFT.Idele ↥K ⧸ Φ.ker) ≃* (↥M ≃ₐ[↥K] ↥M) :=
    QuotientGroup.quotientKerEquivOfSurjective Φ hsurjΦ
  let Ψbar : (NK.GlobalCFT.Idele ↥K ⧸ Φ.ker) →* (↥L ≃ₐ[↥K] ↥L) :=
    QuotientGroup.lift Φ.ker Ψ hle
  let χ : (↥M ≃ₐ[↥K] ↥M) →* (↥L ≃ₐ[↥K] ↥L) := Ψbar.comp eΦ.symm.toMonoidHom
  have hχ : ∀ y : NK.GlobalCFT.Idele ↥K, χ (Φ y) = Ψ y := by
    intro y
    have h1 : eΦ (QuotientGroup.mk' Φ.ker y) = Φ y := rfl
    have h2 : Ψbar (QuotientGroup.mk' Φ.ker y) = Ψ y := QuotientGroup.lift_mk' _ _ y
    calc χ (Φ y) = Ψbar (eΦ.symm (Φ y)) := rfl
      _ = Ψbar (eΦ.symm (eΦ (QuotientGroup.mk' Φ.ker y))) := by rw [h1]
      _ = Ψbar (QuotientGroup.mk' Φ.ker y) := by rw [MulEquiv.symm_apply_apply]
      _ = Ψ y := h2
  -- ## Chebotarev: `χ` agrees with the restriction along `↥L ⊆ ↥M`
  have hχρ : χ = restrictMol L M hLM := by
    let T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K)) :=
      NK.CFTLib.ExistsCongruence.ramPrimes (K := ↥K) (L := ↥M) ∪
        NK.CFTLib.ExistsCongruence.ramPrimes (K := ↥K) (L := ↥L)
    have hunrM : ∀ 𝔭, 𝔭 ∉ T → NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥M) 𝔭 := by
      intro 𝔭 h𝔭
      have h1 : 𝔭 ∉ NK.CFTLib.ExistsCongruence.ramPrimes (K := ↥K) (L := ↥M) := fun h =>
        h𝔭 (Finset.mem_union.mpr (Or.inl h))
      exact fun 𝔮 h𝔮 =>
        NK.CFTLib.ExistsCongruence.ramificationIdx_eq_one_of_notMem_ramPrimes
          (K := ↥K) (L := ↥M) h1 h𝔮
    have hunrL : ∀ 𝔭, 𝔭 ∉ T → NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥L) 𝔭 := by
      intro 𝔭 h𝔭
      have h1 : 𝔭 ∉ NK.CFTLib.ExistsCongruence.ramPrimes (K := ↥K) (L := ↥L) := fun h =>
        h𝔭 (Finset.mem_union.mpr (Or.inr h))
      exact fun 𝔮 h𝔮 =>
        NK.CFTLib.ExistsCongruence.ramificationIdx_eq_one_of_notMem_ramPrimes
          (K := ↥K) (L := ↥L) h1 h𝔮
    have hgen : Subgroup.closure {σ : ↥M ≃ₐ[↥K] ↥M |
        ∃ 𝔭, 𝔭 ∉ T ∧ NK.Chebotarev.IsFrobAtPrime (K := ↥K) (L := ↥M) 𝔭 σ} = ⊤ :=
      NK.CFTLib.Arl.closure_isFrobAtPrime_of_notMem_eq_top (K := ↥K) (L := ↥M) T
    have heqon : Set.EqOn (⇑χ) (⇑(restrictMol L M hLM)) {σ : ↥M ≃ₐ[↥K] ↥M |
        ∃ 𝔭, 𝔭 ∉ T ∧ NK.Chebotarev.IsFrobAtPrime (K := ↥K) (L := ↥M) 𝔭 σ} := by
      rintro σ ⟨𝔭, h𝔭T, hσ⟩
      have hM : NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥M) 𝔭 := hunrM 𝔭 h𝔭T
      have hL : NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥L) 𝔭 := hunrL 𝔭 h𝔭T
      have hσ' : NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥M) 𝔭 = σ :=
        (NK.Chebotarev.isFrobAtPrime_iff_frobAtPrime_eq hcommM 𝔭 hM σ).mp hσ
      rw [← hσ']
      calc χ (NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥M) 𝔭)
          = χ (Φ (NK.HeckeL.ideleOfPrime ↥K 𝔭)) := by rw [hΦfrob 𝔭 hM]
        _ = Ψ (NK.HeckeL.ideleOfPrime ↥K 𝔭) := hχ _
        _ = NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥L) 𝔭 := hΨfrob 𝔭 hL
        _ = restrictMol L M hLM (NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥M) 𝔭) :=
            (restrictMol_frobAtPrime (K := ↥K) (Ω := Ω) (L := L) (M := M) hLM hcommM 𝔭 hM).symm
    refine MonoidHom.ext fun σ => ?_
    have h := MonoidHom.eqOn_closure (f := χ) (g := restrictMol L M hLM) heqon
    exact h (by rw [hgen]; exact Subgroup.mem_top σ)
  -- ## Conclusion
  have hcomp : ∀ y : NK.GlobalCFT.Idele ↥K, restrictMol L M hLM (Φ y) = Ψ y := by
    intro y
    rw [← hχρ]
    exact hχ y
  rw [hLMF, hLLF]
  rw [← restrictMol_apply (K := ↥K) (L := L) (M := M) hLM (Φ z) x]
  rw [hcomp z]

end Work.SSGRoute.ZConstruction
