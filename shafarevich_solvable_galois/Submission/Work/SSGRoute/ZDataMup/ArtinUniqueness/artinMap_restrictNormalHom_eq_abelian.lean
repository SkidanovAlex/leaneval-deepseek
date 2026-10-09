import Mathlib
import Submission.Work.SSGRoute.ZDataMup.ArtinUniqueness.artinMap_restrictNormalHom_eq
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.surjective_of_frobAtPrime_unramified
import Submission.NK.Chebotarev.ExistsUniqueIsFrobAtPrime
import Submission.NK.Chebotarev.IsFrobAtRestrictNormalHom
import Submission.NK.NUV2.ARL.isOpenNorm
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Level compatibility of the abelian idèlic Artin map

This is the abelian case of `Work.SSGRoute.ZDataMup.ArtinUniqueness.artinMap_restrictNormalHom_eq`:
`M/K` is assumed **abelian** (commutative Galois group) rather than cyclic, and the intermediate
field `↥L ⊆ M` is a finite Galois subextension.  The conclusion is the functoriality of the Artin
map: the restriction of the Artin map of `M/K` along `Gal(M/K) → Gal(↥L/K)` is the Artin map of
`↥L/K`.

This is the "wiring" step needed by the gate `Work.SSGRoute.ZConstruction.auxPairingGate_odd`: the
Kummer levels `K((α x)^{1/p}) · K((β y)^{1/p})` occurring in its pairing construction are
composita of *two* cyclic degree-`p` extensions, hence abelian but **not cyclic**, so the cyclic
lemma does not apply to them.

The proof is the proof of the cyclic case verbatim; the only change is that the cyclicity
hypothesis is replaced by the commutativity hypothesis `hcommM` (so `comm_of_isCyclic` is dropped,
and `hcommL` --- commutativity of the quotient `Gal(↥L/K)` --- is derived from `hcommM` as before).
-/

open scoped NumberField
open NumberField IsDedekindDomain

namespace Work.SSGRoute.ZDataMup.ArtinUniqueness

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- **Level compatibility of the abelian idèlic Artin map.**

If `M/K` is a finite abelian extension of number fields, `↥L ⊆ M` an intermediate finite Galois
subextension, `Φ` the Artin map of `M/K` and `Ψ` that of `↥L/K`, both with kernel
`N 𝕀 ⊔ Kˣ` and Frobenius normalised at every unramified prime, then
`(restrictNormalHom) ∘ Φ = Ψ`. -/
theorem artinMap_restrictNormalHom_eq_abelian {K M : Type} [Field K] [NumberField K] [Field M]
    [NumberField M] [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
    (hcommM : ∀ a b : M ≃ₐ[K] M, a * b = b * a)
    (L : IntermediateField K M) [FiniteDimensional K L] [IsGalois K L]
    (Φ : NK.GlobalCFT.Idele K →* (M ≃ₐ[K] M))
    (hΦker : Φ.ker = NK.GlobalCFT.Idele.normImage K M ⊔ NK.GlobalCFT.Idele.principalSubgroup K)
    (hΦfrob : ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      NK.HeckeL.IsUnramifiedIn (K := K) (L := M) Q →
      Φ (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := M) Q)
    (Ψ : NK.GlobalCFT.Idele K →* (↥L ≃ₐ[K] ↥L))
    (hΨker : Ψ.ker = NK.GlobalCFT.Idele.normImage K ↥L ⊔ NK.GlobalCFT.Idele.principalSubgroup K)
    (hΨfrob : ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      NK.HeckeL.IsUnramifiedIn (K := K) (L := ↥L) Q →
      Ψ (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := ↥L) Q) :
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) ↥L).comp Φ = Ψ := by
  classical
  -- `↥L` is a number field.
  haveI hNF_L : NumberField ↥L :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField L
  -- Galois groups of the intermediate fields are commutative (quotients of `Gal(M/K)`).
  have hsurjρ : Function.Surjective (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) ↥L) :=
    AlgEquiv.restrictNormalHom_surjective (F := K) (E := M) (K₁ := ↥L)
  have hcommL : ∀ a b : (↥L ≃ₐ[K] ↥L), a * b = b * a := by
    intro a b
    obtain ⟨a', rfl⟩ := hsurjρ a
    obtain ⟨b', rfl⟩ := hsurjρ b
    rw [← map_mul, ← map_mul, hcommM a' b']
  -- Both `Φ` and `Ψ` are surjective (their ranges contain all Frobenius elements).
  have hsurjΦ : Function.Surjective Φ :=
    ArtinReciprocity.surjective_of_frobAtPrime_unramified hcommM Φ hΦfrob
  have hsurjΨ : Function.Surjective Ψ :=
    ArtinReciprocity.surjective_of_frobAtPrime_unramified hcommL Ψ hΨfrob
  -- `Φ.ker ≤ Ψ.ker`: the norms from `M` are norms from `↥L` (norm transitivity).
  have hle : Φ.ker ≤ Ψ.ker := by
    rw [hΦker, hΨker]
    refine sup_le ?_ le_sup_right
    exact le_trans
      (NK.NUV2.ARL.normImage_le_of_tower (K := K) (L := ↥L) (M := M)) le_sup_left
  -- The map induced by `Ψ` on the quotient `𝕀 K ⧸ Φ.ker ≅ Gal(M/K)`.
  let eΦ : (NK.GlobalCFT.Idele K ⧸ Φ.ker) ≃* (M ≃ₐ[K] M) :=
    QuotientGroup.quotientKerEquivOfSurjective Φ hsurjΦ
  let LΨ : (NK.GlobalCFT.Idele K ⧸ Φ.ker) →* (↥L ≃ₐ[K] ↥L) :=
    QuotientGroup.lift Φ.ker Ψ hle
  let χ : (M ≃ₐ[K] M) →* (↥L ≃ₐ[K] ↥L) := LΨ.comp eΦ.symm.toMonoidHom
  have hχ : ∀ x : NK.GlobalCFT.Idele K, χ (Φ x) = Ψ x := by
    intro x
    have h1 : eΦ (QuotientGroup.mk' Φ.ker x) = Φ x := rfl
    have h2 : LΨ (QuotientGroup.mk' Φ.ker x) = Ψ x := QuotientGroup.lift_mk' _ _ x
    calc χ (Φ x) = LΨ (eΦ.symm (Φ x)) := rfl
      _ = LΨ (eΦ.symm (eΦ (QuotientGroup.mk' Φ.ker x))) := by rw [h1]
      _ = LΨ (QuotientGroup.mk' Φ.ker x) := by rw [MulEquiv.symm_apply_apply]
      _ = Ψ x := h2
  -- `χ` and the restriction map agree on the Frobenius elements outside a finite set (Čebotarev).
  have hχρ : χ = AlgEquiv.restrictNormalHom (F := K) (K₁ := M) ↥L := by
    let T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :=
      NK.CFTLib.ExistsCongruence.ramPrimes (K := K) (L := M)
    have hunrT : ∀ 𝔭, 𝔭 ∉ T → NK.HeckeL.IsUnramifiedIn (K := K) (L := M) 𝔭 :=
      fun 𝔭 h𝔭 𝔮 h𝔮 =>
        NK.CFTLib.ExistsCongruence.ramificationIdx_eq_one_of_notMem_ramPrimes (K := K) (L := M)
          h𝔭 h𝔮
    have hgen := NK.CFTLib.Arl.closure_isFrobAtPrime_of_notMem_eq_top (K := K) (L := M) T
    have heqon : Set.EqOn (⇑χ)
        (⇑(AlgEquiv.restrictNormalHom (F := K) (K₁ := M) ↥L))
        {σ : (M ≃ₐ[K] M) |
          ∃ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
            𝔭 ∉ T ∧ NK.Chebotarev.IsFrobAtPrime (K := K) (L := M) 𝔭 σ} := by
      rintro σ ⟨𝔭, h𝔭T, hσ⟩
      have hunrM : NK.HeckeL.IsUnramifiedIn (K := K) (L := M) 𝔭 := hunrT 𝔭 h𝔭T
      have hunrL : NK.HeckeL.IsUnramifiedIn (K := K) (L := ↥L) 𝔭 :=
        isUnramifiedIn_intermediateField L 𝔭 hunrM
      have hσ' : NK.Chebotarev.frobAtPrime (K := K) (L := M) 𝔭 = σ :=
        (NK.Chebotarev.isFrobAtPrime_iff_frobAtPrime_eq hcommM 𝔭 hunrM σ).mp hσ
      rw [← hσ']
      have e1 : χ (NK.Chebotarev.frobAtPrime (K := K) (L := M) 𝔭)
          = Ψ (NK.HeckeL.ideleOfPrime K 𝔭) := by
        rw [← hΦfrob 𝔭 hunrM]
        exact hχ (NK.HeckeL.ideleOfPrime K 𝔭)
      have e2 : Ψ (NK.HeckeL.ideleOfPrime K 𝔭)
          = NK.Chebotarev.frobAtPrime (K := K) (L := ↥L) 𝔭 := hΨfrob 𝔭 hunrL
      have e3 : AlgEquiv.restrictNormalHom (F := K) (K₁ := M) ↥L
            (NK.Chebotarev.frobAtPrime (K := K) (L := M) 𝔭)
          = NK.Chebotarev.frobAtPrime (K := K) (L := ↥L) 𝔭 :=
        restrictNormalHom_frobAtPrime_of_intermediateField L hcommM hcommL 𝔭 hunrM
      rw [e1, e2, e3]
    have hEq := MonoidHom.eqOn_closure (f := χ)
      (g := AlgEquiv.restrictNormalHom (F := K) (K₁ := M) ↥L) heqon
    refine MonoidHom.ext fun σ => ?_
    exact hEq (by rw [hgen]; exact Subgroup.mem_top σ)
  -- Conclusion: `(ρ ∘ Φ) x = χ (Φ x) = Ψ x`.
  refine MonoidHom.ext fun x => ?_
  have h := hχ x
  rw [hχρ] at h
  simpa using h

end Work.SSGRoute.ZDataMup.ArtinUniqueness
