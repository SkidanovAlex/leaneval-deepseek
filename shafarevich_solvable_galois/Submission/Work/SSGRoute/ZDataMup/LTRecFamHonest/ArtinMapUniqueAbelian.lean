import Mathlib
import Submission.Work.SSGRoute.ZDataMup.NKArtinUmbrella
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.surjective_of_frobAtPrime_unramified
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Uniqueness of the abelian idèlic Artin map

`Work.SSGRoute.ZDataMup.ArtinUniqueness.artinMap_unique` proves that two idèlic Artin maps
`𝕀_K →* Gal(L/K)` with the same kernel `N_{L/K} 𝕀_L ⊔ K^×` and the same Frobenius normalisation
agree, for `L/K` **cyclic**.  The proof uses cyclicity in a single place (`comm_of_isCyclic`); this
file records the **abelian** version, which is what the `LTRecFamHonest` lane consumes (its levels
are composita of two Kummer levels, hence abelian but not cyclic).

The file is a verbatim copy of the cyclic proof with `comm_of_isCyclic` replaced by the `hcomm`
hypothesis; `Work.SSGRoute.ZDataMup.ArtinReciprocity.surjective_of_frobAtPrime_unramified` already
takes `hcomm` explicitly.
-/

namespace Work.SSGRoute.ZDataMup.LTRecFamHonest

open scoped NumberField
open NumberField IsDedekindDomain

/-- **Uniqueness of the abelian idèlic Artin map.**  Two monoid homomorphisms
`Φ Ψ : 𝕀_K →* Gal(L/K)` with kernel exactly `N_{L/K} 𝕀_L ⊔ K^×` and sending the idèle
`ideleOfPrime K Q` of every unramified prime `Q` to the Frobenius element `frobAtPrime Q` agree. -/
theorem artinMap_unique_abelian {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : (L ≃ₐ[K] L), a * b = b * a)
    (Φ Ψ : NK.GlobalCFT.Idele K →* (L ≃ₐ[K] L))
    (hΦker : Φ.ker = NK.GlobalCFT.Idele.normImage K L ⊔
      NK.GlobalCFT.Idele.principalSubgroup K)
    (hΨker : Ψ.ker = NK.GlobalCFT.Idele.normImage K L ⊔
      NK.GlobalCFT.Idele.principalSubgroup K)
    (hΦfrob : ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q →
      Φ (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q)
    (hΨfrob : ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q →
      Ψ (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) :
    Φ = Ψ := by
  classical
  -- ## `Φ` and `Ψ` are surjective
  have hsurjΦ : Function.Surjective Φ :=
    Work.SSGRoute.ZDataMup.ArtinReciprocity.surjective_of_frobAtPrime_unramified hcomm Φ hΦfrob
  have hsurjΨ : Function.Surjective Ψ :=
    Work.SSGRoute.ZDataMup.ArtinReciprocity.surjective_of_frobAtPrime_unramified hcomm Ψ hΨfrob
  -- ## The endomorphism of `Gal(L/K)` relating `Ψ` to `Φ`
  let Q := NK.GlobalCFT.Idele K ⧸ Φ.ker
  let eΦ : Q ≃* (L ≃ₐ[K] L) := QuotientGroup.quotientKerEquivOfSurjective Φ hsurjΦ
  let LΨ : Q →* (L ≃ₐ[K] L) := QuotientGroup.lift Φ.ker Ψ (by rw [hΨker, hΦker])
  let α : (L ≃ₐ[K] L) →* (L ≃ₐ[K] L) := LΨ.comp eΦ.symm.toMonoidHom
  have hα : ∀ x : NK.GlobalCFT.Idele K, α (Φ x) = Ψ x := by
    intro x
    have h1 : eΦ (QuotientGroup.mk' Φ.ker x) = Φ x := rfl
    have h2 : LΨ (QuotientGroup.mk' Φ.ker x) = Ψ x := QuotientGroup.lift_mk' _ _ x
    calc α (Φ x) = LΨ (eΦ.symm (Φ x)) := rfl
      _ = LΨ (eΦ.symm (eΦ (QuotientGroup.mk' Φ.ker x))) := by rw [h1]
      _ = LΨ (QuotientGroup.mk' Φ.ker x) := by rw [MulEquiv.symm_apply_apply]
      _ = Ψ x := h2
  -- ## `α` fixes every Frobenius element at a prime outside the finite set of ramified primes
  let T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :=
    NK.CFTLib.ExistsCongruence.ramPrimes (K := K) (L := L)
  have hunr : ∀ 𝔭, 𝔭 ∉ T → NK.HeckeL.IsUnramifiedIn (K := K) (L := L) 𝔭 :=
    fun 𝔭 h𝔭 𝔮 h𝔮 =>
      NK.CFTLib.ExistsCongruence.ramificationIdx_eq_one_of_notMem_ramPrimes (K := K) (L := L)
        h𝔭 h𝔮
  have hαfix : ∀ 𝔭, 𝔭 ∉ T → α (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭)
      = NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭 := by
    intro 𝔭 h𝔭
    calc α (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭)
        = α (Φ (NK.HeckeL.ideleOfPrime K 𝔭)) := by rw [hΦfrob 𝔭 (hunr 𝔭 h𝔭)]
      _ = Ψ (NK.HeckeL.ideleOfPrime K 𝔭) := hα _
      _ = NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭 := hΨfrob 𝔭 (hunr 𝔭 h𝔭)
  -- ## An endomorphism of `Gal(L/K)` fixing a generating set is the identity
  have hαid : α = MonoidHom.id (L ≃ₐ[K] L) := by
    have hgen : Subgroup.closure {σ : (L ≃ₐ[K] L) |
        ∃ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
          𝔭 ∉ T ∧ NK.Chebotarev.IsFrobAtPrime (K := K) (L := L) 𝔭 σ} = ⊤ :=
      NK.CFTLib.Arl.closure_isFrobAtPrime_of_notMem_eq_top (K := K) (L := L) T
    have heqon : Set.EqOn (⇑α) (⇑(MonoidHom.id (L ≃ₐ[K] L))) {σ : (L ≃ₐ[K] L) |
        ∃ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
          𝔭 ∉ T ∧ NK.Chebotarev.IsFrobAtPrime (K := K) (L := L) 𝔭 σ} := by
      rintro σ ⟨𝔭, h𝔭, hσ⟩
      have hσ' : NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭 = σ :=
        (NK.Chebotarev.isFrobAtPrime_iff_frobAtPrime_eq hcomm 𝔭 (hunr 𝔭 h𝔭) σ).mp hσ
      rw [← hσ']
      exact hαfix 𝔭 h𝔭
    have hEq := MonoidHom.eqOn_closure (f := α) (g := MonoidHom.id (L ≃ₐ[K] L))
      (s := {σ : (L ≃ₐ[K] L) |
        ∃ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
          𝔭 ∉ T ∧ NK.Chebotarev.IsFrobAtPrime (K := K) (L := L) 𝔭 σ}) heqon
    refine MonoidHom.ext fun σ => ?_
    exact hEq (by rw [hgen]; exact Subgroup.mem_top σ)
  -- ## Conclusion
  refine MonoidHom.ext fun x => ?_
  have h := hα x
  rw [hαid] at h
  simpa using h

end Work.SSGRoute.ZDataMup.LTRecFamHonest
