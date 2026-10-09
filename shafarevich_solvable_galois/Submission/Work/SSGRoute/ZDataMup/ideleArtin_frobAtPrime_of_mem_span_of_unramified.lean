import Mathlib
import Submission.Work.SSGRoute.ZDataMup.NKArtinUmbrella
import Submission.Work.SSGRoute.ZDataMup.ideleArtin_independent_of_congruence_data
import Submission.Work.SSGRoute.ZDataMup.ideleArtin_restrictNormalHom
import Submission.NK.NUV2.ARL.abelianWeakToStrong
import Submission.NK.CFTLib.ArtinReciprocityIdeal.iInf_subgroup_isCyclic_quotient
import Submission.NK.Chebotarev.ExistsUniqueIsFrobAtPrime
import Submission.Work.SSGRoute.ZDataMup.localGlobalArtinMap_kills_principal_cyclic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.ZDataMup

open NK.GlobalCFT

/-- `ramificationIdxIn = 1` is the same condition as `NK.HeckeL.IsUnramifiedIn`. -/
lemma isUnramifiedIn_of_ramificationIdxIn_eq_one_zdataMup
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (h : Ideal.ramificationIdxIn p.asIdeal (NumberField.RingOfIntegers L) = 1) :
    NK.HeckeL.IsUnramifiedIn (K := K) (L := L) p := by
  letI hMSA : MulSemiringAction (Gal(L/K)) (NumberField.RingOfIntegers L) :=
    IsIntegralClosure.MulSemiringAction (NumberField.RingOfIntegers K) K L
      (NumberField.RingOfIntegers L)
  haveI hGG : IsGaloisGroup (Gal(L/K)) (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L) :=
    IsGaloisGroup.of_isFractionRing (Gal(L/K)) (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L) K L
  intro q hq
  haveI : q.asIdeal.IsPrime := q.isPrime
  haveI : q.asIdeal.LiesOver p.asIdeal := hq
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (A := NumberField.RingOfIntegers K)
    (B := NumberField.RingOfIntegers L) p.asIdeal q.asIdeal (Gal(L/K))]
  exact h

/-- **The cyclic case.**  For a finite cyclic extension `L/K`, any congruence datum whose reciprocity
hypothesis holds, and any unramified prime `Q` of `K`, the idèlic Artin map of the datum sends the
prime idèle at `Q` to the Frobenius element at `Q`. -/
theorem ideleArtin_ideleOfPrime_of_unramified_cyclic
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (Gal(L/K))]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (m : ℕ) (hm : 0 < m)
    (hram : ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m : NumberField.RingOfIntegers K) ∉ p.asIdeal →
      Ideal.ramificationIdxIn p.asIdeal (NumberField.RingOfIntegers L) = 1)
    (hprinc : NK.CFTLib.artinKillsPrincipal K L m)
    (U : Subgroup (NK.GlobalCFT.Idele K)) (hU : NK.CFTLib.Arl.IsCongruenceSubgroup (K := K) m U)
    (hadj : ∀ x : NK.GlobalCFT.Idele K, ∃ b : Kˣ,
      x * NK.GlobalCFT.Idele.principalIdele K b ∈ U)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q) :
    NK.CFTLib.Arl.ideleArtin hcomm U hadj (NK.HeckeL.ideleOfPrime K Q)
      = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q := by
  classical
  obtain ⟨Φ, hPΦ, hNΦ, hSΦ, hFΦ⟩ :=
    localGlobalArtinMap_kills_principal_cyclic (K := K) (L := L)
  obtain ⟨art, hA, hP, hN, hS, hF⟩ :=
    exists_ideleHom_ideleArtin_of_congruence_data (K := K) (L := L) hcomm m hm hram hprinc U hU hadj
  -- the finite set of primes dividing `m`
  set T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :=
    NK.CFTLib.Arl.primesDividing (K := K) m hm with hT
  have hTunr : ∀ p, p ∉ T →
      Ideal.ramificationIdxIn p.asIdeal (NumberField.RingOfIntegers L) = 1 := by
    intro p hp
    exact hram p (fun hmem => hp ((NK.CFTLib.Arl.mem_primesDividing (K := K) m hm p).mpr hmem))
  have heq : art = Φ :=
    ideleHom_eq_of_frobAtPrime_of_notMem (K := K) (L := L) hcomm T hTunr art Φ
      hP hN hS (fun p hp => hF p (fun hmem =>
        hp ((NK.CFTLib.Arl.mem_primesDividing (K := K) m hm p).mpr hmem)))
      hPΦ hNΦ hSΦ (fun p hp => hFΦ p (isUnramifiedIn_of_ramificationIdxIn_eq_one_zdataMup (K := K) (L := L) p (hTunr p hp)))
  rw [← hA (NK.HeckeL.ideleOfPrime K Q), heq, hFΦ Q hunr]

/-- **The Frobenius normalisation of the idèlic Artin map at an unramified prime dividing the
modulus.**  For a finite abelian extension `L/K` of number fields, a modulus `m > 0` satisfying the
hypotheses of the ideal-theoretic reciprocity law (`hram`: every prime `∤ (m)` is unramified;
`hprinc`: the Artin symbol kills every congruence-principal ideal), a congruence subgroup `U` of
modulus `m` with `𝕀 K = U · Kˣ`, and an unramified prime `Q` of `K` with `(m) ⊆ Q`: the idèlic
Artin map `ideleArtin` of the datum sends the prime idèle at `Q` to the Frobenius element at `Q`.

This is the `(m) ⊆ Q` case of `Work.SSGRoute.ZDataMup.ideleArtin_ideleOfPrime_of_unramified`; the
case `(m) ∌ Q` is the `hgood` clause of `NK.CFTLib.Arl.exists_monoidHom_ideleArtin`.

The reduction to the cyclic case runs through the restriction of the idèlic Artin map to the fixed
fields of the subgroups of `Gal(L/K)` with cyclic quotient, using that those restrictions are the
idèlic Artin maps of the subextensions (`ideleArtin_restrictNormalHom`) and that the Frobenius
elements restrict compatibly. -/
theorem ideleArtin_frobAtPrime_of_mem_span_of_unramified
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (m : ℕ) (hm : 0 < m)
    (hram : ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m : NumberField.RingOfIntegers K) ∉ p.asIdeal →
      Ideal.ramificationIdxIn p.asIdeal (NumberField.RingOfIntegers L) = 1)
    (hprinc : NK.CFTLib.artinKillsPrincipal K L m)
    (U : Subgroup (NK.GlobalCFT.Idele K)) (hU : NK.CFTLib.Arl.IsCongruenceSubgroup (K := K) m U)
    (hadj : ∀ x : NK.GlobalCFT.Idele K, ∃ b : Kˣ,
      x * NK.GlobalCFT.Idele.principalIdele K b ∈ U)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q)
    (hmem : (m : NumberField.RingOfIntegers K) ∈ Q.asIdeal) :
    NK.CFTLib.Arl.ideleArtin hcomm U hadj (NK.HeckeL.ideleOfPrime K Q)
      = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q := by
  classical
  letI : CommGroup (Gal(L/K)) :=
    { (inferInstance : Group (Gal(L/K))) with mul_comm := hcomm }
  set σ : Gal(L/K) := NK.CFTLib.Arl.ideleArtin hcomm U hadj (NK.HeckeL.ideleOfPrime K Q)
      * (NK.Chebotarev.frobAtPrime (K := K) (L := L) Q)⁻¹ with hσ
  suffices hs : σ = 1 by
    rw [hσ, mul_inv_eq_one] at hs
    exact hs
  have hmemσ : σ ∈ ⨅ H : {H : Subgroup (Gal(L/K)) // IsCyclic (Gal(L/K) ⧸ H)},
      (H.1 : Subgroup (Gal(L/K))) := by
    refine Subgroup.mem_iInf.mpr fun H => ?_
    obtain ⟨H₀, hHcyc⟩ := H
    haveI : Subgroup.Normal H₀ := inferInstance
    haveI hcycQ : IsCyclic (Gal(L/K) ⧸ H₀) := hHcyc
    let M : IntermediateField K L := IntermediateField.fixedField H₀
    haveI hgal : IsGalois K M := IsGalois.of_fixedField_normal_subgroup H₀
    haveI hnormM : Normal K M := inferInstance
    haveI hfdM : FiniteDimensional K M := inferInstance
    haveI hnfM : NumberField M := inferInstance
    haveI : IsCyclic (Gal(M/K)) :=
      isCyclic_of_surjective (IsGalois.normalAutEquivQuotient H₀).toMonoidHom
        (fun y => (IsGalois.normalAutEquivQuotient H₀).surjective y)
    have hcommM : ∀ a b : Gal(M/K), a * b = b * a := by
      intro a b
      obtain ⟨x, rfl⟩ := (IsGalois.normalAutEquivQuotient H₀).surjective a
      obtain ⟨y, rfl⟩ := (IsGalois.normalAutEquivQuotient H₀).surjective b
      rw [← map_mul, ← map_mul, mul_comm]
    have hunrM : NK.HeckeL.IsUnramifiedIn (K := K) (L := M) Q := by
      intro q hq
      obtain ⟨P, hP⟩ :=
        Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := M) (L := L) q
      haveI : P.asIdeal.LiesOver q.asIdeal := hP
      have hPover : P.asIdeal.LiesOver Q.asIdeal :=
        Ideal.LiesOver.trans P.asIdeal q.asIdeal Q.asIdeal
      haveI : P.asIdeal.LiesOver Q.asIdeal := hPover
      have htower := Ideal.ramificationIdx_tower (R := NumberField.RingOfIntegers K)
        (S := NumberField.RingOfIntegers M) (T := NumberField.RingOfIntegers L)
        q.asIdeal P.asIdeal
      rw [hunr P hPover] at htower
      exact Nat.eq_one_of_mul_eq_one_right htower.symm
    have hramM : ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        (m : NumberField.RingOfIntegers K) ∉ p.asIdeal →
        Ideal.ramificationIdxIn p.asIdeal (NumberField.RingOfIntegers M) = 1 :=
      fun p hp => NK.NUV2.ARL.ramificationIdxIn_eq_one_of_intermediateField M p (hram p hp)
    have hprincM : NK.CFTLib.artinKillsPrincipal K M m :=
      NK.NUV2.ARL.artinKillsPrincipal_of_intermediateField M hram hprinc
    have hcyclic : NK.CFTLib.Arl.ideleArtin hcommM U hadj (NK.HeckeL.ideleOfPrime K Q)
        = NK.Chebotarev.frobAtPrime (K := K) (L := M) Q :=
      ideleArtin_ideleOfPrime_of_unramified_cyclic (K := K) (L := M) hcommM m hm hramM hprincM
        U hU hadj Q hunrM
    have hres1 : AlgEquiv.restrictNormalHom (F := K) (K₁ := L) M
        (NK.CFTLib.Arl.ideleArtin hcomm U hadj (NK.HeckeL.ideleOfPrime K Q))
        = NK.CFTLib.Arl.ideleArtin hcommM U hadj (NK.HeckeL.ideleOfPrime K Q) :=
      ideleArtin_restrictNormalHom hcomm m hm hram U hU hadj M hcommM _
    have hres2 : AlgEquiv.restrictNormalHom (F := K) (K₁ := L) M
        (NK.Chebotarev.frobAtPrime (K := K) (L := L) Q)
        = NK.Chebotarev.frobAtPrime (K := K) (L := M) Q := by
      refine (NK.Chebotarev.ExistsUniqueIsFrobAtPrime (K := K) (L := M) hcommM Q hunrM).unique
        ?_ (NK.Chebotarev.isFrobAtPrime_frobAtPrime (K := K) (L := M) hcommM Q hunrM)
      obtain ⟨P, hP, hPfrob⟩ :=
        NK.Chebotarev.isFrobAtPrime_frobAtPrime (K := K) (L := L) hcomm Q hunr
      haveI : P.asIdeal.LiesOver Q.asIdeal := hP
      refine ⟨P.under (NumberField.RingOfIntegers M), ?_, ?_⟩
      · refine ⟨?_⟩
        rw [NK.Chebotarev.under_asIdeal M P, Ideal.under_under]
        exact hP.over
      · exact NK.Chebotarev.IsFrobAtRestrictNormalHom (M := L) M hP hPfrob
    have hker : σ ∈ (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) M).ker := by
      rw [MonoidHom.mem_ker]
      show AlgEquiv.restrictNormalHom (F := K) (K₁ := L) M σ = 1
      rw [hσ, map_mul, map_inv, hres1, hres2, hcyclic]
      exact mul_inv_cancel _
    rw [IntermediateField.restrictNormalHom_ker,
      IntermediateField.fixingSubgroup_fixedField H₀] at hker
    exact hker
  rw [NK.CFTLib.ArtinReciprocityIdeal.iInf_subgroup_isCyclic_quotient,
    Subgroup.mem_bot] at hmemσ
  exact hmemσ

end Work.SSGRoute.ZDataMup
