import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Submission.NK.CFTLib.HR.TransferAux.localLevelMap_injective_vanishing
import Submission.NK.CFTLib.HRdescent.localConditionCyclotomicPrime
import Submission.NK.HassePrinciple.ideleInclusion_smul_of_restrict
import Submission.NK.NUV2.ARL.HR.locUnits_inflation_eq_zero_iff
import Submission.NK.NUV2.ArtinBridge.kummerE_le_normImage_of_isGalois_exp
import Submission.NK.NUV2.ChebAux.Transfer.cycClassOf_translation
import Submission.NK.NUV2.ChebAux.Transfer.locUnits_res_inflation_eq_zero
import Submission.NK.NUV2.LC.localNormFinite_range_iff_val_pow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataMup

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

/-- **The idèlic Artin map is compatible with restriction to a normal intermediate field.**

For a finite abelian Galois extension `L/K` of number fields, a modulus `m > 0` unramified in `L`
outside the primes dividing `m`, a congruence subgroup `U` of modulus `m` with an adjustment
`𝕀 K = U · Kˣ`, and a normal intermediate field `M` of `L/K` with `Gal(M/K)` abelian: restricting
the idèlic Artin map `ideleArtin` of `L/K` to `M` gives the idèlic Artin map of `M/K`.

Both sides are, by definition, the product `∏_𝔭 Frob_𝔭 ^ (count 𝔭 A)` of the chosen Frobenius
elements at the primes occurring in the fractional ideal `A` of the adjusted idèle, so the content
is the compatibility `(Frob_𝔭)|_M = Frob_𝔭` of the Frobenius elements.  This holds at every prime
`𝔭 ∤ (m)`, and no prime dividing `(m)` occurs in `A`: the adjusted idèle lies in the congruence
subgroup, so it is a local unit at each `𝔭 | (m)`. -/
theorem ideleArtin_restrictNormalHom
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (m : ℕ) (hm : 0 < m)
    (hram : ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m : NumberField.RingOfIntegers K) ∉ p.asIdeal →
      Ideal.ramificationIdxIn p.asIdeal (NumberField.RingOfIntegers L) = 1)
    (U : Subgroup (NK.GlobalCFT.Idele K))
    (hU : NK.CFTLib.Arl.IsCongruenceSubgroup (K := K) m U)
    (hadj : ∀ x : NK.GlobalCFT.Idele K, ∃ b : Kˣ,
      x * NK.GlobalCFT.Idele.principalIdele K b ∈ U)
    (M : IntermediateField K L) [FiniteDimensional K M] [NumberField ↥M] [Normal K M]
    (hcommM : ∀ a b : Gal(↥M/K), a * b = b * a)
    (x : NK.GlobalCFT.Idele K) :
    AlgEquiv.restrictNormalHom (F := K) (K₁ := L) M
        (NK.CFTLib.Arl.ideleArtin hcomm U hadj x)
      = NK.CFTLib.Arl.ideleArtin hcommM U hadj x := by
  classical
  -- The adjusted idèle lies in the congruence subgroup of modulus `m`.
  have hcong : (x * NK.GlobalCFT.Idele.principalIdele K (NK.CFTLib.Arl.adjust U hadj x))
      ∈ NK.CFTLib.Arl.congruenceSubgroup K m :=
    (hU.1 _).mp (NK.CFTLib.Arl.adjust_spec U hadj x)
  -- Hence no prime dividing `(m)` occurs in its ideal.
  have hcount : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (m : 𝓞 K) ∈ 𝔭.asIdeal →
      FractionalIdeal.count K 𝔭 (NK.GlobalCFT.Idele.idealOf
        (x * NK.GlobalCFT.Idele.principalIdele K (NK.CFTLib.Arl.adjust U hadj x))) = 0 :=
    fun 𝔭 h𝔭 => NK.CFTLib.ARL.count_idealOf_eq_zero_of_congruence hcong 𝔭 h𝔭
  -- The chosen Frobenius elements are compatible with restriction to `M`.
  have hfrob : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (m : 𝓞 K) ∉ 𝔭.asIdeal →
      AlgEquiv.restrictNormalHom (F := K) (K₁ := L) M
          (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭)
        = NK.Chebotarev.frobAtPrime (K := K) (L := ↥M) 𝔭 := by
    intro 𝔭 h𝔭
    -- `𝔭` is unramified in `L` ...
    have hunrL : ∀ P : NK.Chebotarev.PrimeIdeal L, P.asIdeal.LiesOver 𝔭.asIdeal →
        P.asIdeal.ramificationIdx (𝓞 K) = 1 := by
      intro P hP
      rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (A := 𝓞 K) (B := 𝓞 L)
        𝔭.asIdeal P.asIdeal (Gal(L/K))]
      exact hram 𝔭 h𝔭
    -- ... hence also in `M`, by multiplicativity of the ramification index in a tower.
    have hunrM : ∀ Q : NK.Chebotarev.PrimeIdeal ↥M, Q.asIdeal.LiesOver 𝔭.asIdeal →
        Q.asIdeal.ramificationIdx (𝓞 K) = 1 := by
      intro Q hQ
      haveI : IsScalarTower (𝓞 K) (𝓞 ↥M) (𝓞 L) := inferInstance
      haveI : Module.Flat (𝓞 ↥M) (𝓞 L) := inferInstance
      obtain ⟨P, hP⟩ :=
        Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := ↥M) (L := L) Q
      haveI : P.asIdeal.LiesOver Q.asIdeal := hP
      have hPQ : P.asIdeal.LiesOver 𝔭.asIdeal :=
        Ideal.LiesOver.trans P.asIdeal Q.asIdeal 𝔭.asIdeal
      haveI := hPQ
      have htw := Ideal.ramificationIdx_tower (R := 𝓞 K) (S := 𝓞 ↥M) (T := 𝓞 L)
        Q.asIdeal P.asIdeal
      rw [hunrL P hPQ] at htw
      exact Nat.eq_one_of_mul_eq_one_right htw.symm
    -- Both sides are Frobenius elements at `𝔭` in `M/K`, where the Frobenius is unique.
    have h1 : NK.Chebotarev.IsFrobAtPrime (K := K) (L := ↥M) 𝔭
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) M
          (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭)) := by
      obtain ⟨P, hP, hPfrob⟩ :=
        NK.Chebotarev.isFrobAtPrime_frobAtPrime (K := K) (L := L) hcomm 𝔭 hunrL
      refine ⟨P.under (𝓞 ↥M), ?_, ?_⟩
      · refine ⟨?_⟩
        rw [NK.Chebotarev.under_asIdeal M P, Ideal.under_under]
        exact hP.over
      · exact NK.Chebotarev.IsFrobAtRestrictNormalHom (M := L) M hP hPfrob
    have h2 : NK.Chebotarev.IsFrobAtPrime (K := K) (L := ↥M) 𝔭
        (NK.Chebotarev.frobAtPrime (K := K) (L := ↥M) 𝔭) :=
      NK.Chebotarev.isFrobAtPrime_frobAtPrime (K := K) (L := ↥M) hcommM 𝔭 hunrM
    exact (NK.Chebotarev.ExistsUniqueIsFrobAtPrime (K := K) (L := ↥M) hcommM 𝔭 hunrM).unique
      h1 h2
  -- Unfold the two idèlic Artin maps to products of Frobenius elements.
  show AlgEquiv.restrictNormalHom (F := K) (K₁ := L) M
      (NK.CFTLib.Arl.artinSym hcomm (NK.GlobalCFT.Idele.idealOf
        (x * NK.GlobalCFT.Idele.principalIdele K (NK.CFTLib.Arl.adjust U hadj x))))
    = NK.CFTLib.Arl.artinSym hcommM (NK.GlobalCFT.Idele.idealOf
        (x * NK.GlobalCFT.Idele.principalIdele K (NK.CFTLib.Arl.adjust U hadj x)))
  set A : FractionalIdeal (𝓞 K)⁰ K := NK.GlobalCFT.Idele.idealOf
    (x * NK.GlobalCFT.Idele.principalIdele K (NK.CFTLib.Arl.adjust U hadj x)) with hA
  have hcountA : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (m : 𝓞 K) ∈ 𝔭.asIdeal →
      FractionalIdeal.count K 𝔭 A = 0 := by
    intro 𝔭 h𝔭
    rw [hA]
    exact hcount 𝔭 h𝔭
  letI := NK.CFTLib.Arl.galCommMonoid hcomm
  letI := NK.CFTLib.Arl.galCommMonoid hcommM
  have hL : NK.CFTLib.Arl.artinSym hcomm A =
      ∏ 𝔭 ∈ (NK.CFTLib.Arl.exps A).support,
        (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) ^ ((NK.CFTLib.Arl.exps A) 𝔭) := by
    unfold NK.CFTLib.Arl.artinSym
    exact Finsupp.prod_of_support_subset (NK.CFTLib.Arl.exps A) le_rfl _
      (fun i _ => zpow_zero _)
  have hR : NK.CFTLib.Arl.artinSym hcommM A =
      ∏ 𝔭 ∈ (NK.CFTLib.Arl.exps A).support,
        (NK.Chebotarev.frobAtPrime (K := K) (L := ↥M) 𝔭) ^ ((NK.CFTLib.Arl.exps A) 𝔭) := by
    unfold NK.CFTLib.Arl.artinSym
    exact Finsupp.prod_of_support_subset (NK.CFTLib.Arl.exps A) le_rfl _
      (fun i _ => zpow_zero _)
  rw [hL, hR, map_prod]
  refine Finset.prod_congr rfl (fun 𝔭 h𝔭 => ?_)
  have hne : (NK.CFTLib.Arl.exps A) 𝔭 ≠ 0 := Finsupp.mem_support_iff.mp h𝔭
  have hne' : FractionalIdeal.count K 𝔭 A ≠ 0 := by
    rwa [NK.CFTLib.Arl.exps_apply] at hne
  have hm𝔭 : (m : 𝓞 K) ∉ 𝔭.asIdeal := fun h => hne' (hcountA 𝔭 h)
  rw [map_zpow, hfrob 𝔭 hm𝔭]

end Work.SSGRoute.ZDataMup
