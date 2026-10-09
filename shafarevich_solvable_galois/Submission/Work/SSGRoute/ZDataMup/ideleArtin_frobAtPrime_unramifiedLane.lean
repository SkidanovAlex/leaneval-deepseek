import Mathlib
import Submission.Work.SSGRoute.ZDataMup.NKArtinUmbrella
import Submission.Work.SSGRoute.ZDataMup.conductorDrop_ramifiedCongrLane
import Submission.NK.CFTLib.ArtinReciprocityIdeal.langX2KernelLe
import Submission.NK.CFTLib.ArtinReciprocityIdeal.artinSymbol_span_eq_one_of_kernelLe_of_relIndex
import Submission.NK.CFTLib.ArtinReciprocityIdeal.indexPrincipalRaySupNormRayLe
import Submission.NK.CFTLib.ArtinReciprocityIdeal.langCyclicRelIndex
import Submission.NK.CFTLib.ArtinReciprocityIdeal.exists_admissible
import Submission.NK.CFTLib.ArtinReciprocityIdeal.artinKillsPrincipal_cyclic
import Submission.NK.CFTLib.ArtinReciprocityIdeal.iInf_subgroup_isCyclic_quotient
import Submission.Work.SSGRoute.ZDataMup.ideleArtin_independent_of_congruence_data
import Submission.NK.NUV2.ARL.abelianWeakToStrong
import Submission.Work.SSGRoute.ZDataMup.CyclicCaseStatement
import Submission.Work.SSGRoute.ZDataMup.ideleArtin_restrictNormalHom
import Submission.Work.SSGRoute.ZDataMup.LaneUnramifiedImports
import Submission.NK.CFTLib.ArtinReciprocityIdeal.iInf_subgroup_isCyclic_quotient
import Submission.NK.Chebotarev.ExistsUniqueIsFrobAtPrime
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.Defs
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.exists_idealModulus_of_natModulus
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.hprinc_idealModulus_ramifiedSupport
import Submission.Work.SSGRoute.ZDataMup.IdealModulusKernelLeProved
import Submission.Work.SSGRoute.ZDataMup.IdealModulusIndexProved
import Submission.Work.SSGRoute.ZDataMup.IdealModulusContainmentProved
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.ZDataMup

open NK.GlobalCFT

/- ## The two pieces of the proof

The target is assembled from

* the **cyclic case**, which is the Frobenius normalisation of the idèlic Artin map obtained from
  the *conductor drop at the ramified primes* for a cyclic extension
  (`Work.SSGRoute.ZDataMup.CyclicCaseStatement`) exactly as in
  `Submission/Work/SSGRoute/ZDataMup/ideleArtin_frob_unramified_abelian.lean`; and
* the **reduction of the abelian case to the cyclic quotients**, via
  `Work.SSGRoute.ZDataMup.ideleArtin_restrictNormalHom`,
  `NK.CFTLib.ArtinReciprocityIdeal.iInf_subgroup_isCyclic_quotient` and the Frobenius
  restriction lemma `restrictNormalHom_frobAtPrime_lane` below.
-/

/-- **Frobenius elements restrict along a normal intermediate field.** -/
lemma restrictNormalHom_frobAtPrime_lane
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (M : IntermediateField K L) [FiniteDimensional K M] [NumberField ↥M] [Normal K ↥M]
    (hcommM : ∀ a b : Gal(↥M/K), a * b = b * a)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) 𝔭) :
    AlgEquiv.restrictNormalHom (F := K) (K₁ := L) M
        (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭)
      = NK.Chebotarev.frobAtPrime (K := K) (L := ↥M) 𝔭 := by
  classical
  have hunrL : ∀ P : NK.Chebotarev.PrimeIdeal L, P.asIdeal.LiesOver 𝔭.asIdeal →
      P.asIdeal.ramificationIdx (𝓞 K) = 1 := hunr
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

/-- **The cyclic case: the conductor drop at the ramified primes normalises the idèlic Artin map
at every unramified prime.**

This is the proof of
`Submission/Work/SSGRoute/ZDataMup/ideleArtin_frob_unramified_abelian.lean`, with the appeal to
the conductor drop made explicit through the hypothesis `hcd`. -/
theorem cyclic_frobAtPrime_of_unramified_lane
    (hcd : CyclicCaseStatement)
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (Gal(L/K))]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (m : ℕ) (hm : 0 < m)
    (hram : ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m : NumberField.RingOfIntegers K) ∉ p.asIdeal →
      Ideal.ramificationIdxIn p.asIdeal (NumberField.RingOfIntegers L) = 1)
    (hprinc : NK.CFTLib.artinKillsPrincipal K L m)
    (U : Subgroup (NK.GlobalCFT.Idele K))
    (hU : NK.CFTLib.Arl.IsCongruenceSubgroup (K := K) m U)
    (hadj : ∀ x : NK.GlobalCFT.Idele K, ∃ b : Kˣ,
      x * NK.GlobalCFT.Idele.principalIdele K b ∈ U)
    {Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
    (hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q) :
    NK.CFTLib.Arl.ideleArtin (K := K) (L := L) hcomm U hadj (NK.HeckeL.ideleOfPrime K Q)
      = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q := by
  classical
  set b : Kˣ := NK.CFTLib.Arl.adjust U hadj (NK.HeckeL.ideleOfPrime K Q) with hbdef
  have hspec : NK.HeckeL.ideleOfPrime K Q * NK.GlobalCFT.Idele.principalIdele K b ∈ U :=
    NK.CFTLib.Arl.adjust_spec U hadj _
  have hcongU :=
    (hU.1 (NK.HeckeL.ideleOfPrime K Q * NK.GlobalCFT.Idele.principalIdele K b)).mp hspec
  have hQunrIn : Ideal.ramificationIdxIn Q.asIdeal (NumberField.RingOfIntegers L) = 1 := by
    obtain ⟨P, hP⟩ := NK.Chebotarev.exists_primeIdeal_liesOver (K := K) (L := L) Q
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx (A := NumberField.RingOfIntegers K)
      (B := NumberField.RingOfIntegers L) Q.asIdeal P.asIdeal (Gal(L/K))]
    exact hunr P hP
  have hcomp : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K), 𝔮 ≠ Q →
      (NK.HeckeL.ideleOfPrime K Q * NK.GlobalCFT.Idele.principalIdele K b)
          (NK.GlobalCFT.Place.ofFinite 𝔮)
        = Units.map (algebraMap K (𝔮.adicCompletion K)).toMonoidHom b := by
    intro 𝔮 h𝔮
    rw [NK.GlobalCFT.Idele.mul_apply, NK.CFTLib.IdeleHasse.ideleOfPrime_apply_ofFinite_ne_exists h𝔮,
      one_mul, NK.GlobalCFT.Idele.principalIdele_apply]
    rfl
  have hcompInf : ∀ w : InfinitePlace K,
      (NK.HeckeL.ideleOfPrime K Q * NK.GlobalCFT.Idele.principalIdele K b)
          (NK.GlobalCFT.Place.ofInfinite w)
        = Units.map (algebraMap K w.Completion).toMonoidHom b := by
    intro w
    rw [NK.GlobalCFT.Idele.mul_apply, NK.CFTLib.IdeleHasse.ideleOfPrime_apply_ofInfinite, one_mul,
      NK.GlobalCFT.Idele.principalIdele_apply]
    rfl
  have hcong : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m : NumberField.RingOfIntegers K) ∈ 𝔮.asIdeal →
      Ideal.ramificationIdxIn 𝔮.asIdeal (NumberField.RingOfIntegers L) ≠ 1 →
      Valued.v (algebraMap K (𝔮.adicCompletion K) ((b : Kˣ) : K) - 1)
        ≤ Valued.v ((m : ℕ) : 𝔮.adicCompletion K) := by
    intro 𝔮 h𝔮 hram𝔮
    have h𝔮Q : 𝔮 ≠ Q := by
      intro h; subst h; exact hram𝔮 hQunrIn
    have hval := (hcongU.1 𝔮 h𝔮)
    rw [hcomp 𝔮 h𝔮Q] at hval
    simpa using hval
  have hpos : ∀ (w : InfinitePlace K) (hw : w.IsReal),
      0 < (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
            (algebraMap K w.Completion ((b : Kˣ) : K)) := by
    intro w hw
    have hval := (hcongU.2 w) hw
    rw [hcompInf w] at hval
    simpa using hval
  -- the conductor drop at the ramified primes
  have hb1 : NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
        ((b : Kˣ) : K)) = 1 :=
    hcd (hcomm := hcomm) (M := m) (hM := hm) (hramM := hram) (hprincM := hprinc)
      (b := b) (hcong := hcong) (hpos := hpos)
  have hA : ((Q.asIdeal : Ideal (NumberField.RingOfIntegers K)) :
        FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr Q.ne_bot
  have hB : FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
      ((b : Kˣ) : K) ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Units.ne_zero _)
  show NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
      (Idele.idealOf (NK.HeckeL.ideleOfPrime K Q * NK.GlobalCFT.Idele.principalIdele K b))
    = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q
  rw [Idele.idealOf_mul, NK.CFTLib.Arl.idealOf_ideleOfPrime, Idele.idealOf_principalIdele,
    NK.CFTLib.Arl.artinSym_mul (K := K) (L := L) hcomm hA hB, hb1, mul_one,
    NK.CFTLib.Arl.artinSym_prime]


/-- **The "good case" of the Frobenius normalisation: an unramified prime `Q` with `Q ∤ (m)`.**

This is the case of `ideleArtin_frobAtPrime_unramifiedLane` in which the rational prime below `Q`
does not divide `m`: the whole congruence content of the target sits at the primes dividing `(m)`,
and there `ideleOfPrime K Q` has component `1`, so the adjustment `b` is itself congruent `1`
modulo `m`; `principalRay_le_ker_of_artinKillsPrincipal` (equivalently the `hgood` clause of
`NK.CFTLib.Arl.exists_monoidHom_ideleArtin`, i.e. `Work.SSGRoute.ZDataMup.exists_ideleHom_ideleArtin_of_congruence_data`)
then gives the claim directly. -/
theorem ideleArtin_ideleOfPrime_of_notMem
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (m : ℕ) (hm : 0 < m)
    (hram : ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m : NumberField.RingOfIntegers K) ∉ p.asIdeal →
      Ideal.ramificationIdxIn p.asIdeal (NumberField.RingOfIntegers L) = 1)
    (hprinc : NK.CFTLib.artinKillsPrincipal K L m)
    (U : Subgroup (NK.GlobalCFT.Idele K))
    (hU : NK.CFTLib.Arl.IsCongruenceSubgroup (K := K) m U)
    (hadj : ∀ x : NK.GlobalCFT.Idele K, ∃ b : Kˣ,
      x * NK.GlobalCFT.Idele.principalIdele K b ∈ U)
    {Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
    (hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q)
    (hQm : (m : NumberField.RingOfIntegers K) ∉ Q.asIdeal) :
    NK.CFTLib.Arl.ideleArtin (K := K) (L := L) hcomm U hadj (NK.HeckeL.ideleOfPrime K Q)
      = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q := by
  obtain ⟨art, hagree, -, -, -, hgood⟩ :=
    exists_ideleHom_ideleArtin_of_congruence_data (K := K) (L := L) hcomm m hm hram hprinc U hU
      hadj
  rw [← hagree]
  exact hgood Q hQm


open NK.CFTLib.ArtinReciprocityIdeal in
/-- **The cyclic case of the conductor drop, from the ideal-modulus Lang theory.**

`Work.SSGRoute.ZDataMup.CyclicCaseStatement` (the conductor drop at a natural-number modulus, the
hypothesis of the assembly below) follows from the Lang–Artin machinery at an *ideal* modulus
`𝔪 = ∏_{𝔭 ramified} 𝔭^{v_𝔭(M)}`, produced by
`NK.CFTLib.ArtinReciprocityIdeal.exists_idealModulus_of_natModulus`: the ideal modulus has support
*exactly* the ramified primes (no natural-number modulus has this property, its support being
saturated above the rational primes), so the conductor drop is available at every prime not in that
support — including the unramified primes dividing `(M)`.

The two arithmetic inputs are proved in this workspace:

* `IdealModulusKernelLeProved` — Lang's transfer `ker ψ ∩ I(𝔪) ⊆ P(𝔪)·𝔑(𝔪)`,
* `IdealModulusIndexProved` — the norm index inequality `[L:K] ≤ [I(𝔪) : P(𝔪)·𝔑(𝔪)]`,
* `IdealModulusContainmentProved` — the containment `P(𝔪)·𝔑(𝔪) ≤ I(𝔪)`. -/
theorem cyclicCaseStatement_of_idealModulus : CyclicCaseStatement := by
  intro K L _ _ _ _ _ _ _ _ hcomm M hM hramM hprincM b hcong hpos
  haveI hcyc : IsCyclic (L ≃ₐ[K] L) := inferInstance
  have hunrOf : ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (M : NumberField.RingOfIntegers K) ∉ p.asIdeal →
      Ideal.ramificationIdxIn p.asIdeal (NumberField.RingOfIntegers L) = 1 := hramM
  rcases Nat.eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hM)) with hM1 | hM2
  · -- `M = 1`: `hramM` says that every prime is unramified, and the congruence is vacuous
    subst hM1
    exact NK.CFTLib.Arl.artinSym_spanSingleton_eq_one (K := K) (L := L) hcomm 1 one_pos hramM
      hprincM b
      (fun 𝔭 hmem => absurd hmem (fun h => 𝔭.isPrime.ne_top
        ((Ideal.eq_top_iff_one 𝔭.asIdeal).mpr (by simpa using h)))) hpos
  · -- `M > 1`: the ideal modulus supported exactly on the ramified primes
    have hadm : NK.CFTLib.ArtinReciprocityIdeal.IsAdmissible K L M :=
      isAdmissible_of_artinKillsPrincipal (K := K) (L := L) hcomm M hM hramM hprincM
    obtain ⟨𝔪, h𝔪, hadmId, hramId, _hsupp, hcongId⟩ :=
      exists_idealModulus_of_natModulus (K := K) (L := L) M hM2 hramM hadm
    exact NK.CFTLib.ArtinReciprocityIdeal.artinSym_spanSingleton_eq_one_of_congrOneId
      (K := K) (L := L) hcomm 𝔪 h𝔪 hramId
      (fun A hcop hsym =>
        IdealModulusKernelLeProved (K := K) (L := L) hcomm 𝔪 h𝔪 hadmId hramId A hcop hsym)
      (IdealModulusContainmentProved (K := K) (L := L) 𝔪 h𝔪)
      (IdealModulusIndexProved (K := K) (L := L) 𝔪 h𝔪 hramId hadmId)
      b (hcongId b hcong hpos)

/-- **The target from the cyclic case.**

The abelian case is reduced to its cyclic quotients: an element of `Gal(L/K)` is trivial as soon as
its restrictions to the fixed fields of all the subgroups with cyclic quotient are trivial
(`NK.CFTLib.ArtinReciprocityIdeal.iInf_subgroup_isCyclic_quotient`), and the restriction of the
idèlic Artin map to such a fixed field is the idèlic Artin map of the subextension
(`Work.SSGRoute.ZDataMup.ideleArtin_restrictNormalHom`), while the Frobenius elements restrict
compatibly (`restrictNormalHom_frobAtPrime_lane`). -/
theorem ideleArtin_frobAtPrime_unramifiedLane_of_cyclicDrop
    (hcd : CyclicCaseStatement)
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (m : ℕ) (hm : 0 < m)
    (hram : ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m : NumberField.RingOfIntegers K) ∉ p.asIdeal →
      Ideal.ramificationIdxIn p.asIdeal (NumberField.RingOfIntegers L) = 1)
    (hprinc : NK.CFTLib.artinKillsPrincipal K L m)
    (U : Subgroup (NK.GlobalCFT.Idele K))
    (hU : NK.CFTLib.Arl.IsCongruenceSubgroup (K := K) m U)
    (hadj : ∀ x : NK.GlobalCFT.Idele K, ∃ b : Kˣ,
      x * NK.GlobalCFT.Idele.principalIdele K b ∈ U)
    {Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
    (hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q) :
    NK.CFTLib.Arl.ideleArtin (K := K) (L := L) hcomm U hadj (NK.HeckeL.ideleOfPrime K Q)
      = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q := by
  classical
  haveI : IsMulCommutative (L ≃ₐ[K] L) := IsMulCommutative.of_comm hcomm
  have hbot : (⨅ H : {H : Subgroup Gal(L/K) // IsCyclic (Gal(L/K) ⧸ H)},
      (H.1 : Subgroup Gal(L/K))) = ⊥ := by
    letI : CommGroup (Gal(L/K)) :=
      { (inferInstance : Group (Gal(L/K))) with mul_comm := fun a b => hcomm a b }
    exact NK.CFTLib.ArtinReciprocityIdeal.iInf_subgroup_isCyclic_quotient
  have hmem : ∀ H : Subgroup Gal(L/K), IsCyclic (Gal(L/K) ⧸ H) →
      NK.CFTLib.Arl.ideleArtin (K := K) (L := L) hcomm U hadj (NK.HeckeL.ideleOfPrime K Q)
        * (NK.Chebotarev.frobAtPrime (K := K) (L := L) Q)⁻¹ ∈ H := by
    intro H hHcyc
    let M : IntermediateField K L := IntermediateField.fixedField H
    haveI : FiniteDimensional K M := inferInstance
    haveI : NumberField ↥M := inferInstance
    haveI : Normal K M := inferInstance
    haveI : IsGalois K ↥M :=
      Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
    haveI : IsCyclic (Gal(↥M/K)) :=
      (MulEquiv.isCyclic (IsGalois.normalAutEquivQuotient H).symm).mpr hHcyc
    have hcommM : ∀ a b : Gal(↥M/K), a * b = b * a :=
      fun a b => IsCyclic.isMulCommutative.is_comm.comm a b
    have hcyclic : NK.CFTLib.Arl.ideleArtin (K := K) (L := ↥M) hcommM U hadj
        (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := ↥M) Q := by
      refine cyclic_frobAtPrime_of_unramified_lane (K := K) (L := ↥M) hcd hcommM m hm
        (fun p hp => NK.NUV2.ARL.ramificationIdxIn_eq_one_of_intermediateField M p (hram p hp))
        (NK.NUV2.ARL.artinKillsPrincipal_of_intermediateField (M := M) (m := m) hram hprinc)
        U hU hadj ?_
      intro q hq
      obtain ⟨P, hP⟩ :=
        Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := ↥M) (L := L) q
      haveI : P.asIdeal.LiesOver q.asIdeal := hP
      have hPq : P.asIdeal.LiesOver Q.asIdeal :=
        Ideal.LiesOver.trans P.asIdeal q.asIdeal Q.asIdeal
      haveI := hPq
      have htw := Ideal.ramificationIdx_tower (R := 𝓞 K) (S := 𝓞 ↥M) (T := 𝓞 L)
        q.asIdeal P.asIdeal
      rw [hunr P hPq] at htw
      exact Nat.eq_one_of_mul_eq_one_right htw.symm
    have hrestrict : AlgEquiv.restrictNormalHom (F := K) (K₁ := L) M
        (NK.CFTLib.Arl.ideleArtin (K := K) (L := L) hcomm U hadj (NK.HeckeL.ideleOfPrime K Q))
        = NK.CFTLib.Arl.ideleArtin (K := K) (L := ↥M) hcommM U hadj
            (NK.HeckeL.ideleOfPrime K Q) :=
      ideleArtin_restrictNormalHom (K := K) (L := L) hcomm m hm hram U hU hadj M hcommM _
    have hfrobM : AlgEquiv.restrictNormalHom (F := K) (K₁ := L) M
        (NK.Chebotarev.frobAtPrime (K := K) (L := L) Q)
        = NK.Chebotarev.frobAtPrime (K := K) (L := ↥M) Q :=
      restrictNormalHom_frobAtPrime_lane (K := K) (L := L) hcomm M hcommM Q hunr
    have hker : NK.CFTLib.Arl.ideleArtin (K := K) (L := L) hcomm U hadj
          (NK.HeckeL.ideleOfPrime K Q)
        * (NK.Chebotarev.frobAtPrime (K := K) (L := L) Q)⁻¹
        ∈ (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) M).ker := by
      rw [MonoidHom.mem_ker]
      show AlgEquiv.restrictNormalHom (F := K) (K₁ := L) M
          (NK.CFTLib.Arl.ideleArtin (K := K) (L := L) hcomm U hadj
              (NK.HeckeL.ideleOfPrime K Q)
            * (NK.Chebotarev.frobAtPrime (K := K) (L := L) Q)⁻¹) = 1
      rw [map_mul, map_inv, hrestrict, hfrobM, hcyclic]
      exact mul_inv_cancel _
    rw [IntermediateField.restrictNormalHom_ker,
      IntermediateField.fixingSubgroup_fixedField H] at hker
    exact hker
  have hmeminf : NK.CFTLib.Arl.ideleArtin (K := K) (L := L) hcomm U hadj
      (NK.HeckeL.ideleOfPrime K Q) * (NK.Chebotarev.frobAtPrime (K := K) (L := L) Q)⁻¹
      ∈ ⨅ H : {H : Subgroup Gal(L/K) // IsCyclic (Gal(L/K) ⧸ H)}, (H.1 : Subgroup Gal(L/K)) :=
    Subgroup.mem_iInf.mpr fun H => hmem H.1 H.2
  rw [hbot, Subgroup.mem_bot] at hmeminf
  exact mul_inv_eq_one.mp hmeminf

/-- **Frobenius normalisation of the idèlic Artin map at *every* unramified prime.**

Let `L/K` be a finite abelian extension of number fields, `m > 0` a modulus whose primes `∤ (m)`
are unramified in `L` (`hram`) and for which the ideal-theoretic Artin symbol kills every
congruence-principal ideal (`hprinc`, i.e. `NK.CFTLib.artinKillsPrincipal K L m`), `U` the
congruence subgroup of modulus `m` with an adjustment `𝕀 K = U · Kˣ` (`hadj`).  Then the idèlic
Artin map

  `NK.CFTLib.Arl.ideleArtin hcomm U hadj x = artinSym (idealOf (x * principalIdele K (adjust x)))`

sends the prime idèle at `Q` to the Frobenius element `frobAtPrime Q` for **every** prime `Q`
unramified in `L/K`, including the primes dividing `(m)`.

If `b = adjust U hadj (ideleOfPrime K Q)` then `ideleOfPrime K Q * principalIdele K b ∈ U`, so
`b ≡ 1 mod m` at every ramified `𝔮 | (m)` with `𝔮 ≠ Q` (the component of `ideleOfPrime K Q` there
is `1`) and `b` is totally positive; since `Q` is unramified no congruence is needed at `Q`, so
`conductorDrop_ramifiedCongrLane` gives `artinSym (b) = 1`, and
`artinSym (Q · (b)) = frobAtPrime Q · 1`.

(This is `Work.SSGRoute.ZDataMup.ideleArtin_ideleOfPrime_of_unramified`, restated at a fresh path
so that this lane has a clean module to import; the proof may be transplanted from
`Submission/Work/SSGRoute/ZDataMup/ideleArtin_frob_unramified_abelian.lean`, where the same
argument is already carried out modulo the one `conductorDrop` appeal.) -/
theorem ideleArtin_frobAtPrime_unramifiedLane
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (m : ℕ) (hm : 0 < m)
    (hram : ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m : NumberField.RingOfIntegers K) ∉ p.asIdeal →
      Ideal.ramificationIdxIn p.asIdeal (NumberField.RingOfIntegers L) = 1)
    (hprinc : NK.CFTLib.artinKillsPrincipal K L m)
    (U : Subgroup (NK.GlobalCFT.Idele K))
    (hU : NK.CFTLib.Arl.IsCongruenceSubgroup (K := K) m U)
    (hadj : ∀ x : NK.GlobalCFT.Idele K, ∃ b : Kˣ,
      x * NK.GlobalCFT.Idele.principalIdele K b ∈ U)
    {Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
    (hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q) :
    NK.CFTLib.Arl.ideleArtin (K := K) (L := L) hcomm U hadj (NK.HeckeL.ideleOfPrime K Q)
      = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q := by
  exact ideleArtin_frobAtPrime_unramifiedLane_of_cyclicDrop cyclicCaseStatement_of_idealModulus
    hcomm m hm hram hprinc U hU hadj hunr
end Work.SSGRoute.ZDataMup


/-!
## State of the proof of `ideleArtin_frobAtPrime_unramifiedLane` (measured)

**Proved here and clean:**

* `ideleArtin_ideleOfPrime_of_notMem` — the *good case* `(m : 𝓞 K) ∉ Q.asIdeal`: immediate from the
  `hgood` clause of `Work.SSGRoute.ZDataMup.exists_ideleHom_ideleArtin_of_congruence_data`
  (i.e. `NK.CFTLib.Arl.exists_monoidHom_ideleArtin`).
* `ideleArtin_frobAtPrime_unramifiedLane_of_cyclicDrop` and `ideleArtin_restrictNormalHom`,
  reducing the abelian case to the cyclic one and the cyclic case to `CyclicCaseStatement`.

**The obstruction (the whole difficulty).**  In the remaining case `Q ∣ (m)` the element
`b := adjust U hadj (ideleOfPrime K Q)` has `v_Q(b) ≠ 0`, hence `b` is *not* `≡ 1 mod m` at `Q`:
no modulus `m'` whatsoever can satisfy both `hram(m')` and `CongrOne m' b`.  Equivalently, every
`ℕ`-modulus containing all the ramified primes also contains `Q` (`supp(m)` is saturated above the
rational primes), so the Frobenius normalisation obtained from a congruence datum never covers an
unramified prime dividing the modulus.  The classical input needed is

> the conductor of `L/K` is supported on the ramified primes
> (Neukirch, *ANT*, V.6.1; Lang, *ANT*, X §4),

equivalently Milne, *CFT*, VII.8.1(a) (`Φ` kills `Kˣ` for the glued local–global Artin map), i.e.
the *strong* form `∑_v inv_v(x) = 0` of Hilbert reciprocity.

**What is on disk cleanly, and why it does not suffice:**
* the one-place form of Hilbert reciprocity (`NK.CFTLib.hilbertReciprocity_onePlace_aux`,
  `NK.CFTLib.IdeleHasse.badSet_not_singleton`, clean): the bad set of `x ∈ Kˣ` is never a
  *singleton*.  This kills the case in which the bad set of the adjustment is a single place but
  says nothing about two or more places — and the *strong* form is what the conductor drop needs.
* the Lang/Artin-lemma transfer and index theorem, but only for `ℕ`-moduli
  (`NK.CFTLib.ArtinReciprocityIdeal.langX2KernelLe`, `NK.NUV2.ARL.Gap.langCyclicRelIndex`,
  `Work.SSGRoute.ZDataMup.artinKillsPrincipal_of_isAdmissible`): they give
  `artinKillsPrincipal K L m'` for every admissible `m'` containing the ramified primes, but such
  an `m'` is saturated, i.e. contains `Q`.
* the glued local–global Artin map `Φ₀` (`NK.CFTLib.IdeleHasse.localGlobalArtinMap_exists`, clean),
  which *is* Frobenius-normalised at every unramified prime but is not known to kill the principal
  idèles `Kˣ`: that statement *is* Milne VII.8.1(a).

**The two routes to close the gap** (both new library content, cf.
`Submission/Work/SSGRoute/ZDataMup/NOTE_conductorDrop_obstruction.md`):
(a) the strong form of Hilbert reciprocity (Milne VII.8.1(a)/(b)), or
(b) the Lang transfer/index machinery at an *ideal* modulus (cycle) — the vocabulary exists in
`Submission/Work/SSGRoute/ZDataMup/CycleDefs.lean` and the target statement of that lane is
`Work.SSGRoute.ZDataMup.cycleConductorDrop`.

**Reduction of the gap obtained here (new).**  Iterating the restriction identity
`ideleArtin_restrictNormalHom` over the normal subfields `↥M` of `L/K` that are unramified above
the rational prime of `Q` shows that the error `ε := ideleArtin (ideleOfPrime K Q) * frob_Q⁻¹`
lies in the inertia group of *every* rational prime carrying a ramified prime of `L/K`
(`ε ∈ ⋂_{q ∈ P(R)} I_q`); killing that residual is exactly the conductor drop again.
-/
