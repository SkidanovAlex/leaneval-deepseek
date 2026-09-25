import Mathlib
import Submission.NK.CFTLib.IdeleHasse.localNormSubgroup
import Submission.NK.CFTLib.IdeleHasse.localFaithfulDefs
import Submission.NK.CFTLib.HR.localNormSubgroup_ofInfinite_eq_top
import Submission.NK.CFTLib.IdeleHasse.cyclotomicLocalNorm_infinite
import Submission.NK.CFTLib.IdeleHasse.Crux.cyclotomicAuxiliary

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace NK.CFTLib.IdeleHasse.HilbertReciprocityCyclicProof

open NK.GlobalCFT

/-- Every number field has a (nonarchimedean) place: the height-one prime above `2`. -/
theorem exists_heightOneSpectrum_numberField (K : Type) [Field K] [NumberField K] :
    ∃ Q : HeightOneSpectrum (NumberField.RingOfIntegers K), 0 < Ideal.absNorm Q.asIdeal := by
  haveI hmax : (Ideal.span ({(2 : ℤ)} : Set ℤ)).IsMaximal :=
    Prime.isMaximal_span_singleton (Nat.prime_iff_prime_int.mp Nat.prime_two)
  obtain ⟨Q, hQmax, hQlies⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (R := ℤ)
      (S := NumberField.RingOfIntegers K) (P := Ideal.span ({(2 : ℤ)} : Set ℤ))
  haveI := hQlies
  have hne : (Ideal.span ({(2 : ℤ)} : Set ℤ)) ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]; norm_num
  have hQne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hne Q
  refine ⟨⟨Q, hQmax.isPrime, hQne⟩, ?_⟩
  exact Nat.pos_of_ne_zero fun h => hQne (Ideal.absNorm_eq_zero_iff.mp h)

/-- **The local norm subgroup at an infinite place is everything as soon as one local norm is
surjective.**  This is `NK.CFTLib.IdeleHasse.localNormSubgroup_eq_top_of_range_top` with the
(irrelevant) hypothesis `IsGalois K L` removed: the auxiliary extension `E/M` of the descent is not
Galois, but the argument — the local norm subgroup is the supremum of the local norm images — only
uses the definition. -/
theorem localNormSubgroup_ofInfinite_eq_top_of_range_top {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    {v : NumberField.InfinitePlace K} {w₀ : NumberField.InfinitePlace L} [hw : w₀.LiesOver v]
    (hrange : MonoidHom.range (NK.GlobalCFT.Place.localNormInfinite w₀ v) = ⊤) :
    NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L)
      (NK.GlobalCFT.Place.ofInfinite v) = ⊤ := by
  refine top_le_iff.mp ?_
  have h : MonoidHom.range (@NK.GlobalCFT.Place.localNormInfinite K _ L _ _ w₀ v hw) ≤
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L)
        (NK.GlobalCFT.Place.ofInfinite v) := by
    rw [NK.CFTLib.IdeleHasse.localNormSubgroup_ofInfinite]
    exact le_iSup (fun w' : {w' : NumberField.InfinitePlace L // w'.LiesOver v} =>
      MonoidHom.range (@NK.GlobalCFT.Place.localNormInfinite K _ L _ _ w'.1 v w'.2))
      ⟨w₀, hw⟩
  rw [hrange] at h
  exact h

theorem localCondition_exists_infinite {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (hcyc : IsCyclic (L ≃ₐ[K] L)) (w : NumberField.InfinitePlace K) : ∃ (M E : Type) (_ : Field M) (_ : NumberField M) (_ : Field E) (_ : NumberField E) (_ : Algebra K M) (_ : Algebra K E) (_ : Algebra L E) (_ : Algebra M E) (_ : IsScalarTower K L E) (_ : IsScalarTower K M E) (_ : FiniteDimensional K M) (_ : FiniteDimensional K E) (_ : IsGalois K M) (_ : IsGalois K E) (_ : IsCyclic (M ≃ₐ[K] M)) (q : ℕ) (_ : q.Prime) (_ : 2 < q) (_ : IsCyclotomicExtension {q} K M), (Algebra.adjoin K (Set.range (algebraMap L E) ∪ Set.range (algebraMap M E)) = ⊤) ∧ (∀ (x : Kˣ) (u : NK.GlobalCFT.Place M), NK.GlobalCFT.Place.LiesOver u (NK.GlobalCFT.Place.ofInfinite w) → Units.map (algebraMap M (NK.GlobalCFT.Place.localField M u)).toMonoidHom (Units.map (algebraMap K M).toMonoidHom x) ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := M) (L := E) u) := by
  classical
  -- ### Step 1: a finite place `Q` of `K`.
  obtain ⟨Q, hQpos⟩ := exists_heightOneSpectrum_numberField K
  -- ### Step 2: a prime `q` larger than `NQ` and than `2`.
  obtain ⟨q, hqle, hqprime⟩ :=
    Nat.exists_infinite_primes (max (Ideal.absNorm Q.asIdeal) 2 + 1)
  have hq_gt : Ideal.absNorm Q.asIdeal < q := by omega
  have hq2 : 2 < q := by omega
  have hcop : Nat.Coprime (Ideal.absNorm Q.asIdeal) q :=
    (hqprime.coprime_iff_not_dvd.mpr fun hdvd => by
      have := Nat.le_of_dvd hQpos hdvd
      omega).symm
  -- ### Step 3: the auxiliary cyclotomic fields `M = K(ζ_q)` and `E = L·M`.
  obtain ⟨M, E, hMf, hMN, hEf, hEN, hKM, hKE, hLE, hME, hstLE, hstME, hfdM, hfdE, hgalM, hgalE,
    hcycM, hcycExt, hgen, -⟩ :=
    NK.CFTLib.IdeleHasse.Crux.cyclotomicAuxiliary (K := K) (L := L) q hqprime Q hcop
  refine ⟨M, E, hMf, hMN, hEf, hEN, hKM, hKE, hLE, hME, hstLE, hstME, hfdM, hfdE, hgalM, hgalE,
    hcycM, q, hqprime, hq2, hcycExt, hgen, ?_⟩
  -- ### Step 4: `M` is totally complex, so at an infinite place of `M` the local norm subgroup
  -- is everything.
  haveI hqne : NeZero q := ⟨hqprime.ne_zero⟩
  haveI := hcycExt
  haveI hTC : NumberField.IsTotallyComplex M :=
    NK.CFTLib.IdeleHasse.isTotallyComplex_of_primitiveRoot (m := q) (by omega)
      (IsCyclotomicExtension.zeta q K M) (IsCyclotomicExtension.zeta_spec q K M)
  intro x u hu
  rcases hu with ⟨u', w', rfl, hw', hlo⟩ | ⟨q', Q', h1, h2, hlo⟩
  · -- `u = ofInfinite u'` with `u'` an infinite place of `M` above `w`.
    have hww' : w = w' := NK.GlobalCFT.Place.ofInfinite_inj.mp hw'
    subst hww'
    obtain ⟨v', hv'⟩ : ∃ v' : NumberField.InfinitePlace E, v'.LiesOver u' := by
      haveI : Algebra.IsAlgebraic M E := Algebra.IsAlgebraic.of_finite M E
      obtain ⟨v', hv'⟩ := InfinitePlace.comap_surjective (k := M) (K := E) u'
      refine ⟨v', AbsoluteValue.LiesOver.mk ?_⟩
      have hh : (v'.comap (algebraMap M E)).1 = u'.1 := congrArg Subtype.val hv'
      rw [← hh]
      rfl
    haveI : v'.LiesOver u' := hv'
    have hu'C : u'.IsComplex := NumberField.IsTotallyComplex.isComplex u'
    have hv'C : v'.IsComplex :=
      NumberField.InfinitePlace.LiesOver.isComplex_of_isComplex_under v' hu'C
    have htop : NK.CFTLib.IdeleHasse.localNormSubgroup (K := M) (L := E)
        (NK.GlobalCFT.Place.ofInfinite u') = ⊤ :=
      localNormSubgroup_ofInfinite_eq_top_of_range_top (K := M) (L := E)
        (v := u') (w₀ := v')
        (NK.NUV2.ArtinBridge.localNormInfinite_range_eq_top_of_complex_complex
          (K := M) (L := E) (v := u') (w := v') hu'C hv'C)
    rw [htop]
    exact Subgroup.mem_top _
  · exact absurd h2 (NK.GlobalCFT.Place.ofInfinite_ne_ofFinite w Q')

end NK.CFTLib.IdeleHasse.HilbertReciprocityCyclicProof
