import Mathlib
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.Defs
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.TUnitsPow
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.KummerLocalUnit
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.exists_goodS
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.exists_place_notMem_of_notMem_Lpow
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.kummerE_le_normImage
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.principal_inf_kummerE_eq_tUnitsPow
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.exists_kummerT_data
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.exists_tUnits_surj
import Submission.NK.GlobalCFTdeep.Herbrand.top_eq_principal_sup_TIdeles
import Submission.NK.GlobalCFTdeep.SecondInequality.tUnits_index_powSubgroup
import Submission.NK.GlobalCFTdeep.SecondInequality.finrank_eq_one_of_le_normImage
import Submission.NK.GlobalCFTdeep.SecondInequality.pow_mem_normGroup_adicCompletion
import Submission.Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely

open scoped NumberField RestrictedProduct

namespace NK.GlobalCFTdeep.SecondInequality.KummerCase

open NK.GlobalCFT

/-- **The `T`-set of the Kummer case of the second inequality** (Milne, *Class Field Theory*,
VII §6, Lemmas 6.2–6.4, 6.7, 6.9, 6.10): for the Kummer extension `L = K(α)`, `α ^ p = a`, with
`ζ_p ∈ K` and `a` an `S`-unit, there is a finite set `T` of primes outside `S`, splitting
completely in `L`, with `|S| = |T| + 1`, such that Milne's subgroup
`E = ∏_{v ∈ S} K_v^{×p} · ∏_{v ∈ T} K_v^× · ∏_{v ∉ S ∪ T} U_v` is contained in `N_{L/K} 𝕀_L` and
satisfies `Kˣ ∩ E = U(S ∪ T)^p`.

This is the input of the index computation `[𝕀_K : Kˣ · E] = p` of Milne 6.5–6.8. -/
theorem exists_kummerT_core {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    {p : ℕ} (hp : p.Prime) (hcard : Nat.card (L ≃ₐ[K] L) = p) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {a : K} (ha : a ≠ 0) {α : L} (hα : α ^ p = algebraMap K L a)
    (hadj : IntermediateField.adjoin K {α} = ⊤)
    (S : Finset (NK.GlobalCFT.Place K))
    (hSinf : ∀ w : NumberField.InfinitePlace K, NK.GlobalCFT.Place.ofInfinite w ∈ S)
    (hSp : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K), (p : NumberField.RingOfIntegers K) ∈ q.asIdeal → NK.GlobalCFT.Place.ofFinite q ∈ S)
    (hSram : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (∃ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L), Q.asIdeal.LiesOver q.asIdeal ∧
        Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) ≠ 1) → NK.GlobalCFT.Place.ofFinite q ∈ S)
    (haS : Units.mk0 a ha ∈ NK.GlobalCFTdeep.TUnits (S : Set (NK.GlobalCFT.Place K)))
    (hSgen : (⊤ : Subgroup (NK.GlobalCFT.Idele K)) =
      NK.GlobalCFT.Idele.principalSubgroup K ⊔ NK.GlobalCFTdeep.TIdeles (S : Set (NK.GlobalCFT.Place K))) :
    ∃ T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      (∀ q ∈ T, NK.GlobalCFT.Place.ofFinite q ∉ S) ∧
      S.card = T.card + 1 ∧
      (∀ q ∈ T, ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L), Q.asIdeal.LiesOver q.asIdeal →
        Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 ∧ Q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = 1) ∧
      KummerCase.kummerE (K := K) p S (T.map (KummerCase.placeOfFiniteEmb K)) ≤ NK.GlobalCFT.Idele.normImage K L ∧
      (NK.GlobalCFT.Idele.principalSubgroup K ⊓ KummerCase.kummerE (K := K) p S (T.map (KummerCase.placeOfFiniteEmb K))
        = KummerCase.tUnitsPowIdele (K := K) p
            ((S : Set (NK.GlobalCFT.Place K)) ∪ ((T.map (KummerCase.placeOfFiniteEmb K) : Finset (NK.GlobalCFT.Place K)) : Set (NK.GlobalCFT.Place K)))) := by
  -- Claim A, in the form consumed by `exists_kummerT_data`
  have hA : ∀ b : K, ∀ hb : b ≠ 0,
      Units.mk0 b hb ∈ NK.GlobalCFTdeep.TUnits (L := K) (S : Set (NK.GlobalCFT.Place K)) →
      (∃ β : L, β ^ p = algebraMap K L b) →
      Units.mk0 b hb ∈ Subgroup.closure {Units.mk0 a ha} ⊔
        Subgroup.map (powMonoidHom p)
          (NK.GlobalCFTdeep.TUnits (L := K) (S : Set (NK.GlobalCFT.Place K))) :=
    fun b hb hbS hbl =>
      mem_kummerH0_of_exists_pow_eq hp hcard hζ ha hα hadj S haS hb hbS hbl
  -- Claim B
  have hB : ∀ b : K, ∀ hb : b ≠ 0,
      Units.mk0 b hb ∈ NK.GlobalCFTdeep.TUnits (L := K) (S : Set (NK.GlobalCFT.Place K)) →
      (¬ ∃ β : L, β ^ p = algebraMap K L b) →
      ∃ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        NK.GlobalCFT.Place.ofFinite q ∉ S ∧
        (∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
          Q.asIdeal.LiesOver q.asIdeal →
            Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 ∧
            Q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = 1) ∧
        (¬ ∃ c : (q.adicCompletion K)ˣ,
          algebraMap K (q.adicCompletion K) b =
            ((c : (q.adicCompletion K)ˣ) : q.adicCompletion K) ^ p) :=
    fun b hb hbS hbl =>
      exists_place_notMem_of_notMem_Lpow hp hcard hζ ha hα hadj S hSinf hSp hSram hb hbS hbl
  -- the set `T`
  obtain ⟨T, hTdisj, hTcard, hTsplit, hTker⟩ :=
    exists_kummerT_data hp hcard hζ ha hα hadj S hSinf hSp haS hA hB
  -- `a` is a `p`-th power of a local unit at each `q ∈ T`
  have haq : ∀ q ∈ T, ∃ c : (q.adicCompletionIntegers K)ˣ,
      algebraMap K (q.adicCompletion K) a =
        ((c : q.adicCompletionIntegers K) : q.adicCompletion K) ^ p := by
    intro q hq
    refine exists_unit_pow_eq_of_splitsCompletely hp ha hα q (hTsplit q hq) ?_
    exact (mem_TUnits.mp haS) (Place.ofFinite q) (hTdisj q hq)
  -- the surjectivity of Milne 6.9
  have hsurj := exists_tUnits_surj hp hζ S hSinf hSp a ha haS T hTdisj hTcard haq hTker
  exact ⟨T, hTdisj, hTcard, hTsplit,
    kummerE_le_normImage hp hcard hζ ha hα hadj S hSinf hSp hSram T hTdisj hTsplit,
    principal_inf_kummerE_eq_tUnitsPow hp hζ S hSinf hSp hSgen T hTdisj hsurj⟩

end NK.GlobalCFTdeep.SecondInequality.KummerCase
