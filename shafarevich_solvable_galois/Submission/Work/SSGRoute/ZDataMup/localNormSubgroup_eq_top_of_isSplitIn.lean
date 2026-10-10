import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.ZDataMup.localNormSubgroup_eq_top_of_split
import Submission.Work.SSGRoute.exists_split_place_avoiding
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local norm subgroup at a finite place that splits completely

Let `K/k` be a finite Galois extension of number fields, `Ω` an algebraic closure of `k`, `E/K` a
finite Galois subextension of `Ω/K`, and `A` a finite place of `Ω`.  If `A` is completely
decomposed in `E/K` (`SSGRoute.IsSplitIn ↥K E A`) and `A` restricts to the place of `K` defined by
the height-one prime `Q`, then the local norm subgroup of `E/K` at `Q` is everything.

The route is:

* `NK.Reconstruct.stabilizer_le_fixingSubgroup_iff_splitCompletely` turns the splitting of the
  place `A` into the statement that `Q` splits completely in `E/K`
  (`(Q.asIdeal.primesOver (𝓞 E)).ncard = [E : K]`);
* `Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely` reads this as
  `ramificationIdxIn = 1 ∧ inertiaDegIn = 1`;
* the two `…In`-to-`…`-conversions below turn these into the per-prime conditions
  `q.asIdeal.ramificationIdx (𝓞 K) = 1 ∧ q.asIdeal.inertiaDeg (𝓞 K) = 1` for every `q | Q`;
* finally `localNormSubgroup_eq_top_of_split` concludes.
-/

set_option linter.style.haveILetI false

open scoped NumberField

namespace Work.SSGRoute.ZDataMup

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **Per-prime ramification index from the Galois-invariant one.**  If `ramificationIdxIn` of `Q`
in `L` is `1`, then so is the ramification index of every prime of `L` above `Q`. -/
theorem ramificationIdx_eq_one_of_ramificationIdxIn_eq_one
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (h : Q.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers L) = 1)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 := by
  letI hMSA : MulSemiringAction (L ≃ₐ[K] L) (NumberField.RingOfIntegers L) :=
    IsIntegralClosure.MulSemiringAction (NumberField.RingOfIntegers K) K L
      (NumberField.RingOfIntegers L)
  haveI hGG : IsGaloisGroup (L ≃ₐ[K] L) (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L) :=
    IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L) K L
  haveI : q.asIdeal.IsPrime := q.isPrime
  haveI : q.asIdeal.LiesOver Q.asIdeal := hq
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (A := NumberField.RingOfIntegers K)
    (B := NumberField.RingOfIntegers L) Q.asIdeal q.asIdeal (L ≃ₐ[K] L)]
  exact h

/-- **Per-prime inertia degree from the Galois-invariant one.**  If `inertiaDegIn` of `Q` in `L`
is `1`, then so is the inertia degree of every prime of `L` above `Q`. -/
theorem inertiaDeg_eq_one_of_inertiaDegIn_eq_one
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (h : Q.asIdeal.inertiaDegIn (NumberField.RingOfIntegers L) = 1)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = 1 := by
  letI hMSA : MulSemiringAction (L ≃ₐ[K] L) (NumberField.RingOfIntegers L) :=
    IsIntegralClosure.MulSemiringAction (NumberField.RingOfIntegers K) K L
      (NumberField.RingOfIntegers L)
  haveI hGG : IsGaloisGroup (L ≃ₐ[K] L) (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L) :=
    IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L) K L
  haveI : q.asIdeal.IsPrime := q.isPrime
  haveI : q.asIdeal.LiesOver Q.asIdeal := hq
  rw [← Ideal.inertiaDegIn_eq_inertiaDeg (A := NumberField.RingOfIntegers K)
    (B := NumberField.RingOfIntegers L) Q.asIdeal q.asIdeal (L ≃ₐ[K] L)]
  exact h

theorem localNormSubgroup_eq_top_of_isSplitIn {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField ↥K]
    (E : IntermediateField ↥K Ω) [FiniteDimensional ↥K E] [IsGalois ↥K E] [NumberField ↥E]
    (A : ValuationSubring Ω) (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (hQ : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K Q)
    (hsplit : SSGRoute.IsSplitIn ↥K E A) :
    NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥E)
      (NK.GlobalCFT.Place.ofFinite Q) = ⊤ := by
  classical
  -- `Ω` is an algebraic (indeed separable) closure of `K` as well.
  haveI hAlgCl : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
  haveI hSepCl : IsSepClosure ↥K Ω := inferInstance
  -- The splitting of the place `A` is total splitting of `Q` in `E/K`.
  have hnc : (Q.asIdeal.primesOver (NumberField.RingOfIntegers ↥E)).ncard
      = Module.finrank ↥K ↥E :=
    (NK.Reconstruct.stabilizer_le_fixingSubgroup_iff_splitCompletely (K := ↥K) (K' := Ω)
      (N := E) Q A hQ).mp hsplit
  have hIn : Q.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers ↥E) = 1 ∧
      Q.asIdeal.inertiaDegIn (NumberField.RingOfIntegers ↥E) = 1 :=
    (Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely
      (K := ↥K) (L := ↥E) Q).mp hnc
  refine localNormSubgroup_eq_top_of_split (K := ↥K) (L := ↥E) Q ?_
  intro q hq
  exact ⟨ramificationIdx_eq_one_of_ramificationIdxIn_eq_one (K := ↥K) (L := ↥E) Q hIn.1 q hq,
         inertiaDeg_eq_one_of_inertiaDegIn_eq_one (K := ↥K) (L := ↥E) Q hIn.2 q hq⟩

end Work.SSGRoute.ZDataMup
