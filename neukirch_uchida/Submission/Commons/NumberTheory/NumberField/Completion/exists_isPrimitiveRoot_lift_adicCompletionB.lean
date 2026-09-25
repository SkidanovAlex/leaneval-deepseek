import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Submission.Commons.RingTheory.Henselian.kummer_root_lift
import Submission.Commons.RingTheory.Henselian.units_mem_pow_of_residue_mem_pow
import Submission.Commons.RingTheory.Henselian.adicCompletionIntegers_henselianLocalRing
import Submission.Commons.NumberTheory.NumberField.Completion.compactSpace_adicCompletionIntegers

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

namespace Commons.NumberTheory.NumberField.Completion

open IsDedekindDomain.HeightOneSpectrum

/-- **Teichmüller lift of a primitive root of the residue field, on the `compactSpace_adicCompletionIntegers` import route.**

Let `K ⊆ L` be number fields, `Q` a prime of `𝓞 K` and `q | Q` a prime of `𝓞 L`.  Then the ring of
integers `A_q = q.adicCompletionIntegers L` contains a unit `ζ` which is a primitive
`(|κ_q| - 1)`-st root of unity (`κ_q` the residue field of `A_q`) and whose residue in `κ_q` is also
a primitive `(|κ_q| - 1)`-st root of unity (hence generates `κ_q^×`).

This is a RE-PROOF (not a re-export) of
`Commons.NumberTheory.NumberField.Completion.exists_isPrimitiveRoot_lift_adicCompletion`, on the
library route that goes through
`Submission.Commons.NumberTheory.NumberField.Completion.compactSpace_adicCompletionIntegers`
(instead of `...finite_residueField_adicCompletion`): the declaration
`finite_residueField_adicCompletion` is duplicated in the commons by those two files, so the two
routes are mutually unimportable and downstream corpus developments on this route MUST NOT import
the original.  The proof is the same: the units of the finite residue field are cyclic, a generator
is lifted through `kummer_root_lift` / `units_mem_pow_of_residue_mem_pow` and the Henselian
structure of `A_q`, and `IsLocalRing.residue` is injective on the roots of unity so lifted. -/
theorem exists_isPrimitiveRoot_lift_adicCompletionB
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    ∃ ζ : q.adicCompletionIntegers L,
      IsPrimitiveRoot (ζ : q.adicCompletion L)
          (Nat.card (IsLocalRing.ResidueField (q.adicCompletionIntegers L)) - 1) ∧
        IsPrimitiveRoot (IsLocalRing.residue (q.adicCompletionIntegers L) ζ)
          (Nat.card (IsLocalRing.ResidueField (q.adicCompletionIntegers L)) - 1) := by
  classical
  have _hq := hq
  haveI hfin : Finite (IsLocalRing.ResidueField (q.adicCompletionIntegers L)) :=
    finite_residueField_adicCompletion L q
  haveI hhens : HenselianLocalRing (q.adicCompletionIntegers L) :=
    Commons.RingTheory.Henselian.adicCompletionIntegers_henselianLocalRing
      (R := NumberField.RingOfIntegers L) (K := L) q
  set R := q.adicCompletionIntegers L with hR
  set k := IsLocalRing.ResidueField R with hk
  set N := Nat.card k - 1 with hN
  haveI : Fintype k := Fintype.ofFinite k
  haveI : Finite kˣ := Finite.of_fintype _
  obtain ⟨ω, hωgen⟩ := IsCyclic.exists_generator (α := kˣ)
  have hωorder : orderOf (ω : k) = N := by
    rw [orderOf_units, orderOf_eq_card_of_forall_mem_zpowers hωgen, Nat.card_units, hN]
  have hωprim : IsPrimitiveRoot (ω : k) N :=
    IsPrimitiveRoot.iff_orderOf.mpr hωorder
  have h1k : 1 ≤ Nat.card k := by
    rw [Nat.card_eq_fintype_card]
    exact le_of_lt Fintype.one_lt_card
  have hNunit : IsUnit (N : R) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    simp only [map_natCast]
    have hcard0 : (Nat.card k : k) = 0 := by
      rw [Nat.card_eq_fintype_card]
      exact FiniteField.cast_card_eq_zero k
    rw [hN, Nat.cast_sub h1k, hcard0]
    simp
  have hβ : (ω : k) ^ N = IsLocalRing.residue R (1 : R) := by
    rw [map_one]
    exact hωprim.pow_eq_one
  obtain ⟨ζ, hζpow, hζres⟩ :=
    Commons.RingTheory.Henselian.kummer_root_lift (R := R) N isUnit_one hNunit (ω : k) hβ
  refine ⟨ζ, ?_, ?_⟩
  · have hdiv1 : N ∣ orderOf ζ := by
      rw [← hωorder, orderOf_dvd_iff_pow_eq_one]
      have h1 : (ω : k) ^ orderOf ζ = IsLocalRing.residue R (ζ ^ orderOf ζ) := by
        rw [map_pow, hζres]
      rw [h1, pow_orderOf_eq_one, map_one]
    have hdiv2 : orderOf ζ ∣ N := orderOf_dvd_iff_pow_eq_one.mpr hζpow
    have hordζ : orderOf ζ = N := (Nat.dvd_antisymm hdiv1 hdiv2).symm
    have hζprim : IsPrimitiveRoot ζ N := IsPrimitiveRoot.iff_orderOf.mpr hordζ
    have hmap := hζprim.map_of_injective (f := ValuationSubring.subtype (q.adicCompletionIntegers L))
      (ValuationSubring.subtype_injective (q.adicCompletionIntegers L))
    simpa only [ValuationSubring.subtype_apply] using hmap
  · rw [hζres]
    exact hωprim

end Commons.NumberTheory.NumberField.Completion