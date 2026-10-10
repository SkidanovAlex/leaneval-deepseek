import Mathlib.NumberTheory.RamificationInertia.Galois
import Submission.Work.SSGRoute.CycLevel.card_stabilizer_eq_of_localNormSubgroup_index
import Submission.Work.SSGRoute.ZDataMup.localNormSubgroup_eq_top_of_split
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.SSGRoute.ZDataMup

/-- **The order of the decomposition group of a finite place.**

For a finite Galois extension `L / K` of number fields, a nonzero prime `Q` of `𝓞 K` and a prime
`q` of `𝓞 L` lying over `Q`: the stabiliser of the place `q` (i.e. the place `Place.ofFinite q`)
under the action of `Gal(L/K)` on the places of `L` has cardinality `e(q|Q) · f(q|Q)`.

This is the order of the decomposition group: the stabiliser of the finite place is the
`Commons` decomposition subgroup (`NK.GlobalCFT.Inclusion.globalCFT_mem_decompositionSubgroup_iff`),
whose order is `e · f` (`Commons.NumberTheory.NumberField.Completion.card_decompositionSubgroup`). -/
lemma stabilizer_ofFinite_card_eq {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    Nat.card (MulAction.stabilizer (L ≃ₐ[K] L) (NK.GlobalCFT.Place.ofFinite q)) =
      Q.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers L) *
        Q.asIdeal.inertiaDegIn (NumberField.RingOfIntegers L) := by
  have hstab : MulAction.stabilizer (L ≃ₐ[K] L) (NK.GlobalCFT.Place.ofFinite q) =
      Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) q := by
    ext σ
    rw [MulAction.mem_stabilizer_iff,
      NK.GlobalCFT.Inclusion.globalCFT_mem_decompositionSubgroup_iff,
      NK.GlobalCFT.Place.smul_ofFinite, NK.GlobalCFT.Place.ofFinite_inj]
  rw [hstab]
  exact Commons.NumberTheory.NumberField.Completion.card_decompositionSubgroup Q q hq

/-- **A completely split place has trivial ramification index and inertia degree.**

If `L / K` is a finite Galois extension of number fields of prime degree `p` and the local norm
subgroup at a finite place `Q` of `K` is everything, then every prime `q` of `𝓞 L` above `Q` is
unramified of residue degree one, i.e. `Q` splits completely in `L`.

The local norm subgroup at `Q` is the supremum of the ranges of the local norms `N_{L_q/K_Q}`
over the primes `q | Q`; by the local norm index theorem (`index_normGroup_eq_finrank`, packaged
in `Work.SSGRoute.CycLevel.card_stabilizer_eq_of_localNormSubgroup_index`) its index is the order
of the decomposition group of `q`, i.e. `e(q|Q) · f(q|Q)`.  If it is the whole of `K_Qˣ` this index
is `1`, hence `e(q|Q) · f(q|Q) = 1` and both factors equal one.

The hypothesis `Nat.card (L ≃ₐ[K] L) = p` with `p` prime is used exactly to make `Gal(L/K)` cyclic
(hence commutative), which is the hypothesis under which all local norm subgroups of the primes
above `Q` coincide, so that the index of their supremum computes the local degree. -/
theorem ramificationIdx_eq_one_of_localNormSubgroup_eq_top {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {p : ℕ} [Fact p.Prime] (hcard : Nat.card (L ≃ₐ[K] L) = p)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (h : NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite Q) = ⊤) :
    ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
      q.asIdeal.LiesOver Q.asIdeal →
      Q.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers L) = 1 ∧
      Q.asIdeal.inertiaDegIn (NumberField.RingOfIntegers L) = 1 := by
  -- `Gal(L/K)` has prime order, hence is cyclic and commutative.
  haveI hcyc : IsCyclic (L ≃ₐ[K] L) := isCyclic_of_prime_card hcard
  intro q hq
  -- The local norm subgroup being everything makes the decomposition group trivial.
  have hstab : Nat.card
      (MulAction.stabilizer (L ≃ₐ[K] L) (NK.GlobalCFT.Place.ofFinite q)) = 1 := by
    rw [Work.SSGRoute.CycLevel.card_stabilizer_eq_of_localNormSubgroup_index (k := K) (L := L)
        Q (NK.GlobalCFT.Place.ofFinite q) (NK.GlobalCFT.Place.liesOver_ofFinite hq), h,
      Subgroup.index_top]
  -- The decomposition group has order `e · f`, so `e · f = 1`.
  have hef : Q.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers L) *
      Q.asIdeal.inertiaDegIn (NumberField.RingOfIntegers L) = 1 := by
    rw [← stabilizer_ofFinite_card_eq Q q hq, hstab]
  exact ⟨Nat.eq_one_of_mul_eq_one_right hef, Nat.eq_one_of_mul_eq_one_left hef⟩

end Work.SSGRoute.ZDataMup
