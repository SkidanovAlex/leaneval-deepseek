import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.PT.finHalfData
import Submission.Work.SSGRoute.ZPlace
import Submission.Work.SSGRoute.exists_finset_unramifiedPlaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

open scoped algebraMap

/-! ## Two helpers for the finiteness of a transversal's bad places -/

/-- The `(-).valuation (·) < 1` condition of the valuation subring attached to a height-one prime
`P` of `𝓞 N` agrees with that of the `P`-adic valuation `P.valuation N`. -/
theorem valuationSubringAtPrime_valuation_lt_one_iff {N : Type} [Field N] [NumberField N]
    (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers N)) (x : N) :
    (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime N P).valuation x < 1 ↔
      P.valuation N x < 1 := by
  refine Valuation.IsEquiv.lt_one_iff_lt_one ?_
  rw [Valuation.isEquiv_iff_valuationSubring, ValuationSubring.valuationSubring_valuation,
    ← IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]

/-- **Only finitely many primes of `𝓞 k` lie above a rational prime `p`.** -/
theorem finite_setOf_val_lt_one_nat (k : Type) [Field k] [NumberField k] (p : ℕ) [Fact p.Prime] :
    {q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k) |
      q.valuation k (p : k) < 1}.Finite := by
  have h0 : ((p : ℕ) : NumberField.RingOfIntegers k) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero
  have hsp : Ideal.span {((p : ℕ) : NumberField.RingOfIntegers k)} ≠ ⊥ := by
    intro h
    exact h0 (Ideal.span_singleton_eq_bot.mp h)
  refine (Ideal.finite_factors (I := Ideal.span {((p : ℕ) : NumberField.RingOfIntegers k)})
    hsp).subset ?_
  intro q hq
  have h2 : q.valuation k (algebraMap (NumberField.RingOfIntegers k) k
      ((p : ℕ) : NumberField.RingOfIntegers k)) < 1 := by simpa using hq
  exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_dvd (K := k) q _).mp h2

/-- **The prime of `𝓞 N` below a place ramified in a finite Galois level is genuinely ramified.**
If `B` is a finite place of `Ω` and `B` is ramified in the finite Galois extension `N/k`, then the
prime of `𝓞 N` below `B` has ramification index `≠ 1` over the prime of `𝓞 k` induced by `B`. -/
theorem exists_ramifiedPrime_of_isRamifiedIn {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (N : IntermediateField k Ω) [FiniteDimensional k N]
    [IsGalois k N] (B : ValuationSubring Ω) (hB : SSGRoute.IsFinPlace k B)
    (hram : SSGRoute.IsRamifiedIn k N B) :
    ∃ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥N),
      P.asIdeal.LiesOver (Submission.NeukirchUchida.primeOf B hB).asIdeal ∧
      P.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) ≠ 1 := by
  by_contra h
  push Not at h
  exact (Work.SSGRoute.not_isRamifiedIn_of_levelSub_le_fixingSubgroup N B
    (Work.SSGRoute.levelSub_le_fixingSubgroup_of_ramificationIdx_eq_one N B hB
      (Submission.NeukirchUchida.primeOf B hB)
      (Submission.NeukirchUchida.primeOf_spec B hB) h)) hram

/-- **The "bad" elements of a transversal of the finite places of `Ω` form a finite set.**

Let `R` be a set of finite places of `Ω` meeting every `Gal(Ω/k)`-orbit of finite places of `Ω`
exactly once (one place per prime of `k`), and `p` a prime.  Then the `v ∈ R` that are *bad* —
lying over the rational prime `p`, ramified over `k` in the finite Galois level `K`, ramified over
`k` in the finite Galois level `L`, or belonging to a prescribed finite set `Sbad ⊆ R` — are
finite.

Proof: two elements of `R` lying over the same prime of `k` are conjugate, hence equal by `hRdisj`;
so `R` injects into the places of `k` via `v ↦ v.comap (algebraMap k Ω)`
(`Work.SSGRoute.isConjPlace_iff_comap_eq_of_isFinPlace`, or directly via
`Commons.RingTheory.Valuation.exists_smul_eq_of_comap_eq`).  The bad primes of `k` — those above
`p`, those ramified in `K` (`Work.SSGRoute.finite_setOf_primeUnder_ramified`,
`Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one`), those ramified in `L`, and
the (finitely many, since `Sbad` is finite) primes under the places of `Sbad`
(`Work.SSGRoute.finite_setOf_primeUnder`) — are therefore finite, and each bad `v ∈ R` has its
trace in that finite set.  For the primes above `p`: they divide the ideal `(p)` of `𝓞 k`, so they
are finite (`Ideal.finite_factors`) — any equivalent available statement may be used. -/
theorem vf_bad_finset {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField K] (L : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L]
    [NumberField L] (hKL : K ≤ L) (p : ℕ) [Fact p.Prime]
    (R : Set (ValuationSubring Ω)) (hRfin : ∀ v ∈ R, SSGRoute.IsFinPlace k v)
    (hRdisj : ∀ v ∈ R, ∀ w ∈ R, SSGRoute.IsConjPlace k v w → v = w)
    (hRcov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → ∃ v ∈ R, SSGRoute.IsConjPlace k v B)
    (Sbad : Set (ValuationSubring Ω)) (hSbadR : ∀ v ∈ Sbad, v ∈ R) (hSbadfin : Sbad.Finite) :
    ∃ T : Finset (ValuationSubring Ω), (∀ v ∈ T, v ∈ R) ∧
      ∀ v ∈ R, (v.valuation (p : Ω) < 1 ∨ SSGRoute.IsRamifiedIn k K v ∨ SSGRoute.IsRamifiedIn k L v ∨
        v ∈ Sbad) → v ∈ T := by
  classical
  haveI hSep : IsSepClosure k Ω := inferInstance
  haveI hGalΩ : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  -- ## The finitely many "bad" primes of `𝓞 k`
  -- ramified in `K`
  have hKfin : ({q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k) |
      ∃ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
        P.asIdeal.LiesOver q.asIdeal ∧
          P.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) ≠ 1}).Finite :=
    Work.SSGRoute.finite_setOf_primeUnder_ramified (k := k) (Ω := Ω) K
  -- ramified in `L`
  have hLfin : ({q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k) |
      ∃ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L),
        P.asIdeal.LiesOver q.asIdeal ∧
          P.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) ≠ 1}).Finite :=
    Work.SSGRoute.finite_setOf_primeUnder_ramified (k := k) (Ω := Ω) L
  -- above `p`
  have hpfin : ({q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k) |
      q.valuation k (p : k) < 1}).Finite := finite_setOf_val_lt_one_nat k p
  -- below a place of `Sbad`
  have hSfin : ({q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k) |
      ∃ w ∈ Sbad, w.comap (algebraMap k Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k q}).Finite := by
    refine (Work.SSGRoute.finite_setOf_primeUnder (k := k) (Ω := Ω) hSbadfin.toFinset).subset ?_
    rintro q ⟨w, hw, hwq⟩
    exact ⟨w, (Set.Finite.mem_toFinset hSbadfin).mpr hw, hwq⟩
  -- the union of the four
  let Pbad : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k)) :=
    {q | q.valuation k (p : k) < 1 ∨
      (∃ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
        P.asIdeal.LiesOver q.asIdeal ∧
          P.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) ≠ 1) ∨
      (∃ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L),
        P.asIdeal.LiesOver q.asIdeal ∧
          P.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) ≠ 1) ∨
      (∃ w ∈ Sbad, w.comap (algebraMap k Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k q)}
  have hPbad : Pbad.Finite := by
    refine (hpfin.union (hKfin.union (hLfin.union hSfin))).subset ?_
    intro q hq
    simpa only [Pbad, Set.mem_union, Set.mem_ofPred_eq] using hq
  -- their images in the places of `k`
  let BadV : Set (ValuationSubring k) :=
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k '' Pbad
  have hBadV : BadV.Finite := hPbad.image _
  -- ## The bad places of `R`
  let s : Set (ValuationSubring Ω) := {v | v ∈ R ∧
    (v.valuation (p : Ω) < 1 ∨ SSGRoute.IsRamifiedIn k K v ∨
      SSGRoute.IsRamifiedIn k L v ∨ v ∈ Sbad)}
  have hs : s.Finite := by
    refine Set.Finite.of_finite_image
      (f := fun v : ValuationSubring Ω => v.comap (algebraMap k Ω)) ?_ ?_
    · refine hBadV.subset ?_
      rintro x ⟨v, hv, rfl⟩
      dsimp only [s] at hv
      obtain ⟨hvR, hvbad⟩ := hv
      have hvfin : SSGRoute.IsFinPlace k v := hRfin v hvR
      have hqspec : v.comap (algebraMap k Ω) =
          IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k
            (Submission.NeukirchUchida.primeOf v hvfin) :=
        Submission.NeukirchUchida.primeOf_spec v hvfin
      have hmemPbad : Submission.NeukirchUchida.primeOf v hvfin ∈ Pbad := by
        dsimp only [Pbad]
        rw [Set.mem_ofPred_eq]
        rcases hvbad with hval | hramK | hramL | hmem
        · refine Or.inl ?_
          have h1 : (v.comap (algebraMap k Ω)).valuation (p : k) < 1 :=
            (Work.SSGRoute.comap_valuation_lt_one_iff v (p : k)).mpr (by simpa using hval)
          rw [hqspec] at h1
          exact (valuationSubringAtPrime_valuation_lt_one_iff
            (Submission.NeukirchUchida.primeOf v hvfin) (p : k)).mp h1
        · exact Or.inr (Or.inl (exists_ramifiedPrime_of_isRamifiedIn K v hvfin hramK))
        · exact Or.inr (Or.inr (Or.inl (exists_ramifiedPrime_of_isRamifiedIn L v hvfin hramL)))
        · exact Or.inr (Or.inr (Or.inr ⟨v, hmem, hqspec⟩))
      change v.comap (algebraMap k Ω) ∈
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k '' Pbad)
      rw [Set.mem_image]
      exact ⟨Submission.NeukirchUchida.primeOf v hvfin, hmemPbad, hqspec.symm⟩
    · intro v hv w hw hcomap
      dsimp only [s] at hv hw
      have hvR : v ∈ R := hv.1
      have hwR : w ∈ R := hw.1
      have hconj : SSGRoute.IsConjPlace k v w :=
        Commons.FieldTheory.Galois.exists_smul_eq_of_comap_eq v w (hRfin v hvR) hcomap
      exact hRdisj v hvR w hwR hconj
  refine ⟨hs.toFinset, ?_, ?_⟩
  · intro v hv
    exact ((Set.Finite.mem_toFinset hs).mp hv).1
  · intro v hvR hbad
    exact (Set.Finite.mem_toFinset hs).mpr ⟨hvR, hbad⟩

end Work.SSGRoute.PT
