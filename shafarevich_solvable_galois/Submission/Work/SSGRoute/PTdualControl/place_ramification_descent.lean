import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.ramificationIdx_mul_inertiaDeg_dvd_finrank
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.SSGRoute.PTdualControl

open NumberField

/-- **Reading off the ideal-level lies-over relation from the places.**  If the place `w` of `L`
lies over the place `v` of `K`, and `w`, `v` are the finite places attached to the nonzero prime
ideals `Q`, `q`, then `Q` lies over `q`.  (The two finite places cannot lie over an archimedean
place, and the finite places of `Place _` are injective.) -/
lemma liesOver_of_eq_ofFinite {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] {w : NK.GlobalCFT.Place L} {v : NK.GlobalCFT.Place K}
    (h : NK.GlobalCFT.Place.LiesOver w v)
    {Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)}
    {q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
    (hw : w = NK.GlobalCFT.Place.ofFinite Q) (hv : v = NK.GlobalCFT.Place.ofFinite q) :
    Q.asIdeal.LiesOver q.asIdeal := by
  rcases h with ⟨a, b, hab, -, -⟩ | ⟨Q₀, q₀, hQ₀, hq₀, hlies⟩
  · exact absurd (hw.symm.trans hab) (Ne.symm (NK.GlobalCFT.Place.ofInfinite_ne_ofFinite a Q))
  · rw [show Q = Q₀ from NK.GlobalCFT.Place.ofFinite_inj.mp (hw.symm.trans hQ₀),
        show q = q₀ from NK.GlobalCFT.Place.ofFinite_inj.mp (hv.symm.trans hq₀)]
    exact hlies

/-- **Place and ramification bookkeeping for the descent of the unramified detector along a
tower of number fields.**

Tower `k ⊆ K ⊆ K' ⊆ L` of number fields, all Galois over `k` and `K'` Galois over `K`, with a
tower of places `w'' | w' | w` of `L | K' | K` whose finite parts are the prime ideals `q''`,
`q'`, `q`.  If `p` does not divide the degree `[K' : K]`, and `p` does not divide the ramification
index of `q''` over `q'`, then `w''` lies over `w`, `p` does not divide the ramification index of
`q''` over `q`, and the prime ideals lie over one another.  This is the number-theoretic input of
the base-change step `K' → K` of the unramified detector `C6`: `e(q''|q) = e(q''|q') · e(q'|q)`
and `e(q'|q) ∣ [K' : K]`. -/
theorem place_ramification_descent (p : ℕ) [Fact p.Prime]
    (k K K' L : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Field K'] [NumberField K']
    [Field L] [NumberField L] [Algebra k K] [Algebra k K'] [Algebra k L] [Algebra K K']
    [Algebra K L] [Algebra K' L] [IsScalarTower k K K'] [IsScalarTower k K L]
    [IsScalarTower k K' L] [IsScalarTower K K' L]
    [FiniteDimensional k K] [FiniteDimensional k K'] [FiniteDimensional k L] [FiniteDimensional K K']
    [IsGalois k K] [IsGalois k K'] [IsGalois k L] [IsGalois K K']
    (w : NK.GlobalCFT.Place K) (w' : NK.GlobalCFT.Place K') (w'' : NK.GlobalCFT.Place L)
    (hw' : NK.GlobalCFT.Place.LiesOver w' w) (hw'' : NK.GlobalCFT.Place.LiesOver w'' w')
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K'))
    (hwq' : w' = NK.GlobalCFT.Place.ofFinite q')
    (q'' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hwq'' : w'' = NK.GlobalCFT.Place.ofFinite q'')
    (hp : ¬ p ∣ Module.finrank K K')
    (h2 : ¬ p ∣ q'.asIdeal.ramificationIdx' q''.asIdeal) :
    NK.GlobalCFT.Place.LiesOver w'' w ∧ (¬ p ∣ q.asIdeal.ramificationIdx' q''.asIdeal) ∧
    q'.asIdeal.LiesOver q.asIdeal ∧ q''.asIdeal.LiesOver q'.asIdeal := by
  -- the places have the expected prime ideals
  have hq'q : q'.asIdeal.LiesOver q.asIdeal := liesOver_of_eq_ofFinite hw' hwq' hwq
  have hq''q' : q''.asIdeal.LiesOver q'.asIdeal := liesOver_of_eq_ofFinite hw'' hwq'' hwq'
  haveI : q''.asIdeal.LiesOver q'.asIdeal := hq''q'
  haveI : q'.asIdeal.LiesOver q.asIdeal := hq'q
  -- the ideals lie over one another, hence so do the places
  have hq''q : q''.asIdeal.LiesOver q.asIdeal :=
    Ideal.LiesOver.trans q''.asIdeal q'.asIdeal q.asIdeal
  -- the ramification index of `q'` over `q` divides the degree `[K' : K]` (Galois, so the
  -- local degree `e·f` is the cardinality of the decomposition group)
  have hdvd : q.asIdeal.ramificationIdx' q'.asIdeal ∣ Module.finrank K K' := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx q.asIdeal q'.asIdeal q.ne_bot]
    exact dvd_trans (dvd_mul_right _ _)
      (Work.SSGRoute.ramificationIdx_mul_inertiaDeg_dvd_finrank K K' q q' hq'q)
  refine ⟨?_, ?_, hq'q, hq''q'⟩
  · rw [hwq'', hwq]
    exact NK.GlobalCFT.Place.liesOver_ofFinite hq''q
  · -- multiplicativity of the ramification index in the tower `𝓞 K ⊆ 𝓞 K' ⊆ 𝓞 L`
    intro hbad
    have hmul : q.asIdeal.ramificationIdx' q''.asIdeal =
        q.asIdeal.ramificationIdx' q'.asIdeal * q'.asIdeal.ramificationIdx' q''.asIdeal :=
      Ideal.ramificationIdx'_algebra_tower' q.asIdeal q'.asIdeal q''.asIdeal
    rw [hmul] at hbad
    rcases (Fact.out : p.Prime).dvd_mul.mp hbad with h | h
    · exact (fun hd : p ∣ q.asIdeal.ramificationIdx' q'.asIdeal => hp (hd.trans hdvd)) h
    · exact h2 h

end Work.SSGRoute.PTdualControl
