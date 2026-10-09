import Mathlib.RingTheory.RamificationInertia.Basic
import Submission.Commons.NumberTheory.NumberField.finite_primesOver
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.NumberField

set_option linter.style.haveILetI false

/-- For a number field extension `L / K`, the number of primes of `𝓞 L` lying over a
nonzero prime `p` of `𝓞 K` is at most the degree `[L : K]`.

The set of primes over `p` is finite, and the fundamental identity of ramification gives
`∑ q, e(q) f(q) = [𝓞 L : 𝓞 K] = [L : K]`, where every summand is at least `1`. -/
theorem ncard_primesOver_le_finrank {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (p.asIdeal.primesOver (NumberField.RingOfIntegers L)).ncard ≤ Module.finrank K L := by
  classical
  haveI : p.asIdeal.IsPrime := p.isPrime
  have hp0 : p.asIdeal ≠ ⊥ := p.ne_bot
  haveI hfin : (p.asIdeal.primesOver (NumberField.RingOfIntegers L)).Finite :=
    finite_primesOver (K := K) (L := L) p.asIdeal inferInstance hp0
  letI : Fintype (p.asIdeal.primesOver (NumberField.RingOfIntegers L)) := hfin.fintype
  have hsum :
      (∑ q : p.asIdeal.primesOver (NumberField.RingOfIntegers L),
          q.1.ramificationIdx (NumberField.RingOfIntegers K) *
            q.1.inertiaDeg (NumberField.RingOfIntegers K)) =
        Module.finrank (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) :=
    Ideal.sum_ramification_inertia_eq_finrank (R := NumberField.RingOfIntegers K)
      (S := NumberField.RingOfIntegers L) p.asIdeal
  have hcard :
      Fintype.card (p.asIdeal.primesOver (NumberField.RingOfIntegers L)) ≤
        Module.finrank (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) := by
    rw [← hsum, ← Finset.card_univ, Finset.card_eq_sum_ones]
    refine Finset.sum_le_sum fun q _ => ?_
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
      (Ideal.ramificationIdx_pos (NumberField.RingOfIntegers K) q.1).ne'
      (Ideal.inertiaDeg_pos q.1 (NumberField.RingOfIntegers K)).ne')
  rw [← Set.fintypeCard_eq_ncard]
  refine hcard.trans ?_
  exact le_of_eq (IsFractionRing.finrank_eq (NumberField.RingOfIntegers K) K
    (NumberField.RingOfIntegers L) L).symm

end Commons.NumberTheory.NumberField