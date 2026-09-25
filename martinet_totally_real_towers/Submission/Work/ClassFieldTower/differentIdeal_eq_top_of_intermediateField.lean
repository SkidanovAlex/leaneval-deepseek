import Mathlib
import Submission.Work.ClassFieldTower.Defs
import Submission.Commons.NumberTheory.NumberField.differentIdeal_eq_top_of_ramificationIdx

set_option linter.style.haveILetI false

namespace Work.ClassFieldTower

open scoped NumberField
open NumberField

/-- **A subextension of an unramified extension of number fields is unramified.**

If `differentIdeal (𝓞 E) (𝓞 K) = ⊤` (no ramified prime of `K/E`) and `L` is a finite dimensional
intermediate field `E ⊆ L ⊆ K`, then `differentIdeal (𝓞 E) (𝓞 ↥L) = ⊤`.

Proof strategy: use `Commons.NumberTheory.NumberField.differentIdeal_eq_top_of_ramificationIdx`; for a
prime `q` of `𝓞 ↥L` choose a prime `Q` of `𝓞 K` above `q`, then
`ramificationIdx (𝓞 E) Q = 1` because `Q ∤ differentIdeal (𝓞 E) (𝓞 K)` (via
`Commons.NumberTheory.NumberField.ramificationIdx_one_iff_not_dvd_differentIdeal`), and
multiplicativity of ramification indices (`Ideal.ramificationIdx_tower`, or
`Ideal.ramificationIdx_below_dvd` in divisibility form) gives `ramificationIdx (𝓞 E) q = 1`. -/
theorem differentIdeal_eq_top_of_intermediateField {E K : Type*} [Field E] [NumberField E]
    [Field K] [NumberField K] [Algebra E K]
    (h : differentIdeal (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers K) = ⊤)
    (L : IntermediateField E K) [FiniteDimensional E ↥L] [NumberField ↥L] :
    differentIdeal (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers ↥L) = ⊤ := by
  classical
  -- It suffices that no prime ideal of `𝓞 ↥L` divides the relative different of `L/E`.
  refine Commons.NumberTheory.NumberField.differentIdeal_eq_top_of_forall_not_dvd
    (E := E) (K := ↥L) ?_
  intro q hq
  by_cases hqbot : q = ⊥
  · -- The zero ideal cannot divide a nonzero ideal.
    subst hqbot
    intro hdvd
    obtain ⟨c, hc⟩ := hdvd
    exact differentIdeal_ne_bot (by rw [hc]; simp)
  · -- a nonzero prime `q` of `𝓞 ↥L` is maximal, so it has a prime `Q` of `𝓞 K` above it
    have hqmax : q.IsMaximal := hq.isMaximal hqbot
    obtain ⟨Q, hQmax, hQlies⟩ :=
      Ideal.exists_maximal_ideal_liesOver_of_isIntegral (R := 𝓞 ↥L) (S := 𝓞 K) q
    letI : Q.LiesOver q := hQlies
    have hQprime : Q.IsPrime := hQmax.isPrime
    -- `Q` is unramified over `𝓞 E`, because it does not divide `differentIdeal (𝓞 E) (𝓞 K)`
    have hQ1 : Q.ramificationIdx (𝓞 E) = 1 :=
      (Commons.NumberTheory.NumberField.ramificationIdx_one_iff_not_dvd_differentIdeal
        (E := E) (K := K) Q hQprime).mp (by
        rw [h]
        intro hcon
        exact hQmax.isPrime.ne_top (le_antisymm le_top (Ideal.dvd_iff_le.mp hcon)))
    -- multiplicativity of ramification indices in the tower `𝓞 E ⊆ 𝓞 ↥L ⊆ 𝓞 K`
    have htower := Ideal.ramificationIdx_tower (R := 𝓞 E) (S := 𝓞 ↥L) (T := 𝓞 K) q Q
    rw [hQ1] at htower
    have hq1 : q.ramificationIdx (𝓞 E) = 1 := Nat.eq_one_of_mul_eq_one_right htower.symm
    -- hence `q` does not divide the relative different of `L/E`
    exact (Commons.NumberTheory.NumberField.ramificationIdx_one_iff_not_dvd_differentIdeal
      (E := E) (K := ↥L) q hq).mpr hq1

end Work.ClassFieldTower
