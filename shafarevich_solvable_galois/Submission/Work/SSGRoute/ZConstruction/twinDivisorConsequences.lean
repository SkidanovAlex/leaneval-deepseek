import Mathlib
import Submission.Work.SSGRoute.PinnedTwin.divisorRepresentative
import Submission.Work.SSGRoute.NodeS37.coprimeOfPrimeRepresentative
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZConstruction

open scoped Classical

set_option linter.unusedSectionVars false

/-- The `count` of a height-one prime, regarded as a fractional ideal, at a place `P`: it is `1` at
`𝔮` itself and `0` everywhere else. -/
private lemma count_asIdeal_eq {K : Type} [Field K] [NumberField K]
    (𝔮 P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    FractionalIdeal.count K P
        ((𝔮.asIdeal : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K))
      = (if P = 𝔮 then (1 : ℤ) else 0) := by
  by_cases h : P = 𝔮
  · rw [h, if_pos rfl, FractionalIdeal.count_self]
  · rw [if_neg h, FractionalIdeal.count_maximal_coprime K P (fun hh => h hh.symm)]

/-- `spanSingleton` does not see the sign of its generator. -/
private lemma spanSingleton_neg {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (x : K) :
    FractionalIdeal.spanSingleton (nonZeroDivisors R) (-x)
      = FractionalIdeal.spanSingleton (nonZeroDivisors R) x := by
  rw [FractionalIdeal.spanSingleton_eq_spanSingleton]
  exact ⟨-1, by simp [Units.smul_def]⟩

theorem twinDivisorConsequences {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (t : K ≃ₐ[k] K) (ht2 : t ^ 2 = 1)
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (z : Kˣ)
    (hne : Commons.NumberTheory.NumberField.Completion.placeSmul t 𝔮 ≠ 𝔮)
    (hQ'fix : Commons.NumberTheory.NumberField.Completion.placeSmul t Q' ≠ Q')
    (hQ'miss : Q' ≠ Commons.NumberTheory.NumberField.Completion.placeSmul t 𝔮)
    (hdiv : ∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      FractionalIdeal.count K P (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers K)) (z : K))
        = FractionalIdeal.count K P
            ((𝔮.asIdeal : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K))
          + 2 * FractionalIdeal.count K P
            ((Q'.asIdeal : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K))) :
    ((z : K) - t (z : K) ≠ 0) ∧
    ((z : K) + t (z : K) ≠ 0) ∧
    (∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      FractionalIdeal.count K P (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers K)) (z : K)) ≠ 0 →
      FractionalIdeal.count K
        (Commons.NumberTheory.NumberField.Completion.placeSmul t P)
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
          (z : K)) = 0) := by
  classical
  -- `placeSmul t` is an involution
  have htss : ∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      Commons.NumberTheory.NumberField.Completion.placeSmul t
        (Commons.NumberTheory.NumberField.Completion.placeSmul t P) = P := by
    intro P
    rw [← Commons.NumberTheory.NumberField.Completion.placeSmul_mul, ← pow_two, ht2,
      Commons.NumberTheory.NumberField.Completion.placeSmul_one]
  -- the divisor of `z` is `𝔮 · Q'²`
  have hcount : ∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      FractionalIdeal.count K P (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers K)) (z : K))
      = (if P = 𝔮 then (1 : ℤ) else 0)
        + 2 * (if P = Q' then (1 : ℤ) else 0) := by
    intro P
    rw [hdiv P, count_asIdeal_eq (K := K) 𝔮 P, count_asIdeal_eq (K := K) Q' P]
  -- `𝔮` lies in the support of `z`
  have hzq_ne : FractionalIdeal.count K 𝔮 (FractionalIdeal.spanSingleton
      (nonZeroDivisors (NumberField.RingOfIntegers K)) (z : K)) ≠ 0 := by
    rw [hcount 𝔮, if_pos rfl]
    by_cases h : 𝔮 = Q'
    · rw [if_pos h]; norm_num
    · rw [if_neg h]; norm_num
  -- the translates of `𝔮` and `Q'` are outside the support of `z`
  have htmq : FractionalIdeal.count K
      (Commons.NumberTheory.NumberField.Completion.placeSmul t 𝔮)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
        (z : K)) = 0 := by
    rw [hcount (Commons.NumberTheory.NumberField.Completion.placeSmul t 𝔮), if_neg hne,
      if_neg (fun h => hQ'miss h.symm)]
    norm_num
  have htQ'eq : FractionalIdeal.count K
      (Commons.NumberTheory.NumberField.Completion.placeSmul t Q')
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
        (z : K)) = 0 := by
    have hQ'ne : Commons.NumberTheory.NumberField.Completion.placeSmul t Q' ≠ 𝔮 := by
      intro h
      have h' := congrArg (Commons.NumberTheory.NumberField.Completion.placeSmul t) h
      rw [htss Q'] at h'
      exact hQ'miss h'
    rw [hcount (Commons.NumberTheory.NumberField.Completion.placeSmul t Q'), if_neg hQ'ne,
      if_neg hQ'fix]
    norm_num
  -- consequently the support of the divisor of `z` is contained in `{𝔮, Q'}`
  have hsupport : ∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      FractionalIdeal.count K P (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers K)) (z : K)) ≠ 0 →
      P = 𝔮 ∨ P = Q' := by
    intro P hP
    rw [hcount P] at hP
    by_cases h1 : P = 𝔮
    · exact Or.inl h1
    · refine Or.inr ?_
      by_contra h2
      rw [if_neg h1, if_neg h2] at hP
      norm_num at hP
  -- Galois equivariance: the `𝔮`-count of `t z` is the `t𝔮`-count of `z`, hence `0`
  have htz_count : FractionalIdeal.count K 𝔮
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
        (t (z : K))) = 0 := by
    have h := Work.SSGRoute.NodeS37.count_placeSmul_eq_count t z
      (Commons.NumberTheory.NumberField.Completion.placeSmul t 𝔮)
    rw [show ((Units.map t.toRingEquiv.toMonoidHom z : Kˣ) : K) = t (z : K) from rfl,
      htss 𝔮, htmq] at h
    exact h
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have h1 : t (z : K) = (z : K) := (sub_eq_zero.mp h).symm
    rw [h1] at htz_count
    exact hzq_ne htz_count
  · intro h
    have h1 : t (z : K) = -(z : K) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact h
    rw [h1, spanSingleton_neg] at htz_count
    exact hzq_ne htz_count
  · intro P hP
    rcases hsupport P hP with h | h
    · rw [h]; exact htmq
    · rw [h]; exact htQ'eq

end Work.SSGRoute.ZConstruction
