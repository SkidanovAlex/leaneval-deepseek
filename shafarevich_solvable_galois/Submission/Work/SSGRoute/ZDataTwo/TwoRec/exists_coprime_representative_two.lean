import Mathlib.RingTheory.Henselian
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.exists_prime_in_class_not_fixed
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A representative `z = b·y²` coprime to its `ρ`-conjugate

`Work.SSGRoute.ZDataTwo.TwoRec.exists_coprime_representative_two`: the *representative
normalisation* step of Schmidt--Wingberg's p. 16 computation (see
`ACTION_claimOfPreTwo_p16_carve_session39.md` §7).  Given a finite Galois extension `k ⊆ K`, an
involution `ρ ∈ Gal(K/k)`, `b ∈ Kˣ` whose divisor is `𝔮 · A²` (odd at `𝔮`, even elsewhere) and
`ρ𝔮 ≠ 𝔮`, there is `y ∈ Kˣ` with `z := b·y²` whose divisor is *coprime to its `ρ`-conjugate*
(`supp(z) ∩ supp(ρ z) = ∅`) and misses `ρ𝔮`.

## Structure

Write `div(b) = 𝔮 + 2·div(A)` (`exists_fractionalIdeal_count_eq`), with `A` the fractional ideal
whose divisor is `(div b − 𝔮)/2`.  The normalisation is then provided by the Čebotarev input
`exists_prime_in_class_not_fixed`: a prime `Q'` in the ideal class of `A` (i.e. `(Q') = A·(y)`)
which is not `ρ`-fixed and is not `ρ𝔮`.  For such a `Q'` the divisor of `z := b·y²` is `𝔮·Q'²`
(`Work.SSGRoute.NodeS37.count_mul_sq_of_classRepresentative`), and since the support `{𝔮, Q'}` is
`ρ`-disjoint and misses `ρ𝔮`, the two displayed clauses follow.
-/

namespace Work.SSGRoute.ZDataTwo.TwoRec

open NumberField IsDedekindDomain
open scoped nonZeroDivisors Classical

/-- The involution `ρ` acting twice on primes is the identity. -/
theorem placeSmul_placeSmul {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (ρ : K ≃ₐ[k] K) (hρ2 : ρ ^ 2 = 1)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Commons.NumberTheory.NumberField.Completion.placeSmul ρ
        (Commons.NumberTheory.NumberField.Completion.placeSmul ρ Q) = Q := by
  have hsq : ρ * ρ = 1 := by simpa [pow_two] using hρ2
  rw [← Commons.NumberTheory.NumberField.Completion.placeSmul_mul, hsq,
    Commons.NumberTheory.NumberField.Completion.placeSmul_one]

/-- **The square root of the divisor of `b`.**  If `v_P(b)` is even for every `P ≠ 𝔮` and odd at
`𝔮`, there is a fractional ideal `A` with
`v_P(b) = [P = 𝔮] + 2·v_P(A)` for every prime `P`; explicitly `A = ∏_P P^{(v_P(b) − [P = 𝔮])/2}`. -/
theorem exists_fractionalIdeal_count_eq {K : Type} [Field K] [NumberField K]
    (b : Kˣ)
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (heven : ∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K), P ≠ 𝔮 →
      Even (FractionalIdeal.count K P (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers K)) (b : K))))
    (hodd : Odd (FractionalIdeal.count K 𝔮 (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers K)) (b : K)))) :
    ∃ A : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K,
      A ≠ 0 ∧ ∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        FractionalIdeal.count K P (FractionalIdeal.spanSingleton
          (nonZeroDivisors (NumberField.RingOfIntegers K)) (b : K))
        = (if P = 𝔮 then 1 else 0) + 2 * FractionalIdeal.count K P A := by
  classical
  set f : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → ℤ :=
    fun P => (FractionalIdeal.count K P (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers K)) (b : K))
      - (if P = 𝔮 then 1 else 0)) / 2 with hf
  have hfsupp : ∀ᶠ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)
      in Filter.cofinite, f P = 0 := by
    have h1 : ∀ᶠ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)
        in Filter.cofinite,
        FractionalIdeal.count K P (FractionalIdeal.spanSingleton
          (nonZeroDivisors (NumberField.RingOfIntegers K)) (b : K)) = 0 :=
      FractionalIdeal.finite_factors _
    refine h1.mono fun P hP => ?_
    by_cases h : P = 𝔮
    · -- impossible: the `𝔮`-count of `b` is odd, hence nonzero
      exfalso
      have hqz : FractionalIdeal.count K 𝔮 (FractionalIdeal.spanSingleton
          (nonZeroDivisors (NumberField.RingOfIntegers K)) (b : K)) = 0 := by
        rw [← h]; exact hP
      rw [hqz] at hodd
      obtain ⟨r, hr⟩ := hodd
      omega
    · rw [hf]
      simp only
      rw [if_neg h, hP]
      norm_num
  refine ⟨∏ᶠ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      ((P.asIdeal : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) ^ (f P)),
    ?_, ?_⟩
  · refine finprod_ne_zero fun P => zpow_ne_zero _ ?_
    exact FractionalIdeal.coeIdeal_ne_zero.mpr P.ne_bot
  · intro P
    rw [FractionalIdeal.count_finprod (K := K) P f hfsupp]
    have hff : f P = (FractionalIdeal.count K P (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers K)) (b : K))
        - (if P = 𝔮 then 1 else 0)) / 2 := by rw [hf]
    rw [hff]
    -- the defining identity of `f`
    have hdvd : (2 : ℤ) ∣ (FractionalIdeal.count K P (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers K)) (b : K)) - (if P = 𝔮 then 1 else 0)) := by
      by_cases h : P = 𝔮
      · rw [if_pos h, h]
        obtain ⟨r, hr⟩ := hodd
        exact ⟨r, by rw [hr]; ring⟩
      · rw [if_neg h, sub_zero]
        exact (even_iff_two_dvd.mp (heven P h))
    have hkey : ((FractionalIdeal.count K P (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers K)) (b : K))
        - (if P = 𝔮 then 1 else 0)) / 2) * 2
        = FractionalIdeal.count K P (FractionalIdeal.spanSingleton
          (nonZeroDivisors (NumberField.RingOfIntegers K)) (b : K))
        - (if P = 𝔮 then 1 else 0) := Int.ediv_mul_cancel hdvd
    have h2 : 2 * ((FractionalIdeal.count K P (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers K)) (b : K))
        - (if P = 𝔮 then 1 else 0)) / 2)
        = FractionalIdeal.count K P (FractionalIdeal.spanSingleton
          (nonZeroDivisors (NumberField.RingOfIntegers K)) (b : K))
        - (if P = 𝔮 then 1 else 0) := by rw [mul_comm]; exact hkey
    linarith [h2]


/-- **From a prime in the class of `A` to the coprimality normalisation.**  If `div(b) = 𝔮 + 2·div A`
and `Q' = A·(y)` is not `ρ`-fixed and differs from `ρ𝔮`, then `z := b·y²` satisfies the two
conditions of the normalisation. -/
theorem count_mul_sq_of_prime_in_class {k K : Type} [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (ρ : K ≃ₐ[k] K) (hρ2 : ρ ^ 2 = 1) (b : Kˣ)
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (A : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) (hA : A ≠ 0)
    (hb : ∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      FractionalIdeal.count K P (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers K)) (b : K))
      = (if P = 𝔮 then 1 else 0) + 2 * FractionalIdeal.count K P A)
    (Q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (y : Kˣ)
    (hy : ((Q'.asIdeal : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)
        = A * FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
            (y : K)))
    (hfix : Commons.NumberTheory.NumberField.Completion.placeSmul ρ Q' ≠ Q')
    (hmiss : Q' ≠ Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮)
    (hne : Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮 ≠ 𝔮) :
    ∃ z : Kˣ, z = b * y ^ 2 ∧
      (∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        FractionalIdeal.count K P (FractionalIdeal.spanSingleton
          (nonZeroDivisors (NumberField.RingOfIntegers K)) (z : K)) ≠ 0 →
        FractionalIdeal.count K (Commons.NumberTheory.NumberField.Completion.placeSmul ρ P)
          (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
            (z : K)) = 0) ∧
      FractionalIdeal.count K (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮)
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
          (z : K)) = 0 := by
  classical
  -- the count form of `(Q') = A·(y)`
  have hy' : ∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      FractionalIdeal.count K P A
        + FractionalIdeal.count K P (FractionalIdeal.spanSingleton
            (nonZeroDivisors (NumberField.RingOfIntegers K)) (y : K))
      = (if P = Q' then 1 else 0) := by
    intro P
    have hyl : FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
        (y : K) ≠ 0 :=
      FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Units.ne_zero y)
    have h1 : FractionalIdeal.count K P (A * FractionalIdeal.spanSingleton
          (nonZeroDivisors (NumberField.RingOfIntegers K)) (y : K))
        = FractionalIdeal.count K P A
          + FractionalIdeal.count K P (FractionalIdeal.spanSingleton
              (nonZeroDivisors (NumberField.RingOfIntegers K)) (y : K)) :=
      FractionalIdeal.count_mul K P hA hyl
    have h2 : FractionalIdeal.count K P
          ((Q'.asIdeal : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K))
        = (if P = Q' then 1 else 0) := by
      have := FractionalIdeal.count_maximal (R := NumberField.RingOfIntegers K) (K := K) P Q'
      simpa [eq_comm] using this
    rw [← h1, ← hy]; exact h2
  have hcount : ∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      FractionalIdeal.count K P (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers K)) (((b * y ^ 2 : Kˣ) : K)))
      = (if P = 𝔮 then 1 else 0) + 2 * (if P = Q' then 1 else 0) :=
    Work.SSGRoute.NodeS37.count_mul_sq_of_classRepresentative 𝔮 Q' A b y hb hy'
  -- `ρ`-consequences used below
  have hρQ'ne : Commons.NumberTheory.NumberField.Completion.placeSmul ρ Q' ≠ Q' := hfix
  have hρQ'ne𝔮 : Commons.NumberTheory.NumberField.Completion.placeSmul ρ Q' ≠ 𝔮 := by
    intro h
    have h2 : (Commons.NumberTheory.NumberField.Completion.placeSmul ρ)
        (Commons.NumberTheory.NumberField.Completion.placeSmul ρ Q') =
        Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮 := by rw [h]
    rw [placeSmul_placeSmul ρ hρ2 Q'] at h2
    exact hmiss h2
  have hρ𝔮neQ' : Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮 ≠ Q' := fun h => hmiss h.symm
  refine ⟨b * y ^ 2, rfl, ?_, ?_⟩
  · intro P hP
    have key : P = 𝔮 ∨ P = Q' := by
      by_contra hcon
      push_neg at hcon
      exact hP (by rw [hcount P, if_neg hcon.1, if_neg hcon.2]; norm_num)
    rw [hcount (Commons.NumberTheory.NumberField.Completion.placeSmul ρ P)]
    rcases key with rfl | rfl
    · rw [if_neg hne, if_neg hρ𝔮neQ']; norm_num
    · rw [if_neg hρQ'ne𝔮, if_neg hρQ'ne]; norm_num
  · rw [hcount (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮), if_neg hne,
      if_neg hρ𝔮neQ']; norm_num

theorem exists_coprime_representative_two {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (ρ : K ≃ₐ[k] K) (hρ2 : ρ ^ 2 = 1) (b : Kˣ)
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (heven : ∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K), P ≠ 𝔮 →
      Even (FractionalIdeal.count K P (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers K)) (b : K))))
    (hodd : Odd (FractionalIdeal.count K 𝔮 (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers K)) (b : K))))
    (hne : Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮 ≠ 𝔮) :
    ∃ z y : Kˣ, z = b * y ^ 2 ∧
      (∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        FractionalIdeal.count K P (FractionalIdeal.spanSingleton
          (nonZeroDivisors (NumberField.RingOfIntegers K)) (z : K)) ≠ 0 →
        FractionalIdeal.count K (Commons.NumberTheory.NumberField.Completion.placeSmul ρ P)
          (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
            (z : K)) = 0) ∧
      FractionalIdeal.count K (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮)
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
          (z : K)) = 0 := by
  obtain ⟨A, hAne, hcount⟩ := exists_fractionalIdeal_count_eq b 𝔮 heven hodd
  obtain ⟨Q', y, hfix, hmiss, hy⟩ := exists_prime_in_class_not_fixed ρ hρ2 A hAne 𝔮 hne
  obtain ⟨z, hz, hconj, hzero⟩ :=
    count_mul_sq_of_prime_in_class ρ hρ2 b 𝔮 A hAne hcount Q' y hy hfix hmiss hne
  exact ⟨z, y, hz, hconj, hzero⟩

end Work.SSGRoute.ZDataTwo.TwoRec
