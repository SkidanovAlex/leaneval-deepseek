import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.NodeS37.coprimeOfPrimeRepresentative
import Submission.Work.SSGRoute.PinnedTwin.primeInClassNotFixed
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.exists_coprime_representative_two
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PinnedTwin

open scoped Classical

/-- **The ideal class of `A` is represented by a prime `Q'`.**  Reading-off of the count form of
`Q'.asIdeal = A * (y)` needed by the divisor arithmetic: the `𝔭`-count of the principal prime `Q'`
is `1` at `Q'` and `0` elsewhere, and the count is additive over products of fractional ideals. -/
theorem count_eq_of_asIdeal_eq_mul {K : Type} [Field K] [NumberField K]
    (A : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) (hA : A ≠ 0)
    (Q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (y : Kˣ)
    (hy : ((Q'.asIdeal : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)
        = A * FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
            (y : K))) :
    ∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
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

theorem coprimeRepresentative {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
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
  classical
  -- The square root of the divisor of `b`: `count_P(b) = [P = 𝔮] + 2 * count_P(A)`.
  obtain ⟨A, hAne, hcount⟩ :=
    Work.SSGRoute.ZDataTwo.TwoRec.exists_fractionalIdeal_count_eq b 𝔮 heven hodd
  -- Čebotarev: a prime `Q'` in the ideal class of `A`, not `ρ`-fixed and different from `ρ𝔮`.
  obtain ⟨Q', y, hfix, hmiss, hyIdeal⟩ := primeInClassNotFixed ρ hρ2 A hAne 𝔮 hne
  refine ⟨b * y ^ 2, y, rfl, ?_⟩
  -- The divisor arithmetic: `z = b y²` has `count_P(z) = [P = 𝔮] + 2 * [P = Q']`.
  exact Work.SSGRoute.NodeS37.coprimeOfPrimeRepresentative ρ hρ2 b y 𝔮 Q' A
    hcount (count_eq_of_asIdeal_eq_mul A hAne Q' y hyIdeal) hfix hne hmiss

end Work.SSGRoute.PinnedTwin
