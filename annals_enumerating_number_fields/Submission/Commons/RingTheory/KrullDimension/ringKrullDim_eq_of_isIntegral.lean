import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Ideal.HasGoingUp

namespace Commons.RingTheory.KrullDimension

open Ideal

/-- An injective integral extension of commutative rings preserves Krull dimension. -/
theorem ringKrullDim_eq_of_isIntegral {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] (h : Function.Injective (algebraMap A B)) :
    ringKrullDim B = ringKrullDim A := by
  -- The contraction of primes is strictly monotone, giving `dim B ≤ dim A`.
  have hstrict : StrictMono (PrimeSpectrum.comap (algebraMap A B)) := by
    intro p q hpq
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal] at hpq ⊢
    rw [PrimeSpectrum.comap_asIdeal, PrimeSpectrum.comap_asIdeal]
    exact Ideal.IsIntegral.comap_lt_comap hpq
  have hBA : ringKrullDim B ≤ ringKrullDim A :=
    Order.krullDim_le_of_strictMono _ hstrict
  -- Going-up lifts every chain of primes of `A` to one in `B`, giving `dim A ≤ dim B`.
  have hker : Ideal.comap (algebraMap A B) (⊥ : Ideal B) = ⊥ := by
    rw [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).mp h]
  have hAB : ringKrullDim A ≤ ringKrullDim B := by
    unfold ringKrullDim Order.krullDim
    apply iSup_le
    intro p
    have hmem : Ideal.comap (algebraMap A B) (⊥ : Ideal B) ≤ (RelSeries.head p).asIdeal := by
      rw [hker]; exact bot_le
    obtain ⟨Q, -, hQprime, hQcomap⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral (R := A) (S := B)
        (RelSeries.head p).asIdeal ⊥ hmem
    obtain ⟨L, hLlen, -, -⟩ :=
      @Ideal.exists_ltSeries_of_hasGoingUp A B _ _ _ _ p Q hQprime
        (Ideal.LiesOver.mk hQcomap.symm)
    rw [← hLlen]
    exact le_iSup (fun q : LTSeries (PrimeSpectrum B) => (q.length : WithBot ℕ∞)) L
  exact le_antisymm hBA hAB

end Commons.RingTheory.KrullDimension