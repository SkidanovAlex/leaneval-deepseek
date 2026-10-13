/-
  Ported (mechanically) from the lead-supplied reuse file
  `sources/reuse/ours/annals_van_der_waerden_conjecture/Submission/Commons/RingTheory/Ideal/card_minimalPrimes_quotient_le_univ.lean`
  section `mission.Commons.RingTheory.KrullDimension.ringKrullDim_eq_of_isIntegral` (piece 0).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Data.Finsupp.PWO
import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Star
import Mathlib.Data.Sym.NatCard
import Mathlib.GroupTheory.CosetCover
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Polynomial.HilbertPoly
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Submission.Work.WilE2.BzPort.P13

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option warn.classDefReducibility false



set_option autoImplicit true

-- ==== from Submission.Commons.RingTheory.KrullDimension.ringKrullDim_eq_of_isIntegral ====
section

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
end


