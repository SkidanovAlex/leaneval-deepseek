import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.KrullDimension.Polynomial
import Submission.Commons.Algebra.MvPolynomial.exists_isHomogeneous_one_notMem_minimalPrimes

namespace Commons.Algebra.MvPolynomial

theorem height_idealOfVars (n : ℕ) :
    (MvPolynomial.idealOfVars (Fin n) ℂ).height = (n : ℕ∞) := by
  haveI : (MvPolynomial.idealOfVars (Fin n) ℂ).IsPrime := by
    rw [← Commons.Algebra.MvPolynomial.ker_aeval_zero_eq_idealOfVars n]
    exact RingHom.ker_isPrime _
  refine le_antisymm ?_ ?_
  · have h := Ideal.height_le_ringKrullDim_of_isPrime
      (R := MvPolynomial (Fin n) ℂ) (I := MvPolynomial.idealOfVars (Fin n) ℂ)
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      zero_add] at h
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at h
    exact WithBot.coe_le_coe.mp h
  · exact Commons.Algebra.MvPolynomial.idealOfVars_le_height _ le_rfl

end Commons.Algebra.MvPolynomial