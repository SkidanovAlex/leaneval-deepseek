import Mathlib

namespace Work.DSREG.PrimeDimQuot

theorem exists_isPrime_ringKrullDim_quotient_eq (R : Type*) [CommRing R]
    (n : ℕ) (h : ringKrullDim R = n) :
    ∃ p : Ideal R, p.IsPrime ∧ ringKrullDim (R ⧸ p) = ringKrullDim R := by
  -- Pick a strictly increasing chain of primes of length `n`.
  obtain ⟨l, hl⟩ := (Order.le_krullDim_iff (α := PrimeSpectrum R)).mp h.ge
  refine ⟨l.head.asIdeal, l.head.2, ?_⟩
  -- The first element of that chain has coheight `n`, hence dimension `n`.
  have hcoheight : (↑(Order.coheight l.head) : WithBot ℕ∞) = ringKrullDim R := by
    refine le_antisymm (Order.coheight_le_krullDim l.head) ?_
    rw [h]
    have hc := WithBot.coe_le_coe.mpr (Order.length_le_coheight_head (p := l))
    rwa [WithBot.coe_natCast, hl] at hc
  -- The dimension of `R ⧸ p` is the coheight of `p`.
  have hdim : ringKrullDim (R ⧸ l.head.asIdeal) = (↑(Order.coheight l.head) : WithBot ℕ∞) := by
    rw [ringKrullDim, Order.krullDim_eq_of_orderIso
      (Ideal.primeSpectrumQuotientOrderIsoZeroLocus (R := R) l.head.asIdeal)]
    have hset : PrimeSpectrum.zeroLocus (R := R) (l.head.asIdeal : Set R) = Set.Ici l.head := by
      ext x
      simp only [PrimeSpectrum.mem_zeroLocus, Set.mem_Ici]
      exact PrimeSpectrum.asIdeal_le_asIdeal l.head x
    rw [hset]
    exact (Order.coheight_eq_krullDim_Ici l.head).symm
  exact hdim.trans hcoheight

end Work.DSREG.PrimeDimQuot
