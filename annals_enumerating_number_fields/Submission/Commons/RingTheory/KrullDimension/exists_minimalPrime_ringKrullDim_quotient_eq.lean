import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

namespace Commons.RingTheory.KrullDimension

/-- For any commutative ring `A` of Krull dimension `d`, there is a minimal prime `p` of `A`
such that the quotient `A ⧸ p` again has Krull dimension `d`. -/
theorem exists_minimalPrimes_ringKrullDim_eq {A : Type*} [CommRing A]
    {d : ℕ} (hd : ringKrullDim A = (d : WithBot ℕ∞)) :
    ∃ p ∈ minimalPrimes A, ringKrullDim (A ⧸ p) = (d : WithBot ℕ∞) := by
  -- A strict chain of `d + 1` primes of `A`.
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.mp (le_of_eq hd.symm)
  -- Extend the chain downwards to a minimal prime `q` below its head.
  obtain ⟨q, hqmem, hqle⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := l.head.asIdeal) bot_le
  -- Every prime of the chain lies above `q`, so the chain sits in `zeroLocus q`.
  have hmem : ∀ i, (l i) ∈ PrimeSpectrum.zeroLocus (R := A) q := by
    intro i
    rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
    exact le_trans hqle (by simpa using LTSeries.head_le l i)
  -- Push the chain into the closed set `zeroLocus q`.
  let l' : LTSeries (PrimeSpectrum.zeroLocus (R := A) q) :=
    LTSeries.mk l.length (fun i => ⟨l i, hmem i⟩) (fun i j hij => by
      rw [Subtype.mk_lt_mk]; exact l.strictMono hij)
  have hlow : (d : WithBot ℕ∞) ≤ Order.krullDim (PrimeSpectrum.zeroLocus (R := A) q) := by
    rw [← hl]
    exact Order.le_krullDim_iff.mpr ⟨l', rfl⟩
  have hqdim_le : ringKrullDim (A ⧸ q) ≤ (d : WithBot ℕ∞) := by
    rw [← hd]; exact ringKrullDim_quotient_le q
  have hqdim_ge : (d : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ q) := by
    rw [ringKrullDim_quotient q]; exact hlow
  exact ⟨q, hqmem, le_antisymm hqdim_le hqdim_ge⟩

theorem exists_minimalPrime_ringKrullDim_quotient_eq {R : Type*} [CommRing R]
    (q : Ideal R) (d : ℕ) (hd : ringKrullDim (R ⧸ q) = (d : WithBot ℕ∞)) :
    ∃ p ∈ q.minimalPrimes, ringKrullDim (R ⧸ p) = (d : WithBot ℕ∞) := by
  obtain ⟨p', hp'mem, hp'dim⟩ :=
    exists_minimalPrimes_ringKrullDim_eq (A := R ⧸ q) hd
  refine ⟨p'.comap (Ideal.Quotient.mk q), ?_, ?_⟩
  · rw [Ideal.minimalPrimes_eq_comap]
    exact ⟨p', hp'mem, rfl⟩
  · have hqp : q ≤ p'.comap (Ideal.Quotient.mk q) := by
      intro x hx
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact p'.zero_mem
    have hmap : (p'.comap (Ideal.Quotient.mk q)).map (Ideal.Quotient.mk q) = p' :=
      Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective p'
    have he : ((R ⧸ q) ⧸ p') ≃+* (R ⧸ p'.comap (Ideal.Quotient.mk q)) :=
      (Ideal.quotEquivOfEq hmap).symm.trans (DoubleQuot.quotQuotEquivQuotOfLE hqp)
    rw [← RingEquiv.ringKrullDim he]
    exact hp'dim

end Commons.RingTheory.KrullDimension