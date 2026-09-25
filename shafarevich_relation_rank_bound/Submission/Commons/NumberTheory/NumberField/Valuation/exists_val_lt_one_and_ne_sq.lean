import Mathlib
import Submission.Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime
import Submission.Commons.NumberTheory.NumberField.ringOfIntegers_le_of_ne_top

namespace Commons.NumberTheory.NumberField.Valuation

open IsDedekindDomain WithZero

/-- Pulling back a valuation subring along a ring homomorphism corresponds to pulling back the
associated valuation. -/
private lemma comap_valuationSubring {K K' : Type*} [Field K] [Field K']
    (f : K →+* K') (A : ValuationSubring K') :
    (Valuation.comap f A.valuation).valuationSubring = A.comap f := by
  ext x
  rw [Valuation.mem_valuationSubring_iff, ValuationSubring.mem_comap,
    ← ValuationSubring.valuation_le_one_iff, Valuation.comap_apply]

/-- In `ℤᵐ⁰`, the element `exp (-1)` is not a square. -/
private lemma exp_neg_one_ne_sq (y : ℤᵐ⁰) : y ^ 2 ≠ exp (-1 : ℤ) := by
  intro h
  have hy : y ≠ 0 := by
    intro hy0
    rw [hy0, zero_pow (by norm_num)] at h
    exact WithZero.coe_ne_zero h.symm
  have h2 : (y ^ 2).log = (exp (-1 : ℤ)).log := by rw [h]
  rw [log_pow, log_exp, nsmul_eq_mul] at h2
  omega

theorem exists_val_lt_one_and_ne_sq {K K' : Type*} [Field K] [NumberField K] [Field K']
    [Algebra K K'] (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') ≠ ⊤) :
    ∃ π : K, A.valuation (algebraMap K K' π) < 1 ∧
      ∀ c : K, A.valuation (algebraMap K K' π) ≠ A.valuation ((algebraMap K K' c) ^ 2) := by
  classical
  -- The comap `A.comap (algebraMap K K')` is a proper valuation subring of the number
  -- field `K`, hence the valuation ring of a finite place `P` of `K`.
  obtain ⟨P, hP⟩ := Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime
    (A.comap (algebraMap K K')) hA
    (Commons.NumberTheory.NumberField.ringOfIntegers_le_of_valuationSubring
      (A.comap (algebraMap K K')))
  -- The `P`-adic valuation of `K`.
  let w : Valuation K ℤᵐ⁰ := IsDedekindDomain.HeightOneSpectrum.valuation K P
  have hwsub : w.valuationSubring = A.comap (algebraMap K K') := by
    rw [show w = IsDedekindDomain.HeightOneSpectrum.valuation K P from rfl, hP]
    exact (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring P).symm
  -- The valuation induced on `K` by `A`.
  let u : Valuation K A.ValueGroup := Valuation.comap (algebraMap K K') A.valuation
  have husub : u.valuationSubring = A.comap (algebraMap K K') :=
    comap_valuationSubring (algebraMap K K') A
  -- `u` and `w` have the same valuation subring, hence are equivalent.
  have heq : u.IsEquiv w :=
    (Valuation.isEquiv_iff_valuationSubring u w).mpr (by rw [husub, hwsub])
  -- A uniformizer of the `P`-adic valuation.
  obtain ⟨π, hπ⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer K P
  have hpi : A.valuation (algebraMap K K' π) = u π :=
    (Valuation.comap_apply (algebraMap K K') A.valuation π).symm
  refine ⟨π, ?_, ?_⟩
  · rw [hpi, heq.lt_one_iff_lt_one, hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  · intro c
    have hc : A.valuation ((algebraMap K K' c) ^ 2) = u (c ^ 2) := by
      rw [Valuation.comap_apply]
      exact congrArg A.valuation (map_pow (algebraMap K K') c 2).symm
    rw [hpi, hc]
    intro h
    have hw : w π = w (c ^ 2) := (heq.eq_iff).mp h
    rw [hπ, Valuation.map_pow] at hw
    exact exp_neg_one_ne_sq (w c) hw.symm

end Commons.NumberTheory.NumberField.Valuation
