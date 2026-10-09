import Mathlib
import Submission.Commons.NumberTheory.NumberField.Completion.val_adicCompletion_intCast_eq_padicValInt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open NumberField
open scoped WithZero

namespace Commons.NumberTheory.NumberField.Completion

/-- The valuation of the prime `p` in the `Q0`-adic completion of `ℚ` (for a height one
spectrum `Q0` whose prime ideal contains `p`) is `exp (-1)`. -/
theorem val_prime_adicCompletion_rat {p : ℕ} (hp : p.Prime)
    (Q0 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (hmem : (p : NumberField.RingOfIntegers ℚ) ∈ Q0.asIdeal) :
    Valued.v (R := Q0.adicCompletion ℚ) (Γ₀ := WithZero (Multiplicative ℤ))
      ((p : ℚ) : Q0.adicCompletion ℚ) = WithZero.exp (-1 : ℤ) := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hcast : ((p : ℤ) : ℚ) = (p : ℚ) := by simp
  have hval := val_adicCompletion_intCast_eq_padicValInt Q0 p hp hmem (p : ℤ) hp0
  rw [hcast] at hval
  rw [hval]
  rw [@padicValInt_self p ⟨hp⟩]
  norm_num

theorem exists_pow_mul_eq_int_adicCompletion_rat {p : ℕ} (hp : p.Prime)
    (Q0 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (hmem : (p : NumberField.RingOfIntegers ℚ) ∈ Q0.asIdeal)
    (c : Q0.adicCompletion ℚ) :
    ∃ m : ℕ, ∃ u : Q0.adicCompletionIntegers ℚ,
      c * (algebraMap (Q0.adicCompletionIntegers ℚ) (Q0.adicCompletion ℚ)
        (p : Q0.adicCompletionIntegers ℚ)) ^ m = (u : Q0.adicCompletion ℚ) := by
  by_cases hc : c = 0
  · exact ⟨0, 0, by simp [hc]⟩
  · have hvc : Valued.v (R := Q0.adicCompletion ℚ) (Γ₀ := WithZero (Multiplicative ℤ)) c ≠ 0 := by
      rw [Valuation.ne_zero_iff]
      exact hc
    set k : ℤ := WithZero.log (Valued.v (R := Q0.adicCompletion ℚ)
      (Γ₀ := WithZero (Multiplicative ℤ)) c) with hk
    have hck : Valued.v (R := Q0.adicCompletion ℚ) (Γ₀ := WithZero (Multiplicative ℤ)) c
        = WithZero.exp k := by
      rw [hk]
      exact (WithZero.exp_log hvc).symm
    have hπ : Valued.v (R := Q0.adicCompletion ℚ) (Γ₀ := WithZero (Multiplicative ℤ))
        (algebraMap (Q0.adicCompletionIntegers ℚ) (Q0.adicCompletion ℚ)
          (p : Q0.adicCompletionIntegers ℚ)) = WithZero.exp (-1 : ℤ) := by
      have hcoe : algebraMap (Q0.adicCompletionIntegers ℚ) (Q0.adicCompletion ℚ)
          (p : Q0.adicCompletionIntegers ℚ) = ((p : ℚ) : Q0.adicCompletion ℚ) := by
        change ((p : Q0.adicCompletionIntegers ℚ) : Q0.adicCompletion ℚ)
          = ((p : ℚ) : Q0.adicCompletion ℚ)
        have h1 : ((p : Q0.adicCompletionIntegers ℚ) : Q0.adicCompletion ℚ)
            = (p : Q0.adicCompletion ℚ) := by norm_cast
        rw [h1]
        have h2 : algebraMap ℚ (Q0.adicCompletion ℚ) (p : ℚ)
            = ((p : ℚ) : Q0.adicCompletion ℚ) := by simp
        rw [← h2]
        exact (map_natCast (algebraMap ℚ (Q0.adicCompletion ℚ)) p).symm
      rw [hcoe]
      exact val_prime_adicCompletion_rat hp Q0 hmem
    have hpow : (WithZero.exp (-1 : ℤ)) ^ k.natAbs = WithZero.exp (-(k.natAbs : ℤ)) := by
      rw [← WithZero.exp_nsmul]
      congr 1
      simp
    refine ⟨k.natAbs, ⟨c * (algebraMap (Q0.adicCompletionIntegers ℚ) (Q0.adicCompletion ℚ)
        (p : Q0.adicCompletionIntegers ℚ)) ^ k.natAbs, ?_⟩, rfl⟩
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    rw [map_mul, map_pow, hck, hπ, hpow, ← WithZero.exp_add]
    rw [← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr (by omega)

end Commons.NumberTheory.NumberField.Completion
