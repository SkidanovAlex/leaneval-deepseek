import Mathlib
import Submission.NK.NUV2.localUnitLogShim

namespace NK.NUV2

/-- **The local unit logarithm at a finite place.**  For a number field `K` and a finite place
`v` there is `M ≥ 1` together with functions `exp`, `log` on the completion `K_v` which are
mutually inverse on the balls `{x | v x ≤ exp (-M)}` and `{y | v (y - 1) ≤ exp (-M)}`, and such
that on those balls the logarithm is additive (`log (y * z) = log y + log z`) and preserves the
valuation (`v (log y) = v (y - 1)`), while the exponential satisfies `v (exp x - 1) = v x`.

All clauses except the multiplicative one are direct conjuncts of
`Commons.Analysis.Nonarchimedean.exists_exp_log_adicCompletion_log_val_eq`; multiplicativity
follows from `exp (log y + log z) = exp (log y) * exp (log z) = y * z` together with
`log (exp w) = w` at `w = log y + log z` (which lies in the domain of `log ∘ exp` by the
nonarchimedean triangle inequality `Valuation.map_add_le`). -/
theorem localUnitLogStructure (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∃ M : ℕ, 1 ≤ M ∧ ∃ exp log : v.adicCompletion K → v.adicCompletion K,
      (∀ y : v.adicCompletion K,
        Valued.v (R := v.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) (y - 1) ≤
          (WithZero.exp (-(M : ℤ)) : WithZero (Multiplicative ℤ)) →
        Valued.v (R := v.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) (log y) =
          Valued.v (R := v.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) (y - 1)) ∧
      (∀ y z : v.adicCompletion K,
        Valued.v (R := v.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) (y - 1) ≤
          (WithZero.exp (-(M : ℤ)) : WithZero (Multiplicative ℤ)) →
        Valued.v (R := v.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) (z - 1) ≤
          (WithZero.exp (-(M : ℤ)) : WithZero (Multiplicative ℤ)) →
        log (y * z) = log y + log z) ∧
      (log 1 = 0) ∧
      (∀ x : v.adicCompletion K,
        Valued.v (R := v.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) x ≤
          (WithZero.exp (-(M : ℤ)) : WithZero (Multiplicative ℤ)) →
        log (exp x) = x) ∧
      (∀ x : v.adicCompletion K,
        Valued.v (R := v.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) x ≤
          (WithZero.exp (-(M : ℤ)) : WithZero (Multiplicative ℤ)) →
        Valued.v (R := v.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) (exp x - 1) =
          Valued.v (R := v.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) x) ∧
      (∀ y : v.adicCompletion K,
        Valued.v (R := v.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) (y - 1) ≤
          (WithZero.exp (-(M : ℤ)) : WithZero (Multiplicative ℤ)) →
        exp (log y) = y) := by
  obtain ⟨M, hM, exp, log, h₁, h₂, h₃, h₄, h₅, h₆⟩ :=
    Commons.Analysis.Nonarchimedean.exists_exp_log_adicCompletion_log_val_eq (K := K) v
  refine ⟨M, hM, exp, log, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `v (log y) = v (y - 1)`
    intro y hy
    exact (h₅ y hy).2.1
  · -- multiplicativity of `log`
    intro y z hy hz
    have hly := (h₅ y hy).1
    have hlz := (h₅ z hz).1
    have hsum : Valued.v (R := v.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (log y + log z) ≤ (WithZero.exp (-(M : ℤ)) : WithZero (Multiplicative ℤ)) :=
      Valuation.map_add_le (v := Valued.v) hly hlz
    have hexp : exp (log y + log z) = y * z := by
      rw [h₄ (log y) (log z) hly hlz, (h₅ y hy).2.2, (h₅ z hz).2.2]
    rw [← hexp, h₆ (log y + log z) hsum]
  · -- `log 1 = 0`
    have h0 : Valued.v (R := v.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (0 : v.adicCompletion K) ≤ (WithZero.exp (-(M : ℤ)) : WithZero (Multiplicative ℤ)) := by
      rw [Valuation.map_zero]
      exact zero_le
    rw [← h₃, h₆ (0 : v.adicCompletion K) h0]
  · -- `log (exp x) = x`
    intro x hx
    exact h₆ x hx
  · -- `v (exp x - 1) = v x`
    intro x hx
    exact h₂ x hx
  · -- `exp (log y) = y`
    intro y hy
    exact (h₅ y hy).2.2

end NK.NUV2
