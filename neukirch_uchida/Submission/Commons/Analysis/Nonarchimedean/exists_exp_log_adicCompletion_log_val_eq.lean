import Mathlib
import Submission.Commons.Analysis.Nonarchimedean.exists_exp_log_adicCompletion

namespace Commons.Analysis.Nonarchimedean

/-- The missing clause `v (log y) = v (y - 1)` on the logarithm's domain, derived in three
lines from the already published `Commons.Analysis.Nonarchimedean.exists_exp_log_adicCompletion`
(whose existential supplies `M`, `exp`, `log`, the identity `Valued.v (exp x - 1) = Valued.v x`
on `v x ≤ exp (-M)`, the identity `exp (log y) = y` on `v (y - 1) ≤ exp (-M)`, and the bound
`Valued.v (log y) ≤ exp (-M)` on that same domain): for `y` with `v (y - 1) ≤ exp (-M)` the bound
on `log y` puts `log y` in the domain of the first identity, so
`v (y - 1) = v (exp (log y) - 1) = v (log y)`. -/
theorem exists_exp_log_adicCompletion_log_val_eq {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∃ M : ℕ, 1 ≤ M ∧ ∃ exp log : v.adicCompletion K → v.adicCompletion K,
      (∀ x : v.adicCompletion K,
        Valued.v (R := v.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) x ≤
            (WithZero.exp (-(M : ℤ)) : WithZero (Multiplicative ℤ)) →
          HasSum (fun n : ℕ => x ^ n / ((n.factorial : ℕ) : v.adicCompletion K)) (exp x)) ∧
      (∀ x : v.adicCompletion K,
        Valued.v (R := v.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) x ≤
            (WithZero.exp (-(M : ℤ)) : WithZero (Multiplicative ℤ)) →
          Valued.v (R := v.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) (exp x - 1) =
            Valued.v (R := v.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) x) ∧
      (exp 0 = 1) ∧
      (∀ x y : v.adicCompletion K,
        Valued.v (R := v.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) x ≤
            (WithZero.exp (-(M : ℤ)) : WithZero (Multiplicative ℤ)) →
        Valued.v (R := v.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) y ≤
            (WithZero.exp (-(M : ℤ)) : WithZero (Multiplicative ℤ)) →
          exp (x + y) = exp x * exp y) ∧
      (∀ y : v.adicCompletion K,
        Valued.v (R := v.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) (y - 1) ≤
            (WithZero.exp (-(M : ℤ)) : WithZero (Multiplicative ℤ)) →
          Valued.v (R := v.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) (log y) ≤
            (WithZero.exp (-(M : ℤ)) : WithZero (Multiplicative ℤ)) ∧
          Valued.v (R := v.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) (log y) =
            Valued.v (R := v.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) (y - 1) ∧
          exp (log y) = y) ∧
      (∀ x : v.adicCompletion K,
        Valued.v (R := v.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) x ≤
            (WithZero.exp (-(M : ℤ)) : WithZero (Multiplicative ℤ)) →
          log (exp x) = x) := by
  obtain ⟨M₀, exp, log, h₁, h₂, h₃, h₄, h₅, h₆⟩ :=
    exists_exp_log_adicCompletion (K := K) v
  -- Enlarge the radius parameter so that it is at least `1`; this shrinks the domain
  -- `v ≤ exp (-M)`, so every property transports.
  refine ⟨max M₀ 1, le_max_right _ _, exp, log, ?_, ?_, h₃, ?_, ?_, ?_⟩
  · -- HasSum
    intro x hx
    exact h₁ x (le_trans hx (WithZero.exp_le_exp.mpr (neg_le_neg (by exact_mod_cast le_max_left M₀ 1))))
  · -- valuation of `exp x - 1`
    intro x hx
    exact h₂ x (le_trans hx (WithZero.exp_le_exp.mpr (neg_le_neg (by exact_mod_cast le_max_left M₀ 1))))
  · -- additivity
    intro x y hx hy
    exact h₄ x y
      (le_trans hx (WithZero.exp_le_exp.mpr (neg_le_neg (by exact_mod_cast le_max_left M₀ 1))))
      (le_trans hy (WithZero.exp_le_exp.mpr (neg_le_neg (by exact_mod_cast le_max_left M₀ 1))))
  · -- logarithm: bound, the missing valuation identity, and the splitting identity
    intro y hy
    have hy₀ : Valued.v (y - 1) ≤ (WithZero.exp (-(M₀ : ℤ)) : WithZero (Multiplicative ℤ)) :=
      le_trans hy (WithZero.exp_le_exp.mpr (neg_le_neg (by exact_mod_cast le_max_left M₀ 1)))
    obtain ⟨hlog_le, hlog_exp⟩ := h₅ y hy₀
    -- `log y` lies in the domain of the first identity, and `exp (log y) = y`.
    have hval := h₂ (log y) hlog_le
    rw [hlog_exp] at hval
    exact ⟨by rw [hval.symm]; exact hy, hval.symm, hlog_exp⟩
  · -- `log (exp x) = x`
    intro x hx
    exact h₆ x (le_trans hx (WithZero.exp_le_exp.mpr (neg_le_neg (by exact_mod_cast le_max_left M₀ 1))))

end Commons.Analysis.Nonarchimedean
