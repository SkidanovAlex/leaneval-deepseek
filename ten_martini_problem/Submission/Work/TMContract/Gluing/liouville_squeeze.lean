import Mathlib
set_option linter.unusedVariables false

namespace Work.TMContract.Gluing

/-- Numerical contradiction: an exponentially squeezed lower bound of the form
`c₀ e^{-ε q} λ^{q/2} ≤ 2 K e^{-b q}` cannot hold for arbitrarily large `q` when
`λ > e^{-2b + 2ε}`, `c₀ > 0`, `λ > 0`, `ε > 0` and `K ≥ 0`. -/
theorem liouville_squeeze {c₀ lam b ε K : ℝ} (hc₀ : 0 < c₀) (hlam : 0 < lam)
    (hε : 0 < ε) (hb : Real.exp (-(2 * b) + 2 * ε) < lam) (hK : 0 ≤ K)
    (h : ∃ᶠ q : ℕ in Filter.atTop,
      c₀ * Real.exp (-(ε * q)) * lam ^ ((q : ℝ) / 2) ≤ 2 * K * Real.exp (-(b * q))) : False := by
  -- The logarithmic slope of the comparison `λ^{q/2}` against `e^{-bq}` is positive.
  have hα : 0 < Real.log lam / 2 + b - ε := by
    have h1 : -(2 * b) + 2 * ε < Real.log lam := by
      have h2 := Real.log_lt_log (Real.exp_pos (-(2 * b) + 2 * ε)) hb
      rwa [Real.log_exp] at h2
    linarith
  by_cases hK0 : K = 0
  · -- With `K = 0` the right-hand side is `0`, while the left-hand side is positive.
    rw [hK0] at h
    apply (Filter.not_frequently.mpr ?_) h
    apply Filter.Eventually.of_forall
    intro q hle
    have hpos : 0 < c₀ * Real.exp (-(ε * (q : ℝ))) * lam ^ ((q : ℝ) / 2) := by positivity
    simp only [mul_zero, zero_mul] at hle
    linarith
  · -- `K > 0`: taking logarithms of the inequality bounds `q` uniformly.
    have hKpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hK0)
    have hbound : ∀ q : ℕ,
        (c₀ * Real.exp (-(ε * q)) * lam ^ ((q : ℝ) / 2) ≤ 2 * K * Real.exp (-(b * q))) →
        (q : ℝ) * (Real.log lam / 2 + b - ε) ≤ Real.log (2 * K) - Real.log c₀ := by
      intro q hPq
      have hLpos : 0 < c₀ * Real.exp (-(ε * (q : ℝ))) * lam ^ ((q : ℝ) / 2) := by positivity
      have hlog := Real.log_le_log hLpos hPq
      have hlogL : Real.log (c₀ * Real.exp (-(ε * (q : ℝ))) * lam ^ ((q : ℝ) / 2))
          = Real.log c₀ + (-(ε * (q : ℝ))) + (q : ℝ) / 2 * Real.log lam := by
        rw [Real.log_mul (by positivity) (by positivity),
            Real.log_mul (by positivity) (by positivity),
            Real.log_exp, Real.log_rpow hlam]
      have hlogR : Real.log (2 * K * Real.exp (-(b * (q : ℝ))))
          = Real.log (2 * K) + (-(b * (q : ℝ))) := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_exp]
      rw [hlogL, hlogR] at hlog
      nlinarith [hlog]
    -- Choose `N` larger than the uniform bound `β/α`.
    obtain ⟨N, hN⟩ : ∃ N : ℕ,
        (Real.log (2 * K) - Real.log c₀) / (Real.log lam / 2 + b - ε) < (N : ℝ) :=
      exists_nat_gt _
    -- Extract a squeezed index `q ≥ N`, whose bound contradicts `q ≥ N`.
    obtain ⟨q, hNq, hPq⟩ := (Filter.frequently_atTop.mp h) N
    have hbnd := hbound q hPq
    have hqle : (q : ℝ) ≤ (Real.log (2 * K) - Real.log c₀) / (Real.log lam / 2 + b - ε) := by
      rw [le_div_iff₀ hα]
      linarith
    have hNq' : (N : ℝ) ≤ (q : ℝ) := by exact_mod_cast hNq
    linarith

end Work.TMContract.Gluing
