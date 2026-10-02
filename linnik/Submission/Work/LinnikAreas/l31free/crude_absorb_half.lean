import Mathlib
import Submission.Commons.Analysis.Real.log_pow_le_mul_rpow

set_option autoImplicit false

namespace Work.LinnikAreas.l31free

/-- For `σ ≥ 1` with `σ ≤ 1 + loglog N / log N`, the crude factor `1 + log N` is dominated by
`C_ε · N^((1/2)(1-σ)(1+1/k) + ε)`: the `σ ≥ 1` half of the `φ = 1/2` L-function bound.
`Commons.Analysis.Real.log_pow_le_mul_rpow` (importable as
`Submission.Commons.Analysis.Real.log_pow_le_mul_rpow`) gives `(log x)^A ≤ C x^ε'`; the existing
proof of `Commons.NumberTheory.DirichletCharacter.crude_absorb` in
`Submission/Commons/NumberTheory/DirichletCharacter/LFunction_bound_third_of_burgess.lean`
adapts verbatim, replacing the exponent `(1+1/k)/3` by `(1+1/k)/2` (the argument only uses
`1 - σ + loglog N / log N ≥ 0`, `e ≥ 0` and `e ≤ 2`). -/
lemma crude_absorb_half {k : ℕ} (hk : 3 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ Cf : ℝ, 0 < Cf ∧ ∀ (N : ℕ), 1 ≤ N → ∀ σ : ℝ, 1 ≤ σ →
      σ ≤ 1 + Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ) →
      (1 + Real.log (N:ℝ)) ≤
        Cf * (N:ℝ) ^ (((1:ℝ)/2) * (1-σ) * (1 + 1/(k:ℝ)) + ε) := by
  obtain ⟨Cl, hClpos, hCl⟩ := Commons.Analysis.Real.log_pow_le_mul_rpow hε 3
  have hkR : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
  have hk3 : (3:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  refine ⟨8*(1+Cl) + 8, by positivity, ?_⟩
  intro q hq1 σ hσge hσle
  rcases eq_or_lt_of_le hq1 with hq | hq
  · subst hq
    simp only [Nat.cast_one, Real.log_one, Real.one_rpow, mul_one]
    linarith only [hClpos]
  have hqR1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast (le_of_lt hq)
  have hqRpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hlogq0 : (0:ℝ) ≤ Real.log (q:ℝ) := Real.log_nonneg hqR1
  have hlogqpos : 0 < Real.log (q:ℝ) := Real.log_pos (by exact_mod_cast hq)
  have hqe1 : (1:ℝ) ≤ (q:ℝ)^ε := Real.one_le_rpow hqR1 (le_of_lt hε)
  set e : ℝ := (1:ℝ)/2 + 1/(2*(k:ℝ)) with hedef
  have hepos : 0 < e := by rw [hedef]; positivity
  have hee : (1+1/(k:ℝ))/2 = e := by rw [hedef]; ring
  have hsq : (1 + Real.log (q:ℝ))^3 ≤ (8*(1+Cl)+8) * (q:ℝ)^ε := by
    have h1 : (Real.log (q:ℝ))^3 ≤ Cl * (q:ℝ)^ε := hCl (q:ℝ) hqR1
    have h2 : (1:ℝ) ≤ 1 + Real.log (q:ℝ) := by linarith only [hlogqpos]
    have h3 : (1 + Real.log (q:ℝ))^3
        = 1 + 3*Real.log (q:ℝ) + 3*(Real.log (q:ℝ))^2 + (Real.log (q:ℝ))^3 := by ring
    have h4 : 3*Real.log (q:ℝ) + 3*(Real.log (q:ℝ))^2 ≤ 3 + 6*(Real.log (q:ℝ))^2 := by
      linarith only [hlogq0, h2, pow_nonneg hlogq0 2, sq_nonneg (Real.log (q:ℝ) - 1), hlogqpos]
    nlinarith only [h1, h4, hlogq0, hqe1, hClpos, Real.rpow_nonneg (by positivity) ε,
      pow_nonneg hlogq0 2]
  have hloge : (Real.log (q:ℝ))^e ≤ (1 + Real.log (q:ℝ))^(2:ℕ) := by
    have h1 : (Real.log (q:ℝ))^e ≤ (1 + Real.log (q:ℝ))^e :=
      Real.rpow_le_rpow hlogq0 (by linarith only []) (le_of_lt hepos)
    have h2 : e ≤ 2 := by
      rw [hedef]
      have h : 1/(2*(k:ℝ)) ≤ 1/6 :=
        one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 6) (by linarith only [hk3])
      linarith only [h]
    have h3 : (1 + Real.log (q:ℝ))^e ≤ (1 + Real.log (q:ℝ))^((2:ℕ):ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_right (Real.log_nonneg hqR1)) h2
    exact h1.trans (by simpa only [Real.rpow_natCast] using h3)
  have hprod : (1 + Real.log (q:ℝ)) * (Real.log (q:ℝ))^e ≤ (8*(1+Cl)+8) * (q:ℝ)^ε := by
    calc (1 + Real.log (q:ℝ)) * (Real.log (q:ℝ))^e
        ≤ (1 + Real.log (q:ℝ)) * (1 + Real.log (q:ℝ))^2 :=
          mul_le_mul_of_nonneg_left hloge (by linarith only [hlogqpos])
      _ = (1 + Real.log (q:ℝ))^3 := by ring
      _ ≤ (8*(1+Cl)+8) * (q:ℝ)^ε := hsq
  set L : ℝ := Real.log (Real.log (q:ℝ))/Real.log (q:ℝ) with hLdef
  have hexp_eq : Real.log (q:ℝ) = (q:ℝ)^L := by
    rw [hLdef, Real.rpow_def_of_pos hqRpos]
    rw [show Real.log (q:ℝ) * (Real.log (Real.log (q:ℝ))/Real.log (q:ℝ))
        = Real.log (Real.log (q:ℝ)) by field_simp]
    exact (Real.exp_log hlogqpos).symm
  have hlogeq : (q:ℝ)^(e * L) = (Real.log (q:ℝ))^e := by
    conv_rhs => rw [hexp_eq, ← Real.rpow_mul (le_of_lt hqRpos)]
    rw [mul_comm]
  have hqe : (q:ℝ)^ε ≤ (q:ℝ)^(((1:ℝ)/2)*(1-σ)*(1+1/(k:ℝ)) + ε) * (Real.log (q:ℝ))^e := by
    rw [← hlogeq, ← Real.rpow_add hqRpos]
    apply Real.rpow_le_rpow_of_exponent_le hqR1
    have h1 : (1:ℝ) - σ + Real.log (Real.log (q:ℝ))/Real.log (q:ℝ) ≥ 0 := by linarith only [hσle]
    have h2 := mul_le_mul_of_nonneg_left h1 (show (0:ℝ) ≤ 1+1/(k:ℝ) by positivity)
    rw [← hee]
    linarith only [h2]
  have hloge_pos : 0 < (Real.log (q:ℝ))^e := Real.rpow_pos_of_pos hlogqpos e
  have hfinal : (1 + Real.log (q:ℝ))
      ≤ (8*(1+Cl)+8) * (q:ℝ)^(((1:ℝ)/2)*(1-σ)*(1+1/(k:ℝ)) + ε) := by
    have h1 : (1 + Real.log (q:ℝ)) * (Real.log (q:ℝ))^e
        ≤ ((8*(1+Cl)+8) * (q:ℝ)^(((1:ℝ)/2)*(1-σ)*(1+1/(k:ℝ)) + ε)) * (Real.log (q:ℝ))^e := by
      calc (1 + Real.log (q:ℝ)) * (Real.log (q:ℝ))^e
          ≤ (8*(1+Cl)+8) * (q:ℝ)^ε := hprod
        _ ≤ (8*(1+Cl)+8) * ((q:ℝ)^(((1:ℝ)/2)*(1-σ)*(1+1/(k:ℝ)) + ε)
              * (Real.log (q:ℝ))^e) :=
            mul_le_mul_of_nonneg_left hqe (by positivity)
        _ = ((8*(1+Cl)+8) * (q:ℝ)^(((1:ℝ)/2)*(1-σ)*(1+1/(k:ℝ)) + ε))
              * (Real.log (q:ℝ))^e := by ring
    exact le_of_mul_le_mul_right h1 hloge_pos
  exact hfinal

end Work.LinnikAreas.l31free
