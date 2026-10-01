import Mathlib
import Submission.Work.LinnikAreas.Density4.thetaDiag_eval_defs

/-!
# Termwise lower bound for the diagonal majorant `tdH`

For `2 ≤ n ≤ ⌊e^{M-2}⌋` one has

  `(6/7) * ((M - 1 - log n)/n) ≤ (M - 1 - log n) * tdH σ A n`,

where `tdH σ A n = n^{σ-1} e^{-n/A}`, `σ > 0` and `A ≥ e^M`.

Since `log n ≤ M - 2` the factor `M - 1 - log n` is positive, and since
`n/A ≤ e^{M-2}/e^M = e^{-2}` we have `e^{-n/A} ≥ e^{-e^{-2}} ≥ 1 - e^{-2} ≥ 6/7`
(using `e^2 ≥ 7`).  Together with `n^σ ≥ 1` this gives `n^{σ-1} e^{-n/A} ≥ (6/7)/n`,
and multiplying by the positive factor `M - 1 - log n` yields the claim.
-/

open scoped BigOperators
noncomputable section

namespace Work.LinnikAreas.Density4

/-- `e^{-2} ≤ 1/7`, i.e. `7 ≤ e^2`. -/
private lemma exp_neg_two_le_seventh : Real.exp (-2) ≤ 1/7 := by
  have h7 : (7:ℝ) ≤ Real.exp 2 := by
    have h1 : (2.7182818283:ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have h2 : Real.exp 2 = (Real.exp 1)^2 := by
      rw [show (2:ℝ) = 1+1 by norm_num, Real.exp_add]; ring
    rw [h2]
    nlinarith [Real.exp_pos 1, sq_nonneg (Real.exp 1 - 2.7182818283)]
  have h := (inv_le_inv₀ (Real.exp_pos 2) (by norm_num : (0:ℝ) < 7)).mpr h7
  rw [Real.exp_neg]
  simpa using h

theorem tdH_termwise_ge (M σ A : ℝ) (hM : 15000 ≤ M) (hσ : 0 < σ) (hA : Real.exp M ≤ A) :
    ∀ n ∈ Finset.Icc 2 ⌊Real.exp (M-2)⌋₊,
      (6/7) * ((M - 1 - Real.log (n:ℝ)) / (n:ℝ))
        ≤ (M - 1 - Real.log (n:ℝ)) * Work.LinnikAreas.Density4.tdH σ A n := by
  intro n hn
  have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnN : n ≤ ⌊Real.exp (M-2)⌋₊ := (Finset.mem_Icc.mp hn).2
  have hn0 : 0 < n := by omega
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast hn0
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hApos : 0 < A := lt_of_lt_of_le (Real.exp_pos M) hA
  have hM2 : (2:ℝ) ≤ M := by linarith
  -- `log n ≤ M - 2`
  have hnle : (n:ℝ) ≤ Real.exp (M-2) := by
    have h1 : (n:ℝ) ≤ (⌊Real.exp (M-2)⌋₊ : ℝ) := by exact_mod_cast hnN
    have h2 : (⌊Real.exp (M-2)⌋₊ : ℝ) ≤ Real.exp (M-2) :=
      Nat.floor_le (le_of_lt (Real.exp_pos _))
    linarith
  have hlog : Real.log (n:ℝ) ≤ M - 2 :=
    (Real.log_le_iff_le_exp hnpos).mpr hnle
  have hc : (0:ℝ) ≤ M - 1 - Real.log (n:ℝ) := by linarith
  -- `n/A ≤ e^{-2}`
  have hnA : (n:ℝ)/A ≤ Real.exp (-2) := by
    have h2 : Real.exp M * Real.exp (-2) = Real.exp (M-2) := by
      rw [Real.exp_neg, Real.exp_sub]; ring
    have h1 : (n:ℝ) ≤ A * Real.exp (-2) := by
      have h3 : Real.exp M * Real.exp (-2) ≤ A * Real.exp (-2) :=
        mul_le_mul_of_nonneg_right hA (le_of_lt (Real.exp_pos _))
      linarith
    calc (n:ℝ)/A ≤ (A * Real.exp (-2))/A := div_le_div_of_nonneg_right h1 (le_of_lt hApos)
      _ = Real.exp (-2) := by field_simp
  -- `6/7 ≤ e^{-n/A}`
  have hexp : (6/7:ℝ) ≤ Real.exp (-(n:ℝ)/A) := by
    have hbase : (6/7:ℝ) ≤ Real.exp (-(Real.exp (-2))) := by
      have h := Real.add_one_le_exp (-(Real.exp (-2)))
      have h7 := exp_neg_two_le_seventh
      linarith
    have hmono : Real.exp (-(Real.exp (-2))) ≤ Real.exp (-(n:ℝ)/A) := by
      rw [show -(n:ℝ)/A = -((n:ℝ)/A) by ring]
      exact Real.exp_le_exp.mpr (neg_le_neg hnA)
    linarith
  have hpow : (1:ℝ) ≤ (n:ℝ)^σ := Real.one_le_rpow hn1 (le_of_lt hσ)
  have hkey : (6/7:ℝ) ≤ (n:ℝ)^σ * Real.exp (-(n:ℝ)/A) := by
    calc (6/7:ℝ) ≤ Real.exp (-(n:ℝ)/A) := hexp
      _ = 1 * Real.exp (-(n:ℝ)/A) := by ring
      _ ≤ (n:ℝ)^σ * Real.exp (-(n:ℝ)/A) :=
          mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)
  -- `n^{σ-1} = n^σ / n`
  have hsplit : (n:ℝ)^(σ-1) = (n:ℝ)^σ / (n:ℝ) := by
    have h := Real.rpow_add hnpos (σ-1) 1
    rw [Real.rpow_one] at h
    have hσ' : σ - 1 + 1 = σ := by ring
    rw [hσ'] at h
    rw [eq_div_iff (ne_of_gt hnpos)]
    exact h.symm
  have htdH : tdH σ A n = ((n:ℝ)^σ * Real.exp (-(n:ℝ)/A)) / (n:ℝ) := by
    rw [tdH, hsplit]; ring
  rw [htdH]
  have hdiv : (6/7:ℝ)/(n:ℝ) ≤ ((n:ℝ)^σ * Real.exp (-(n:ℝ)/A))/(n:ℝ) :=
    div_le_div_of_nonneg_right hkey (le_of_lt hnpos)
  have hfin := mul_le_mul_of_nonneg_left hdiv hc
  calc (6/7) * ((M - 1 - Real.log (n:ℝ)) / (n:ℝ))
      = (M - 1 - Real.log (n:ℝ)) * ((6/7)/(n:ℝ)) := by ring
    _ ≤ (M - 1 - Real.log (n:ℝ)) * (((n:ℝ)^σ * Real.exp (-(n:ℝ)/A))/(n:ℝ)) := hfin

end Work.LinnikAreas.Density4
