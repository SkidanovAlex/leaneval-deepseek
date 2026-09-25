import Mathlib
import Submission.Work.RHContract.Corpus

namespace Work.RHContract.Identity.PsiErr

open Filter

/-- `ψ x − x = O(x)`, quantitatively: `|ψ x − x| ≤ (log 4 + 4) * x`.  This is Chebyshev's
elementary upper bound `ψ x ≤ (log 4 + 4) x` together with `ψ x ≥ 0`. -/
private lemma abs_psi_sub_self_le (x : ℝ) (hx : 0 ≤ x) :
    |Chebyshev.psi x - x| ≤ (Real.log 4 + 4) * x := by
  have hC : (1 : ℝ) ≤ Real.log 4 + 4 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    linarith
  have hpsi_le : Chebyshev.psi x ≤ (Real.log 4 + 4) * x :=
    Chebyshev.psi_le_const_mul_self hx
  have hpsi_nn : 0 ≤ Chebyshev.psi x := Chebyshev.psi_nonneg x
  rw [abs_sub_le_iff]
  exact ⟨by nlinarith, by nlinarith⟩

/-- The Chebyshev bounds `0 ≤ ψ x ≤ (log 4 + 4) x` give `(ψ x − x) / (x log x) → 0`:
the quotient is `O(1/log x)` and `log x → ∞`. -/
theorem psi_sub_id_div_mul_log_tendsto_zero :
    Filter.Tendsto (fun x : ℝ => (Chebyshev.psi x - x) / (x * Real.log x)) Filter.atTop (nhds 0) := by
  refine squeeze_zero_norm' ?_ (Filter.Tendsto.const_div_atTop Real.tendsto_log_atTop (Real.log 4 + 4))
  filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hden : 0 < x * Real.log x := mul_pos hx0 hlog
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hden]
  calc |Chebyshev.psi x - x| / (x * Real.log x)
      ≤ ((Real.log 4 + 4) * x) / (x * Real.log x) :=
        div_le_div_of_nonneg_right (abs_psi_sub_self_le x (le_of_lt hx0)) (le_of_lt hden)
    _ = (Real.log 4 + 4) / Real.log x := by
        rw [mul_comm (Real.log 4 + 4) x, mul_div_mul_left _ _ (ne_of_gt hx0)]

end Work.RHContract.Identity.PsiErr
