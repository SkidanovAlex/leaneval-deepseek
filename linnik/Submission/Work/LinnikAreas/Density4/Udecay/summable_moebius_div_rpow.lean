import Mathlib

namespace Work.LinnikAreas.Density4.Udecay

/-- The Dirichlet series `Σ_n μ(n)/n^{1+s}` converges absolutely for `s > 0`.
Bound `|μ n| ≤ 1` and compare with the `p`-series `Σ (n^{1+s})⁻¹` (`1 + s > 1`,
`Real.summable_nat_rpow_inv`). -/
theorem summable_moebius_div_rpow {s : ℝ} (hs : 0 < s) :
    Summable (fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ (1 + s : ℝ)) := by
  have h1 : (1:ℝ) < 1 + s := by linarith
  have hseries : Summable (fun n : ℕ => ((n:ℝ)^(1+s))⁻¹) :=
    (Real.summable_nat_rpow_inv (p := 1+s)).2 h1
  refine Summable.of_norm_bounded hseries (fun n => ?_)
  rw [Real.norm_eq_abs, abs_div]
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    have hz : (0:ℝ) ^ (1+s) = 0 := Real.zero_rpow (by linarith : (1+s:ℝ) ≠ 0)
    simp [hz]
  · have hnpos : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hpos : (0:ℝ) < (n:ℝ)^(1+s) := Real.rpow_pos_of_pos hnpos _
    rw [abs_of_pos hpos, div_le_iff₀ hpos, inv_mul_cancel₀ (ne_of_gt hpos)]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)

end Work.LinnikAreas.Density4.Udecay
