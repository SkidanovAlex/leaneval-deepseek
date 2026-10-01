import Mathlib

namespace Work.LinnikAreas.Density4

/-- Harmonic sum bound: `Σ_{A ≤ n ≤ B} 1/(n+1) ≤ log((B+1)/A)` for `1 ≤ A ≤ B + 1`
(per-term `1/(n+1) ≤ log((n+1)/n)`, then telescope). -/
theorem sum_one_div_succ_le_log {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B + 1) :
    ∑ n ∈ Finset.Icc A B, (1:ℝ)/((n:ℝ) + 1) ≤ Real.log (((B:ℝ) + 1)/(A:ℝ)) := by
  -- Rewrite the range as a half-open interval so that the telescoping lemma applies.
  have hIco : Finset.Icc A B = Finset.Ico A (B + 1) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  -- Per-term bound: `1/(n+1) ≤ log(n+1) - log n`.
  have hterm : ∀ n ∈ Finset.Ico A (B + 1),
      (1:ℝ)/((n:ℝ) + 1) ≤ Real.log (((n+1 : ℕ):ℝ)) - Real.log ((n:ℝ)) := by
    intro n hn
    have hnA : A ≤ n := (Finset.mem_Ico.mp hn).1
    have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast le_trans hA hnA
    have hn0 : (n:ℝ) ≠ 0 := by linarith
    have hn10 : (n:ℝ) + 1 ≠ 0 := by linarith
    push_cast
    -- `1 - ((n+1)/n)⁻¹ ≤ log((n+1)/n)` and `1 - ((n+1)/n)⁻¹ = 1/(n+1)`.
    have hpos : (0:ℝ) < ((n:ℝ)+1)/(n:ℝ) := by positivity
    have h := Real.one_sub_inv_le_log_of_pos hpos
    have hkey : (1:ℝ) - (((n:ℝ)+1)/(n:ℝ))⁻¹ = (1:ℝ)/((n:ℝ)+1) := by
      rw [inv_div]; field_simp; ring
    rw [hkey] at h
    rw [← Real.log_div hn10 hn0]
    exact h
  rw [hIco]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  -- Telescoping: `Σ_{A ≤ n ≤ B} (log(n+1) - log n) = log(B+1) - log A`.
  rw [Finset.sum_Ico_sub (fun k => Real.log ((k:ℝ))) hAB]
  push_cast
  rw [← Real.log_div (by positivity) (by positivity)]

end Work.LinnikAreas.Density4
