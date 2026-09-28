import Mathlib

namespace Work.HP.MDEstimates

open MeasureTheory Set

/-- Tail bound for the `p`-series: for `s > 1` and `N ≥ 1`,
`∑_{j≥0} 1/(j + N + 1)^s ≤ N^{1-s}/(s-1)`, obtained by comparison with the
integral `∫_N^∞ x^{-s} dx = N^{1-s}/(s-1)`. -/
theorem pSeries_tail_tsum_le (s : ℝ) (hs : 1 < s) (N : ℕ) (hN : 1 ≤ N) :
    ∑' j : ℕ, 1 / ((j + N + 1 : ℕ) : ℝ) ^ s ≤ (N : ℝ) ^ (1 - s) / (s - 1) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  -- the function `x ↦ x^{-s}` is antitone on `[N, ∞)`
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-s)) (Ici (N : ℝ)) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (show -s ≤ 0 by linarith)).mono (by
      intro x hx
      exact lt_of_lt_of_le hNpos hx)
  -- it is integrable on `(N, ∞)` since the exponent is `< -1`
  have hint : IntegrableOn (fun x : ℝ => x ^ (-s)) (Ioi (N : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hNpos
  have hnonneg : ∀ t ∈ Ioi (N : ℝ), 0 ≤ t ^ (-s) := by
    intro t ht
    exact Real.rpow_nonneg (le_of_lt (lt_trans hNpos (mem_Ioi.mp ht))) _
  -- integral test for antitone functions
  have key := hanti.tsum_comp_add_le_integral N hint hnonneg
  -- identify the summands with `x ^ (-s)`
  have hL : (∑' j : ℕ, 1 / ((j + N + 1 : ℕ) : ℝ) ^ s)
      = ∑' n : ℕ, ((n + N + 1 : ℕ) : ℝ) ^ (-s) := by
    apply tsum_congr
    intro n
    have hpos : (0 : ℝ) ≤ ((n + N + 1 : ℕ) : ℝ) := by positivity
    rw [one_div, ← Real.rpow_neg hpos]
  -- evaluate the improper integral
  have hR : (∫ x in Ioi (N : ℝ), x ^ (-s)) = (N : ℝ) ^ (1 - s) / (s - 1) := by
    rw [integral_Ioi_rpow_of_lt (a := -s) (c := (N : ℝ)) (by linarith) hNpos]
    rw [show (-s + 1 : ℝ) = 1 - s by ring, show (1 : ℝ) - s = -(s - 1) by ring]
    rw [neg_div_neg_eq]
  rw [hL]
  exact le_trans key (le_of_eq hR)

end Work.HP.MDEstimates
