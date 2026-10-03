import Mathlib

namespace Work.Pert.pert2v2

/-- Elementary bound: `log x ≤ 2 √x` for `x ≥ 1`.
Proof: `log √x ≤ √x - 1 ≤ √x` and `log √x = log x / 2`. -/
theorem log_le_two_sqrt : ∀ {x : ℝ}, 1 ≤ x → Real.log x ≤ 2 * Real.sqrt x := by
  intro x hx
  have hx0 : 0 < x := by linarith
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := Real.log_le_sub_one_of_pos hs
  have h2 : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt (le_of_lt hx0)
  have h3 : Real.log x / 2 ≤ Real.sqrt x := by linarith [Real.sqrt_nonneg x]
  linarith

/-- For every `K ≥ 0`, `L`, `Ξ` there is a threshold `N > 0` such that
`2 K log (x+1) + (2 L + Ξ) < x` for all `x ≥ N`.  The linear growth of `x` beats the
logarithmic growth of `log (x+1)`. -/
theorem threshold_arith (K L Ξ : ℝ) (hK : 0 ≤ K) :
    ∃ N : ℝ, 0 < N ∧ ∀ x : ℝ, N ≤ x → 2 * K * Real.log (x + 1) + (2 * L + Ξ) < x := by
  refine ⟨(4 * Real.sqrt 2 * K + 1 + |2 * L + Ξ|) ^ 2 + 1, by positivity, ?_⟩
  intro x hx
  set B : ℝ := 4 * Real.sqrt 2 * K + 1 + |2 * L + Ξ| with hB
  have habs : 0 ≤ |2 * L + Ξ| := abs_nonneg _
  have h4K : 0 ≤ 4 * Real.sqrt 2 * K := by positivity
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hN1 : 1 ≤ B ^ 2 + 1 := by nlinarith [sq_nonneg B]
  have hx1 : 1 ≤ x := le_trans hN1 hx
  have hx0 : 0 < x := by linarith
  have hsqrtN : B ≤ Real.sqrt (B ^ 2 + 1) := (Real.le_sqrt hB0 (by positivity)).mpr (by nlinarith)
  have hBx : B ≤ Real.sqrt x := le_trans hsqrtN (Real.sqrt_le_sqrt hx)
  have hlog : Real.log (x + 1) ≤ 2 * Real.sqrt (x + 1) := log_le_two_sqrt (by linarith)
  have hs2 : Real.sqrt (x + 1) ≤ Real.sqrt (2 * x) := Real.sqrt_le_sqrt (by linarith)
  have h2x : Real.sqrt (2 * x) = Real.sqrt 2 * Real.sqrt x := Real.sqrt_mul (by norm_num) x
  have hlog' : Real.log (x + 1) ≤ 2 * (Real.sqrt 2 * Real.sqrt x) := by rw [h2x] at hs2; linarith
  have hmul : 2 * K * Real.log (x + 1) ≤ 4 * Real.sqrt 2 * K * Real.sqrt x := by
    have h := mul_le_mul_of_nonneg_left hlog' (by linarith : (0:ℝ) ≤ 2 * K)
    nlinarith [h]
  have hkey : 4 * Real.sqrt 2 * K * Real.sqrt x + (2 * L + Ξ) < x := by
    have hu0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
    have husq : Real.sqrt x ^ 2 = x := Real.sq_sqrt (le_of_lt hx0)
    have hB1 : 1 ≤ B := by rw [hB]; linarith
    have hu1 : 1 ≤ Real.sqrt x := le_trans hB1 hBx
    have hdiff : 1 + |2 * L + Ξ| ≤ Real.sqrt x - 4 * Real.sqrt 2 * K := by
      rw [hB] at hBx; linarith
    have hprod : (1 : ℝ) * (1 + |2 * L + Ξ|) ≤ Real.sqrt x * (Real.sqrt x - 4 * Real.sqrt 2 * K) :=
      mul_le_mul hu1 hdiff (by positivity) hu0
    have hCabs : 2 * L + Ξ ≤ |2 * L + Ξ| := le_abs_self _
    have : (2 * L + Ξ) < Real.sqrt x * (Real.sqrt x - 4 * Real.sqrt 2 * K) := by linarith
    nlinarith [this, husq]
  linarith

theorem deep_arith {K L Ξ : ℝ} (hK : 0 ≤ K) :
    ∃ N : ℝ, 0 < N ∧ ∀ t s c : ℝ, N ≤ t → 0 ≤ s → 0 ≤ c →
      c ≤ K * Real.log (t + s + 1) + L → 2 * c + Ξ < t + s := by
  obtain ⟨N, hNpos, hN⟩ := threshold_arith K L Ξ hK
  refine ⟨N, hNpos, ?_⟩
  intro t s c ht hs hc hcle
  have hx := hN (t + s) (by linarith)
  have h2 : 2 * c + Ξ ≤ 2 * (K * Real.log (t + s + 1) + L) + Ξ := by linarith
  linarith

end Work.Pert.pert2v2
