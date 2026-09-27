import Mathlib
import Submission.Work.Mostow.LinAlgMatrixIneqAux

/-!
# Sharp bound on `matF` in dimension three with a small coordinate

For `x : Fin 3 → ℝ` with `0 ≤ x i < 1`, `∑ i, x i = 1`, and some coordinate
`x i ≤ δ` with `0 < δ ≤ 1/8`, we prove

`matF x ≤ 1 / (2 * (1 - δ))`.

The proof is the elementary AM–GM estimate.  Writing `a, b, c` for the three
coordinates and assuming the *first* is the small one (`a ≤ δ`), the key
identity is

`(1 - b) * (1 - c) = a + b * c`   (because `a + b + c = 1`),

and the AM–GM inequality

`2 * √(a * (b * c)) ≤ a + b * c`.

Hence

`(1 - a) * (1 - b) * (1 - c) = (1 - a) * (a + b * c)
   ≥ (1 - a) * 2 * √(a * b * c) ≥ 2 * (1 - δ) * √(a * b * c)`,

which is exactly `matF x ≤ 1 / (2 * (1 - δ))` after clearing the (positive)
denominator.  The bound is sharp: at `δ = 1/8` it is attained by
`(a, b, c) = (1/8, (7+√17)/16, (7-√17)/16)`.
-/

namespace Work.Mostow

open Real

/-- The symmetric AM–GM core: for `a, b, c ≥ 0` summing to `1`, each `< 1`, and
`a ≤ δ` with `0 < δ ≤ 1/8`, `√a √b √c / ((1-a)(1-b)(1-c)) ≤ 1/(2(1-δ))`. -/
private lemma matF_three_aux (a b c δ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (ha1 : a < 1) (hb1 : b < 1) (hc1 : c < 1)
    (hsum : a + b + c = 1) (hδ : 0 < δ) (hδle : δ ≤ 1 / 8) (haδ : a ≤ δ) :
    Real.sqrt a * Real.sqrt b * Real.sqrt c / ((1 - a) * (1 - b) * (1 - c))
      ≤ 1 / (2 * (1 - δ)) := by
  have hbc : 0 ≤ b * c := mul_nonneg hb hc
  have h1a : 0 < 1 - a := by linarith
  have h1b : 0 < 1 - b := by linarith
  have h1c : 0 < 1 - c := by linarith
  have h1δ : 0 < 1 - δ := by linarith
  have hD : 0 < (1 - a) * (1 - b) * (1 - c) := by positivity
  -- `1 - b - c = a`
  have hid : (1 - b) * (1 - c) = a + b * c := by nlinarith [hsum]
  -- AM–GM for the pair `(a, b * c)`
  have hamgm : 2 * Real.sqrt (a * (b * c)) ≤ a + b * c := by
    have h2 : Real.sqrt (a * (b * c)) ≤ (a + b * c) / 2 := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      nlinarith [sq_nonneg (a - b * c)]
    linarith
  -- `√a √b √c = √(a * (b * c))`
  have hsqrtprod : Real.sqrt a * Real.sqrt b * Real.sqrt c = Real.sqrt (a * (b * c)) := by
    rw [Real.sqrt_mul ha (b * c), Real.sqrt_mul hb c]
    ring
  have key : 2 * (1 - δ) * (Real.sqrt a * Real.sqrt b * Real.sqrt c)
      ≤ (1 - a) * (1 - b) * (1 - c) := by
    rw [hsqrtprod]
    calc 2 * (1 - δ) * Real.sqrt (a * (b * c))
        ≤ 2 * (1 - a) * Real.sqrt (a * (b * c)) := by
          have h : 2 * (1 - δ) ≤ 2 * (1 - a) := by linarith
          exact mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg _)
        _ = (1 - a) * (2 * Real.sqrt (a * (b * c))) := by ring
        _ ≤ (1 - a) * (a + b * c) := by
          exact mul_le_mul_of_nonneg_left hamgm (le_of_lt h1a)
        _ = (1 - a) * (1 - b) * (1 - c) := by rw [← hid]; ring
  have hpos : (0 : ℝ) < 2 * (1 - δ) := by linarith
  rw [div_le_iff₀ hD, div_mul_eq_mul_div, one_mul, le_div_iff₀ hpos]
  nlinarith [key]

theorem matF_bound_three (x : Fin 3 → ℝ) (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i < 1)
    (hsum : ∑ i, x i = 1) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 8)
    (hsmall : ∃ i, x i ≤ δ) : matF x ≤ 1 / (2 * (1 - δ)) := by
  obtain ⟨i, hi⟩ := hsmall
  have hsum3 : x 0 + x 1 + x 2 = 1 := by
    simpa [Fin.sum_univ_three] using hsum
  simp only [matF, Fin.prod_univ_three]
  -- the small coordinate is `x i`; the three cases differ only by a permutation
  fin_cases i
  · exact matF_three_aux (x 0) (x 1) (x 2) δ (h0 0) (h0 1) (h0 2) (h1 0) (h1 1) (h1 2)
      hsum3 hδ0 hδ hi
  · convert matF_three_aux (x 1) (x 0) (x 2) δ (h0 1) (h0 0) (h0 2) (h1 1) (h1 0) (h1 2)
      (by linarith) hδ0 hδ hi using 1
    ring
  · convert matF_three_aux (x 2) (x 0) (x 1) δ (h0 2) (h0 0) (h0 1) (h1 2) (h1 0) (h1 1)
      (by linarith) hδ0 hδ hi using 1
    ring

end Work.Mostow
