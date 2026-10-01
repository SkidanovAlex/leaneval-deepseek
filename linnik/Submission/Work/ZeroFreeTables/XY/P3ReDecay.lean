/-
# ZeroFreeTables/XY/P3ReDecay

The elementary decay estimate for `Re P₃` at the argument `α/(a + iu)` that the
`XY`-engine of the order-2 `λ₁`-estimate needs:

  `|Re P₃(α/(a + iu))| ≤ 5 α²/u²`   whenever `0 < a ≤ α ≤ u`.

With `P₃(X) = X + X² + (2/3)X³` and `w = α/(a+iu)` one has `Re w = αa/(a²+u²)`
and `|w|² = α²/(a²+u²)`, and the identity `P3_re_eq` of `P3Pos.lean` reads

  `Re P₃(w) = (8/3)(Re w)³ + (1 + 2 Re w)(Re w − |w|²)`.

Both `Re w` and `|w|²` lie in `[0, α²/u²]` (using `0 < a ≤ α ≤ u`), and
`Re w ≤ 1/2`; hence `(8/3)(Re w)³ ≤ (2/3)α²/u²` and
`|1 + 2 Re w| · |Re w − |w|²| ≤ 2 α²/u²`, giving the bound with `8/3 ≤ 5`
to spare.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.P3Pos

namespace Work.ZeroFreeTables.XY

noncomputable section

/-- **Real-variable core of the decay estimate.**  If `0 ≤ x ≤ min A (1/2)` and
`0 ≤ ns ≤ A` then `|(8/3)x³ + (1+2x)(x − ns)| ≤ 5A`.

This is the estimate for `Re P₃(w)` in the variables `x = Re w`, `ns = |w|²`,
`A = α²/u²`. -/
private lemma P3_reDecay_core {x ns A : ℝ} (hx0 : 0 ≤ x) (hxA : x ≤ A) (hxh : x ≤ 1 / 2)
    (hns0 : 0 ≤ ns) (hnsA : ns ≤ A) :
    |(8 / 3) * x ^ 3 + (1 + 2 * x) * (x - ns)| ≤ 5 * A := by
  have hA : 0 ≤ A := le_trans hx0 hxA
  have h1x : 0 ≤ 1 + 2 * x := by linarith
  have h2x : 1 + 2 * x ≤ 2 := by linarith
  have hx3 : (8 / 3) * x ^ 3 ≤ (2 / 3) * A := by
    nlinarith [mul_nonneg hx0 hx0, mul_nonneg (sub_nonneg.mpr hxh) (sub_nonneg.mpr hxh),
      sq_nonneg x, hx0, hxh, hxA]
  have hupper : (8 / 3) * x ^ 3 + (1 + 2 * x) * (x - ns) ≤ 5 * A := by
    have h := mul_le_mul (by linarith : x - ns ≤ A) h2x h1x hA
    nlinarith [h, hx3]
  have hlower : -(5 * A) ≤ (8 / 3) * x ^ 3 + (1 + 2 * x) * (x - ns) := by
    have h1 : -A * (1 + 2 * x) ≤ (x - ns) * (1 + 2 * x) :=
      mul_le_mul_of_nonneg_right (by linarith : -A ≤ x - ns) h1x
    have h2 : -A * 2 ≤ -A * (1 + 2 * x) :=
      mul_le_mul_of_nonpos_left h2x (by linarith : -A ≤ 0)
    have h3 : 0 ≤ (8 / 3) * x ^ 3 := by positivity
    nlinarith [h1, h2, h3]
  rw [abs_le]
  exact ⟨hlower, hupper⟩

/-- **The explicit form of `Re P₃(α/(a+iu))`.**  With `x = αa/(a²+u²)` and
`ns = α²/(a²+u²)` (= `Re w` and `|w|²` for `w = α/(a+iu)`), the identity
`P3_re_eq` gives `Re P₃(w) = (8/3)x³ + (1+2x)(x − ns)`. -/
private lemma P3_re_div_form (α a u : ℝ) :
    (Work.ZeroFreeTables.P3 ((α : ℂ) / ((a : ℂ) + (u : ℂ) * Complex.I))).re
      = (8 / 3) * (α * a / (a ^ 2 + u ^ 2)) ^ 3
        + (1 + 2 * (α * a / (a ^ 2 + u ^ 2)))
          * (α * a / (a ^ 2 + u ^ 2) - α ^ 2 / (a ^ 2 + u ^ 2)) := by
  have hre : ((α : ℂ) / ((a : ℂ) + (u : ℂ) * Complex.I)).re = α * a / (a ^ 2 + u ^ 2) := by
    rw [Complex.div_re]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.normSq_apply]
    ring
  have hns : Complex.normSq ((α : ℂ) / ((a : ℂ) + (u : ℂ) * Complex.I))
      = α ^ 2 / (a ^ 2 + u ^ 2) := by
    rw [Complex.normSq_div, Complex.normSq_ofReal, Complex.normSq_add_mul_I]
    ring
  rw [Work.ZeroFreeTables.P3_re_eq, hre, hns]

/-- **Decay of `Re P₃` at `α/(a + iu)`.**  For `0 < a ≤ α ≤ u`,

  `|Re P₃(α/(a + iu))| ≤ 5 α²/u²`. -/
theorem P3ReDecay {a α u : ℝ} (ha : 0 < a) (haα : a ≤ α) (hαu : α ≤ u) :
    |(Work.ZeroFreeTables.P3 ((α : ℂ) / ((a : ℂ) + (u : ℂ) * Complex.I))).re| ≤ 5 * α ^ 2 / u ^ 2 := by
  have hu : 0 < u := lt_of_lt_of_le ha (le_trans haα hαu)
  have hα0 : 0 ≤ α := le_trans (le_of_lt ha) haα
  have hden : (0 : ℝ) < a ^ 2 + u ^ 2 := by positivity
  have hdenu : (0 : ℝ) < u ^ 2 := by positivity
  have hx0 : 0 ≤ α * a / (a ^ 2 + u ^ 2) := by positivity
  have hxh : α * a / (a ^ 2 + u ^ 2) ≤ 1 / 2 := by
    rw [div_le_iff₀ hden]
    nlinarith [sq_nonneg (a - u), mul_nonneg (le_of_lt ha) (le_of_lt hu),
      mul_le_mul_of_nonneg_right haα (le_of_lt ha)]
  have hxA : α * a / (a ^ 2 + u ^ 2) ≤ α ^ 2 / u ^ 2 := by
    rw [div_le_div_iff₀ hden hdenu]
    nlinarith [mul_le_mul_of_nonneg_right haα hα0, mul_le_mul_of_nonneg_right haα (le_of_lt ha),
      sq_nonneg u, hα0, le_of_lt ha, le_of_lt hu]
  have hns0 : 0 ≤ α ^ 2 / (a ^ 2 + u ^ 2) := by positivity
  have hnsA : α ^ 2 / (a ^ 2 + u ^ 2) ≤ α ^ 2 / u ^ 2 := by
    rw [div_le_div_iff₀ hden hdenu]
    nlinarith [sq_nonneg u, sq_nonneg a, hα0, le_of_lt hu]
  rw [P3_re_div_form]
  have hcore := P3_reDecay_core (x := α * a / (a ^ 2 + u ^ 2))
    (ns := α ^ 2 / (a ^ 2 + u ^ 2)) (A := α ^ 2 / u ^ 2) hx0 hxA hxh hns0 hnsA
  simpa only [mul_div_assoc] using hcore

end

end Work.ZeroFreeTables.XY
