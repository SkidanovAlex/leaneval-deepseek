/-
# ZeroFreeTables/XY/P3ReDecay2

The signed version of the decay estimate `P3ReDecay`: the hypothesis is
`α ≤ |u|` rather than `α ≤ u`, so `u` may be negative.  Since `Re P₃(α/(a+iu))`
and `|α/(a+iu)|²` are both even functions of `u`, the estimate

  `|Re P₃(α/(a+iu))| ≤ 5 α²/u²`

holds verbatim on the whole range `0 < a ≤ α ≤ |u|`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.XY.P3ReDecay

namespace Work.ZeroFreeTables.XY

noncomputable section

/-- **Real-variable core of the decay estimate.**  If `0 ≤ x ≤ min A (1/2)` and
`0 ≤ ns ≤ A` then `|(8/3)x³ + (1+2x)(x − ns)| ≤ 5A`. -/
private lemma P3_reDecay_core' {x ns A : ℝ} (hx0 : 0 ≤ x) (hxA : x ≤ A) (hxh : x ≤ 1 / 2)
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
`ns = α²/(a²+u²)`, `Re P₃(w) = (8/3)x³ + (1+2x)(x − ns)`. -/
private lemma P3_re_div_form' (α a u : ℝ) :
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

/-- **Decay of `Re P₃` at `α/(a + iu)`, signed form.**  For `0 < a ≤ α ≤ |u|`,

  `|Re P₃(α/(a + iu))| ≤ 5 α²/u²`. -/
theorem P3ReDecay2 {a α u : ℝ} (ha : 0 < a) (haα : a ≤ α) (hu : α ≤ |u|) :
    |(Work.ZeroFreeTables.P3 ((α : ℂ) / ((a : ℂ) + (u : ℂ) * Complex.I))).re| ≤ 5 * α ^ 2 / u ^ 2 := by
  have hα : 0 < α := lt_of_lt_of_le ha haα
  have hα0 : 0 ≤ α := le_of_lt hα
  have hua : 0 < |u| := lt_of_lt_of_le hα hu
  have hsq : (|u| : ℝ) ^ 2 = u ^ 2 := sq_abs u
  have hden : (0 : ℝ) < a ^ 2 + u ^ 2 := by positivity
  have hdenu : (0 : ℝ) < u ^ 2 := by rw [← hsq]; positivity
  have hx0 : 0 ≤ α * a / (a ^ 2 + u ^ 2) := by positivity
  have hxh : α * a / (a ^ 2 + u ^ 2) ≤ 1 / 2 := by
    rw [div_le_iff₀ hden]
    have h1 : α * a ≤ |u| * a := mul_le_mul_of_nonneg_right hu (le_of_lt ha)
    nlinarith [h1, sq_nonneg (|u| - a), hsq]
  have hxA : α * a / (a ^ 2 + u ^ 2) ≤ α ^ 2 / u ^ 2 := by
    rw [div_le_div_iff₀ hden hdenu]
    nlinarith [mul_le_mul_of_nonneg_right haα hα0, sq_nonneg u, sq_nonneg a, sq_nonneg α, hα0]
  have hns0 : 0 ≤ α ^ 2 / (a ^ 2 + u ^ 2) := by positivity
  have hnsA : α ^ 2 / (a ^ 2 + u ^ 2) ≤ α ^ 2 / u ^ 2 := by
    rw [div_le_div_iff₀ hden hdenu]
    nlinarith [sq_nonneg u, sq_nonneg a, sq_nonneg α, hα0]
  rw [P3_re_div_form']
  have hcore := P3_reDecay_core' (x := α * a / (a ^ 2 + u ^ 2))
    (ns := α ^ 2 / (a ^ 2 + u ^ 2)) (A := α ^ 2 / u ^ 2) hx0 hxA hxh hns0 hnsA
  simpa only [mul_div_assoc] using hcore

end

end Work.ZeroFreeTables.XY
