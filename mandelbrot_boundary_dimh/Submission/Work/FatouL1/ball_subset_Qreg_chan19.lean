import Mathlib
import Submission.Work.FatouL1.massFatouDerivSubInv

/-!
# The `chan19` ball inside `Qreg`

`MandelDim.Qreg b₁ b₂` is the complement of the two closed `45°` wedges: it is the set of `w` with

* `-|(w - a).im| < (w - a).re` for every vertex `a` of `b₁` (the *left* wedges), and
* `(w - b).re < |(w - b).im|` for every vertex `b` of `b₂` (the *right* wedges).

The present lemma is the quantitative form used by the `L¹` Fatou layer: the vertices of `b₁`
sit (in the weighted sense `a.re + |a.im| ≤ K + (x₀ - 1/4)`) at weighted distance `K` to the left
of the level line `x₀ - 1/4`, the vertices of `b₂` sit (`|b.im| - b.re ≤ K - (x₀ + 19/8)`) at
weighted distance `K` to the right of the level line `x₀ + 19/8`, and `z` is a point of the slab
`[x₀ - 1/4, x₀ + 19/8]` at distance `K` from the real axis.  Then the euclidean ball centred at
`z` of radius `(|z.im| - K)/4` misses both cone families.

The two vertex estimates are the same computation on either side: moving by at most `R` in the
real direction and by at most `R` in the imaginary direction costs at most `2R`, while the weighted
vertex bound gives a gain of `|z.im| - K`; the radius `R = (|z.im| - K)/4` therefore leaves a
strict margin `(|z.im| - K)/2`, positive as soon as the ball is nondegenerate.  (When
`|z.im| = K` the radius vanishes and the ball is empty.)
-/

namespace Work.FatouL1

open Set Metric

set_option linter.unusedVariables false in
theorem ball_subset_Qreg_chan19 {b₁ b₂ : Option ℂ} {x₀ K : ℝ}
    (hK₁ : ∀ a ∈ b₁, a.re + |a.im| ≤ K + (x₀ - 1 / 4))
    (hK₂ : ∀ b ∈ b₂, |b.im| - b.re ≤ K - (x₀ + 19 / 8))
    {z : ℂ} (hz₁ : x₀ - 1 / 4 ≤ z.re) (hz₂ : z.re ≤ x₀ + 19 / 8) (hz₃ : K ≤ |z.im|) :
    Metric.ball z ((|z.im| - K) / 4) ⊆ MandelDim.Qreg b₁ b₂ := by
  intro w hw
  rw [Metric.mem_ball] at hw
  -- a nonempty ball has positive radius, hence `K < |z.im|`
  have hzK : K < |z.im| := by
    have h : 0 < (|z.im| - K) / 4 := lt_of_le_of_lt dist_nonneg hw
    linarith [hz₃]
  -- the real and imaginary displacements are both bounded by the distance
  have hwre : |w.re - z.re| ≤ dist w z := by
    rw [dist_eq_norm]
    simpa [Complex.sub_re] using Complex.abs_re_le_norm (w - z)
  have hwim : |w.im - z.im| ≤ dist w z := by
    rw [dist_eq_norm]
    simpa [Complex.sub_im] using Complex.abs_im_le_norm (w - z)
  have hwre_lt : |w.re - z.re| < (|z.im| - K) / 4 := lt_of_le_of_lt hwre hw
  have hwim_lt : |w.im - z.im| < (|z.im| - K) / 4 := lt_of_le_of_lt hwim hw
  have hwre_left : w.re > z.re - (|z.im| - K) / 4 := by
    have h := (abs_lt.1 hwre_lt).1; linarith
  have hwre_right : w.re < z.re + (|z.im| - K) / 4 := by
    have h := (abs_lt.1 hwre_lt).2; linarith
  have hwim_abs : |w.im| > |z.im| - (|z.im| - K) / 4 := by
    have h1 : |z.im| - |w.im| ≤ |w.im - z.im| :=
      (abs_sub_abs_le_abs_sub z.im w.im).trans_eq (abs_sub_comm z.im w.im)
    linarith
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · -- the left wedge of `a` lies outside the ball
    have hA : |w.im - a.im| > |z.im| - (|z.im| - K) / 4 - |a.im| := by
      have h1 : |w.im| - |a.im| ≤ |w.im - a.im| := abs_sub_abs_le_abs_sub w.im a.im
      linarith
    have hKa := hK₁ a ha
    rw [Complex.sub_re, Complex.sub_im]
    linarith
  · -- the right wedge of `b` lies outside the ball
    have hA : |w.im - b.im| > |z.im| - (|z.im| - K) / 4 - |b.im| := by
      have h1 : |w.im| - |b.im| ≤ |w.im - b.im| := abs_sub_abs_le_abs_sub w.im b.im
      linarith
    have hKb := hK₂ b hb
    rw [Complex.sub_re, Complex.sub_im]
    linarith

end Work.FatouL1
