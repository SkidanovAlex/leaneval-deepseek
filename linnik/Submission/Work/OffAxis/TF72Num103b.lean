import Mathlib
import Submission.Work.ZeroFreeTables.testFn72_defs
import Submission.Work.ZeroFreeTables.tf72Fc_decay
import Submission.Work.ZeroFreeTables.exp_neg_mul_ibp
import Submission.Work.ZeroFreeTables.OffAxis.TF72Calc
import Submission.Work.ZeroFreeTables.XY.xyReQuadFarBound
import Submission.Work.OffAxis.tf72poly_iteratedDeriv_two_bound
import Submission.Work.OffAxis.tf72_far_arith

/-!
# Off-axis far bound for the Lemma 7.2 Laplace transform

For Heath-Brown's Lemma 7.2 test function `f = tf72f` at scale `λ = 6/7` and its
Laplace transform `F(z) = ∫₀^{7/3} e^{-zt} f(t) dt`, the real part is small in the
far strip:

  `|Re F(-a + i m)| ≤ 16/315` for `0 ≤ a ≤ 6/7` and `|m| ≥ 200`.

This is the off-axis decay needed by the `F`-method of HB §10 (Lemma 10.3): the
`F(-λ₁ + iµ)` terms with `|µ|` large are negligible.

The proof is a two-fold integration by parts.  `tf72f (6/7)` agrees on `[0, 7/3]`
with the quintic `tf72poly (6/7)`, which vanishes to *third* order at the right
endpoint and has *no* linear term, so

  `F(z) = p(0)/z + z⁻² ∫₀^{7/3} e^{-zt} p''(t) dt`.

Since `p(0) = 32/35` is real, `|Re (p(0)/z)| ≤ p(0)·|Re z|/‖z‖² ≤ (32/35)·1/m²`,
and the remainder is bounded by `sup |p''| · e^{7/3} · (7/3) / m²` using
`|Re z| ≤ 1`.  With `sup |p''| ≤ 16·(6/7)^3 = 3456/343` (`tf72poly_iteratedDeriv_two_bound`)
this is `≤ (32/35 + e^{7/3}·(3456/343)·(7/3))/m²`, and `tf72_far_arith` finishes
with `m² ≥ 40000`.
-/

namespace Work.OffAxis

theorem TF72Num103b :
    ∀ a m : ℝ, 0 ≤ a → a ≤ 6/7 → 200 ≤ |m| →
      |(Work.ZeroFreeTables.tf72Fc ((6:ℝ)/7) (((-a : ℝ) : ℂ) + (m : ℂ) * Complex.I)).re| ≤ 16/315 := by
  intro a m ha ham hm
  set z : ℂ := ((-a : ℝ) : ℂ) + (m : ℂ) * Complex.I with hzdef
  have hzre : |z.re| ≤ 1 := by
    have h1 : z.re = -a := by rw [hzdef]; simp
    rw [h1, abs_neg, abs_of_nonneg ha]
    linarith [ham, show ((6:ℝ)/7 : ℝ) ≤ 1 by norm_num]
  have hzim : z.im ≠ 0 := by
    have hm0 : m ≠ 0 := by
      intro h; rw [h, abs_zero] at hm; norm_num at hm
    have h1 : z.im = m := by rw [hzdef]; simp
    rw [h1]; exact hm0
  have hM2nn : (0:ℝ) ≤ 16 * ((6:ℝ)/7)^3 := by norm_num
  have hM2 : ∀ t ∈ Set.Icc (0:ℝ) (2 / ((6:ℝ)/7)),
      ‖((iteratedDeriv 2 (Work.ZeroFreeTables.tf72poly ((6:ℝ)/7)) t : ℝ) : ℂ)‖
        ≤ 16 * ((6:ℝ)/7)^3 := by
    intro t ht
    exact tf72poly_iteratedDeriv_two_bound ((6:ℝ)/7) t (by norm_num) ht.1 ht.2
  have hquad := Work.ZeroFreeTables.XY.tf72Fc_re_quadLe ((6:ℝ)/7) (16 * ((6:ℝ)/7)^3)
      (by norm_num) hM2nn hM2 z hzre hzim
  have hz : z.im = m := by rw [hzdef]; simp
  have h0 : |Work.ZeroFreeTables.tf72poly ((6:ℝ)/7) 0| = 32/35 := by
    unfold Work.ZeroFreeTables.tf72poly
    norm_num
  rw [hz, h0] at hquad
  have he1 : (2:ℝ) / ((6:ℝ)/7) = 7/3 := by norm_num
  have he2 : (16:ℝ) * ((6:ℝ)/7)^3 = 3456/343 := by norm_num
  rw [he1, he2] at hquad
  exact hquad.trans (tf72_far_arith m hm)

end Work.OffAxis
