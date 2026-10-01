/-
# ZeroFreeTables/XY/NearP3sumNonneg2

`NearP3sumNonneg2`: the near-zero sum `P9.nearP3sum` of Heath-Brown §9 is **non-negative**,
under the *window* minimality hypothesis on `lam` and the positivity `0 < a + lam` of the
numerator.

## Why it is true

By `P9.P3_re_div_eq` the summand of `nearP3sum` at a zero `u'` is exactly

  `(zeroMult χ u' : ℝ) * nearInd s δ u' * Re P₃((a+lam)/((s-u')L))`,

so it is enough to see that **every single summand is non-negative**; a `tsum` of
non-negative reals is non-negative (`tsum_nonneg`).

* If `u'` is *not* in the `δ`-window of `1 + i·Im s`, then `nearInd s δ u' = 0` and the
  summand vanishes.
* If `u'` *is* in the window and `zeroMult χ u' ≠ 0`, the hypothesis `hmin` gives
  `lam ≤ (1-u'.re)L`, whence
  `Re((s-u')L) = L·Re(s-u') = a + L(1-u'.re) ≥ a + lam`.
  Writing the argument of `P₃` as `α/(β+it)` with `α = a+lam > 0` and `β ≥ α`, the pointwise
  positivity `P3.P3Bounds.1` of `Re P₃(α/(β+it))` on `0 < α ≤ β` gives
  `0 ≤ Re P₃((a+lam)/((s-u')L))`.

No summability hypothesis is needed: `tsum_nonneg` is unconditional for non-negative terms
(an unsummable series has `tsum = 0` by definition).

The companion `NearP3sumExtract*` modules compare `nearP3sum` with a *single* summand; the
remark there (that `hmin` constrains only the zeros with `|Im u'| ≤ 10`, so an unbounded
window may contain a zero with negative `P₃`-term) concerns that comparison, and is not an
obstruction here: `P3.P3Bounds.1` needs the window minimality `hmin` only *at the zeros that
actually appear*, which is exactly what the hypothesis of this lemma supplies.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.P9.Defs
import Submission.Work.ZeroFreeTables.P3Pos

namespace Work.ZeroFreeTables.XY

open Complex

/-- **HB (4.11) at the argument `(a+lam)/((s-u)L)` of the near-zero sum, for a zero `u` of the
window.**  If `lam ≤ (1-u.re)*L` and `0 < a + lam`, the `P₃`-term at `u` is non-negative.

This is `P3.P3Bounds.1`: writing the argument as `α/(β+it)` with `α = a+lam` and
`β = Re((s-u)L) = a + L(1-u.re) ≥ a + lam = α`, positivity at `α ≤ β` gives the claim. -/
lemma P3_term_nonneg_of_window {L a lam : ℝ} (hL : 0 < L) {s u : ℂ}
    (hs : s.re = 1 + a / L) (hα : 0 < a + lam) (hlam : lam ≤ (1 - u.re) * L) :
    0 ≤ (P3 ((↑a + ↑lam) / ((s - u) * (L : ℂ)))).re := by
  have hre : ((s - u) * (L : ℂ)).re = a + L * (1 - u.re) := by
    rw [Complex.mul_re, Complex.sub_re, hs]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    field_simp
    ring
  have hle : a + lam ≤ ((s - u) * (L : ℂ)).re := by
    rw [hre]; linarith
  have h2 : ((↑(a + lam) : ℂ) / ((((s - u) * (L : ℂ)).re : ℂ)
        + (((s - u) * (L : ℂ)).im : ℂ) * Complex.I))
      = (↑a + ↑lam) / ((s - u) * (L : ℂ)) := by
    rw [← (Complex.re_add_im ((s - u) * (L : ℂ))).symm]
    push_cast
    ring
  have h := Work.ZeroFreeTables.P3.P3Bounds.1 (a + lam) (((s - u) * (L : ℂ)).re)
      (((s - u) * (L : ℂ)).im) hα hle
  rwa [h2] at h

theorem NearP3sumNonneg2 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {L a lam δ : ℝ} (hL : 0 < L) (ha : 0 < a) (hδ : 0 < δ) (hα : 0 < a + lam)
    {s : ℂ} (hmin : ∀ u' : ℂ, Work.LinnikContract.zeroMult χ u' ≠ 0 →
      ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u'‖ ≤ δ → lam ≤ (1 - u'.re) * L)
    (hs : s.re = 1 + a / L) :
    0 ≤ Work.ZeroFreeTables.P9.nearP3sum q L χ s a lam δ := by
  classical
  unfold Work.ZeroFreeTables.P9.nearP3sum
  refine tsum_nonneg (fun u => ?_)
  by_cases hnear : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ
  · -- `u` lies in the window: the summand is a product of non-negative factors
    have hind : Work.ZeroFreeTables.P9.nearInd s δ u = 1 := by
      rw [Work.ZeroFreeTables.P9.nearInd_eq_ite, if_pos hnear]
    rw [hind, mul_one]
    by_cases hz : Work.LinnikContract.zeroMult χ u = 0
    · rw [hz]; simp
    · refine mul_nonneg (Nat.cast_nonneg _) ?_
      rw [← Work.ZeroFreeTables.P9.P3_re_div_eq a lam L s u]
      exact P3_term_nonneg_of_window hL hs hα (hmin u hz hnear)
  · -- `u` lies outside the window: `nearInd = 0` kills the summand
    have hind : Work.ZeroFreeTables.P9.nearInd s δ u = 0 := by
      rw [Work.ZeroFreeTables.P9.nearInd_eq_ite, if_neg hnear]
    rw [hind]
    simp

end Work.ZeroFreeTables.XY
