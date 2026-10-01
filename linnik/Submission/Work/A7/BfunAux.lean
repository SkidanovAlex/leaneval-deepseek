/-
# Area 7 — the auxiliary function `g(t) = (t - 1 + e^{-t})/t²`

HB's per-character constant `B(λ)` (Lemma 13.3) is

  `B(λ) = (1 - e^{-2Kλ})/(6K²λ) + (2Kλ - 1 + e^{-2Kλ})/(2K²λ²)`   (`λ ≠ 0`),

and, writing `t = 2Kλ`, this is

  `B(λ) = 1/(3K) + (2 - 2λ/3) · g(t)`,   where   `g(t) = (t - 1 + e^{-t})/t²`.

Indeed the `1/(3K)` term is exactly the value `B(0) = 1/(3K) + 1` split off: for `t ≠ 0`,
`g(t) = ∫_0^1 (1-u)e^{-tu} du`, so `g(t) → 1/2` as `t → 0`, and `2·g(0) = 1`.

This is the form in which the behaviour of `Bfun` away from `λ > 0` is read off: the
coefficient `2 - 2λ/3` is non-increasing in `λ`, and `g` is non-increasing on each of
`(0,∞)` and `(-∞,0)` (each half-line is a Laplace-transform region with a non-negative
kernel), while `g ≥ 0` for `t < 0` and `g ≥ 1/2` for `t < 0`.
-/
import Mathlib
import Submission.Work.LinnikContract.Defs

noncomputable section

namespace Work.A7

/-- `g(t) = (t - 1 + e^{-t})/t²`.  For `t ≠ 0` this equals `∫_0^1 (1-u)e^{-tu} du`, a
decreasing function of `t` on each half-line, with `g(t) → 1/2` as `t → 0`. -/
def gAux (t : ℝ) : ℝ := (t - 1 + Real.exp (-t)) / t ^ 2

/-- Second form of HB's `B(λ)` (Lemma 13.3), valid for `λ ≠ 0` and `K ≠ 0`:
`B(λ) = B(0) - 1 + (2 - 2λ/3)·g(2Kλ)`, i.e. `B(λ) = 1/(3K) + (2 - 2λ/3)·g(2Kλ)`. -/
theorem Bfun_eq_gAux {K lam : ℝ} (hK : K ≠ 0) (hlam : lam ≠ 0) :
    Work.LinnikContract.Bfun K lam
      = 1 / (3 * K) + (2 - 2 * lam / 3) * gAux (2 * K * lam) := by
  rw [Work.LinnikContract.Bfun, if_neg hlam]
  unfold gAux
  have h2K : (2 : ℝ) * K * lam ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hK) hlam
  field_simp
  ring

end Work.A7
