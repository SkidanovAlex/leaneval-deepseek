/-
# Area 7 — `λ ↦ B(K,λ)` (HB Lemma 13.3) is antitone on **all** of `ℝ`

`Work.LinnikContract.Bfun K` is HB's per-character constant

  `B(λ) = (1 - e^{-2Kλ})/(6K²λ) + (2Kλ - 1 + e^{-2Kλ})/(2K²λ²)`   (`λ ≠ 0`),
  `B(0) = 1/(3K) + 1`,

and the aim here is `B` is non-increasing on the whole line (for `K > 0`).

* On `(0,∞)` this is the colleague's `Work.A7.Bfun_antitone`.
* On `(-∞,0)` we use `Bfun K λ = 1/(3K) + (2 - 2λ/3)·g(2Kλ)` (`BfunAux.Bfun_eq_gAux`):
  the coefficient `2 - 2λ/3` is non-increasing in `λ` and positive for `λ ≤ 0`, while
  `g` is non-increasing on `(-∞,0)` (`gAux_antitone_Iio`) and non-negative there.
* Across `λ = 0` the two one-sided branches meet at `B(0)`: `B(λ) ≤ B(0)` for `λ > 0`
  (`Bfun_le_at_zero_of_pos`) and `B(0) ≤ B(λ)` for `λ < 0` (`le_Bfun_at_zero_of_neg`).
-/
import Mathlib
import Submission.Work.LinnikAreas.A7.Defs
import Submission.Work.A7.BfunAux
import Submission.Work.A7.Bfun_antitone
import Submission.Work.A7.gAux_antitone_Iio
import Submission.Work.A7.Bfun_le_at_zero_of_pos
import Submission.Work.A7.le_Bfun_at_zero_of_neg

namespace Work.A7

open Work.LinnikContract

/-- `gAux` is non-negative everywhere (so in particular on the negative half-line):
`gAux t = (t - 1 + e^{-t})/t²` and `t - 1 + e^{-t} ≥ 0` because `1 - t ≤ e^{-t}`. -/
private lemma gAux_nonneg (t : ℝ) : 0 ≤ gAux t := by
  have hnum : 0 ≤ t - 1 + Real.exp (-t) := by
    have h := Real.add_one_le_exp (-t)
    linarith
  rw [gAux]
  exact div_nonneg hnum (sq_nonneg t)

/-- `Bfun K` is antitone on `(-∞,0)`. -/
private lemma Bfun_antitone_neg {K x y : ℝ} (hK : 0 < K) (hxy : x ≤ y) (hy : y < 0) :
    Bfun K y ≤ Bfun K x := by
  have hx : x < 0 := lt_of_le_of_lt hxy hy
  have hKne : K ≠ 0 := ne_of_gt hK
  rw [Bfun_eq_gAux hKne (ne_of_lt hy), Bfun_eq_gAux hKne (ne_of_lt hx)]
  have hcoef : 2 - 2 * y / 3 ≤ 2 - 2 * x / 3 := by linarith
  have hg : gAux (2 * K * y) ≤ gAux (2 * K * x) :=
    gAux_antitone_Iio (show 2 * K * x < 0 by nlinarith) (show 2 * K * y < 0 by nlinarith)
      (by nlinarith)
  have h1 : 0 ≤ gAux (2 * K * y) := gAux_nonneg (2 * K * y)
  have h2 : 0 ≤ 2 - 2 * x / 3 := by linarith
  linarith [mul_le_mul hcoef hg h1 h2]

theorem Bfun_antitone_all {K : ℝ} (hK : 0 < K) :
    ∀ {x y : ℝ}, x ≤ y → Work.LinnikContract.Bfun K y ≤ Work.LinnikContract.Bfun K x := by
  intro x y hxy
  rcases lt_trichotomy x 0 with hx0 | hx0 | hx0
  · rcases lt_trichotomy y 0 with hy0 | hy0 | hy0
    · exact Bfun_antitone_neg hK hxy hy0
    · rw [hy0]
      exact le_Bfun_at_zero_of_neg hK hx0
    · exact le_trans (Bfun_le_at_zero_of_pos hK hy0) (le_Bfun_at_zero_of_neg hK hx0)
  · subst hx0
    rcases eq_or_lt_of_le hxy with h | h
    · rw [← h]
    · exact Bfun_le_at_zero_of_pos hK h
  · exact Bfun_antitone hK hx0 hxy

end Work.A7
