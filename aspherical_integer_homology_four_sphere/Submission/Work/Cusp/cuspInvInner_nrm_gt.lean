/-
# The inner inverse of the polar chart recovers a layer parameter `> 1/24`

`cuspInvInner v q = (t • bndOfU u, y)` where `t` is the layer parameter `‖p‖∞` recovered from
`q 0 = r`: `t = r/(2 r_J)` on the inner branch (`r ≤ r_J`) and
`t = 1 + (R₀ − r − log b)/(2 (log b − log s_J))` with `b = β (cuspX v u y)` on the collar branch
(`r_J < r`).  Since `nrm (bndOfU u) = 1`, the sup norm of the first component is `|t|`, so the
statement is that the recovered layer parameter is `> 1/24` on the polar box
`1/4 < r < r_J + 1`.

* inner branch: `t = r/(2 r_J) = r/6`, and `r > 1/4` gives `t > 1/24`;
* collar branch: `r > r_J = 3`, and `β x < 3/2 < s_J = e^{1/2}` (the ceiling is always below the
  junction), so `log b − log s_J < 0` while `R₀ − r − log s_J = 3 − r < 0`; hence

  `t − 1/2 = (R₀ − r − log s_J)/(2 (log b − log s_J)) > 0`,

  the quotient of two negative numbers.  Thus `t > 1/2 > 1/24`.

No use is made of `q 0 < r_J + 1` beyond `r_J < 3 + 1`; the bound `t > 1/2` on the collar is the
stronger statement.
-/
import Mathlib
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.cuspInvInner_nrm
import Submission.Work.Cusp.ThetaPolar_cuspInvInner
import Submission.Work.Cusp.nrm_smul
import Submission.Work.Cusp.nrm_bndOfU
import Submission.Work.Cusp.beta_pos
import Submission.Work.Cusp.beta_le_max
import Submission.Work.Cusp.betaMax_lt_sJ

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

open scoped Real InnerProductSpace

/-- **Every ceiling height is strictly below the junction height** `s_J = e^{1/2}`: `β x ≤ 3/2`
(`beta_le_max`) and `3/2 < e^{1/2}` (`betaMax_lt_sJ`).  This is what makes the collar branch of
`cuspInvInner` have a *negative* denominator `log (β x) − log s_J`. -/
theorem beta_lt_sJ (x : E3) : beta x < sJ :=
  lt_of_le_of_lt (beta_le_max x) betaMax_lt_sJ

/-- **The recovered layer parameter of `cuspInvInner` is `> 1/24` on the polar box.**

With `y = invY v (q₂,q₃)`, `u` the recovered perimeter coordinate and `b = β (cuspX v u y)`, the
layer parameter is `t = q 0/(2 r_J)` for `q 0 ≤ r_J` and
`t = 1 + (R₀ − q 0 − log b)/(2 (log b − log s_J))` for `q 0 > r_J`; we show `1/24 < t`:

* `q 0 ≤ r_J`: `t = q 0/6 > (1/4)/6 = 1/24` by the lower bound `q 0 > 1/4` of the polar box;
* `q 0 > r_J`: `t − 1/2 = (R₀ − q 0 − log s_J)/(2 (log b − log s_J))`, a quotient of two negative
  numbers (`R₀ − q 0 − log s_J = 3 − q 0 < 0` and `log b − log s_J < 0` by `beta_lt_sJ`), so
  `t > 1/2 > 1/24`.

Since `nrm (bndOfU u) = 1` (`nrm_bndOfU`) and `t > 0`, `nrm (t • bndOfU u) = |t| = t`. -/
theorem cuspInvInner_nrm_gt (v : Fin 5) (q : E4) (hq : q ∈ polarBox) :
    (1 : ℝ) / 24 < nrm (cuspInvInner v q).1 := by
  obtain ⟨hq0lo, hq0hi⟩ := hq
  have hrJ3 : rJ = 3 := rfl
  simp only [cuspInvInner]
  set y : E2 := invY v !₂[q 2, q 3] with hy
  set uu : ℝ := (q 1 - 2 * π * (⟪cuspY v y, slope v⟫_ℝ / ‖slope v‖ ^ 2)) / (2 * π) with huu
  set b : ℝ := beta (cuspX v uu y) with hb
  set t : ℝ := (if q 0 ≤ rJ then q 0 / (2 * rJ)
      else 1 + (R0 - q 0 - Real.log b) / (2 * (Real.log b - Real.log sJ))) with ht
  -- the ceiling is positive (for `log`) and below the junction
  have hbpos : 0 < b := by rw [hb]; exact beta_pos _
  have hblt : b < sJ := by rw [hb]; exact beta_lt_sJ _
  have hlogb_lt : Real.log b < Real.log sJ := Real.log_lt_log hbpos hblt
  have hLne : Real.log b - Real.log sJ ≠ 0 := ne_of_lt (by linarith)
  -- the layer parameter is `> 1/24`
  have ht_gt : (1 : ℝ) / 24 < t := by
    by_cases hc0 : q 0 ≤ rJ
    · -- inner branch: `t = q 0/(2 r_J) = q 0/6 > 1/24`
      rw [ht, if_pos hc0]
      have h2rJ : (0 : ℝ) < 2 * rJ := by rw [hrJ3]; norm_num
      rw [lt_div_iff₀ h2rJ]
      have he : (1 : ℝ) / 24 * (2 * rJ) = 1 / 4 := by rw [hrJ3]; norm_num
      linarith
    · -- collar branch: `t - 1/2` is the quotient of two negative numbers
      have hq0gt : rJ < q 0 := lt_of_not_ge hc0
      have hkey : t - 1/2 = (R0 - q 0 - Real.log sJ) / (2 * (Real.log b - Real.log sJ)) := by
        rw [ht, if_neg hc0]
        field_simp
        ring
      have hnum : R0 - q 0 - Real.log sJ < 0 := by
        have h3 : (3 : ℝ) < q 0 := by rw [← hrJ3]; exact hq0gt
        rw [R0, sJ, Real.log_exp]
        linarith
      have hden : 2 * (Real.log b - Real.log sJ) < 0 := by linarith
      have : 0 < t - 1/2 := by rw [hkey]; exact div_pos_of_neg_of_neg hnum hden
      linarith
  have ht_pos : 0 < t := lt_trans (by norm_num) ht_gt
  rw [nrm_smul, nrm_bndOfU, mul_one, abs_of_pos ht_pos]
  exact ht_gt

end Work.Cusp
