/-
# The ceiling lemma for the unslabbed collar chart

For a point `q` of the *unslabbed* collar source `cuspSourceTop v c δ` (the box of side `2δ` with
height in the window `(s₁, sTop)`, on or above the ceiling `s = β(x)`) the inverse outer chart
`cuspInvOuter v` recovers the layer parameter

  `t = 1 + (log s − log β(x)) / (2 (log β(x) − log s_J))`.

Writing `A = log s − log β(x) ≥ 0` (the point is on or above the ceiling) and
`J = log s_J − log β(x) > 0`, this is `t = 1 − A / (2J)`, so `t = 1` if and only if `A = 0`, i.e.
if and only if `s = β(x)`.  Equivalently: the only points of the collar source whose recovered
layer parameter is `1` are the points of the ceiling `s = β(x)`, i.e. the points of the truncation
torus `τ_v`.

This is the unslabbed companion of `Work.Cusp.cuspInvOuter_nrm_Top`, which gives `1/4 < t ≤ 1`
on the collar source, and the analogue of `cuspInvOuter_nrm_eq_one_ceiling` for the slabbed source
(where the same conclusion is forced by the extra bound `s < s_J` of the box).  Both ingredients of
`cuspInvOuter_nrm_Top` are used:

* `t > 0`, from `β(x) · s² < s_J³` (the numerical property
  `Work.Cusp.betaMax_mul_sTop_sq_lt_sJ_cu` of `sTop = 33/20`), so that the sup norm
  `‖(cuspInvOuter v q).1‖∞ = |t|` of the recovered point is `t` itself;
* the vanishing of the logarithm quotient above.
-/
import Mathlib
import Submission.Work.Cusp.TopBox
import Submission.Work.Cusp.TopWindow
import Submission.Work.Cusp.nrm_smul
import Submission.Work.Cusp.nrm_bndOfU
import Submission.Work.Cusp.cuspInvOuter_mem_SqTop
import Submission.Work.Cusp.cuspInvOuter_heightTop
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function
open scoped Real InnerProductSpace

namespace Work.Cusp

/-- **The recovered layer parameter of the unslabbed collar chart, as an explicit formula.**
For a point of the collar source the scalar

  `t = 1 + (log (q 3) − log β(x)) / (2 (log β(x) − log s_J))`

is positive (`β(x) · (q 3)² < s_J³` and `q 3 ≥ β(x)`), so that the sup norm of the recovered
point `t • bndOfU (outerU v x)` — which is `|t|` — is `t` itself. -/
theorem cuspInvOuter_nrm_fst_eqTop (v : Fin 5) (c : E3) (δ : ℝ) (q : E4)
    (hq : q ∈ cuspSourceTop v c δ) :
    nrm (cuspInvOuter v q).1
      = 1 + (Real.log (q 3) - Real.log (beta (xOf q))) /
          (2 * (Real.log (beta (xOf q)) - Real.log sJ)) := by
  obtain ⟨hbox, hbeta⟩ := hq
  obtain ⟨_, hs1, hlt⟩ := hbox
  have hbpos : 0 < beta (xOf q) := beta_pos _
  have hs_pos : 0 < q 3 := lt_trans (by norm_num [s1]) hs1
  -- `β(x) · s² < s_J³`
  have hprod : q 3 ^ 2 * beta (xOf q) < sJ ^ 3 := by
    have h1 : q 3 ^ 2 * beta (xOf q) < sTop ^ 2 * beta (xOf q) :=
      mul_lt_mul_of_pos_right (by nlinarith [hs_pos, hlt]) hbpos
    have h2 : sTop ^ 2 * beta (xOf q) ≤ sTop ^ 2 * betaMax :=
      mul_le_mul_of_nonneg_left (beta_le_max _) (by positivity)
    linarith [betaMax_mul_sTop_sq_lt_sJ_cu]
  -- its logarithmic form `2 A < 3 J`
  have hlogprod : 2 * Real.log (q 3) + Real.log (beta (xOf q)) < 3 * Real.log sJ := by
    have h := Real.log_lt_log (by positivity) hprod
    rw [Real.log_mul (by positivity) (ne_of_gt hbpos), Real.log_pow, Real.log_pow] at h
    push_cast at h
    linarith
  have hA0 : 0 ≤ Real.log (q 3) - Real.log (beta (xOf q)) := by
    have h := Real.log_le_log hbpos hbeta
    linarith
  have hJpos : 0 < Real.log sJ - Real.log (beta (xOf q)) := by
    have h := Real.log_lt_log hbpos (lt_of_le_of_lt (beta_le_max _) betaMax_lt_sJ)
    linarith
  have h2A : 2 * (Real.log (q 3) - Real.log (beta (xOf q)))
      < 3 * (Real.log sJ - Real.log (beta (xOf q))) := by linarith
  -- hence `t = 1 − A/(2J) > 0`
  have hTpos : 0 < 1 + (Real.log (q 3) - Real.log (beta (xOf q))) /
      (2 * (Real.log (beta (xOf q)) - Real.log sJ)) := by
    have hden : 2 * (Real.log (beta (xOf q)) - Real.log sJ)
        = -(2 * (Real.log sJ - Real.log (beta (xOf q)))) := by ring
    rw [hden, div_neg]
    have h2Jpos : (0 : ℝ) < 2 * (Real.log sJ - Real.log (beta (xOf q))) := by linarith
    have hlt1 : (Real.log (q 3) - Real.log (beta (xOf q))) /
        (2 * (Real.log sJ - Real.log (beta (xOf q)))) < 1 := by
      rw [div_lt_one h2Jpos]
      linarith
    linarith
  -- the recovered point is that scalar times a boundary point of sup norm `1`
  have hpe : (cuspInvOuter v q).1 =
      (1 + (Real.log (q 3) - Real.log (beta (xOf q))) /
        (2 * (Real.log (beta (xOf q)) - Real.log sJ))) • bndOfU (outerU v (xOf q)) := by
    simp only [cuspInvOuter, xOf]
  rw [hpe, nrm_smul, nrm_bndOfU, mul_one, abs_of_pos hTpos]

/-- **A point of the unslabbed collar source whose recovered layer parameter has sup norm `1` lies
on the ceiling** `s = β(x)`. -/
theorem cuspInvOuter_nrm_eq_one_ceilingTop (v : Fin 5) (c : E3) (δ : ℝ) (q : E4)
    (hq : q ∈ cuspSourceTop v c δ) (h1 : nrm (cuspInvOuter v q).1 = 1) :
    q 3 = beta (xOf q) := by
  -- the recovered layer parameter is the explicit quotient
  have hfst := cuspInvOuter_nrm_fst_eqTop v c δ q hq
  have hbpos : 0 < beta (xOf q) := beta_pos _
  have hs1 : s1 < q 3 := hq.1.2.1
  have hq3pos : 0 < q 3 := lt_trans (by norm_num [s1]) hs1
  rw [hfst] at h1
  -- the denominator does not vanish, so the quotient itself vanishes
  have hne : (2 : ℝ) * (Real.log (beta (xOf q)) - Real.log sJ) ≠ 0 := by
    have h := Real.log_lt_log hbpos (lt_of_le_of_lt (beta_le_max _) betaMax_lt_sJ)
    intro hc
    linarith
  have hnum : Real.log (q 3) - Real.log (beta (xOf q)) = 0 := by
    have hz : (Real.log (q 3) - Real.log (beta (xOf q))) /
        (2 * (Real.log (beta (xOf q)) - Real.log sJ)) = 0 := by linarith
    rcases div_eq_zero_iff.mp hz with h | h
    · exact h
    · exact absurd h hne
  -- two positive numbers with the same logarithm are equal
  have hlog : Real.log (q 3) = Real.log (beta (xOf q)) := by linarith
  exact Real.log_injOn_pos hq3pos hbpos hlog

end Work.Cusp
