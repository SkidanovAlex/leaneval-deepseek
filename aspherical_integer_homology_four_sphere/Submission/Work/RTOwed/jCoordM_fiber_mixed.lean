import Mathlib
import Submission.Work.RTOwed.jLat
import Submission.Work.Cusp.cuspCoordM_injective
import Submission.Work.Cusp.cuspInvInner_nrm

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function
open scoped RealInnerProductSpace

namespace Work.RTOWed

open Work.Cusp

/-! ### The two layer-parameter bounds of the mixed case -/

/-- **Below the junction height `s₁ < x 3 < s_J`, the outer chart recovers a layer parameter
strictly above `1/2`.**

The recovered parameter is `t = 1 + (log x₃ − log β(x))/(2 (log β(x) − log s_J))`; since
`x₃ < s_J` and `β(x) ≤ β_max < s_J`, both `log x₃ − log s_J` and `log β(x) − log s_J` are
negative, so `t − 1/2 = (log x₃ − log s_J)/(2 (log β(x) − log s_J)) > 0`. -/
private theorem jnrm_cuspInvOuter_gt_half {v : Work.Space.Cusp} {x : Work.Cusp.E4}
    (h1 : Work.Cusp.s1 < x 3) (h2 : x 3 < Work.Cusp.sJ) :
    1 / 2 < Work.Cusp.nrm (Work.Cusp.cuspInvOuter v x).1 := by
  set b : ℝ := Work.Cusp.beta (Work.Cusp.xOf x) with hb
  have hxpos : 0 < x 3 := lt_trans (by norm_num [Work.Cusp.s1]) h1
  have hbpos : 0 < b := by rw [hb]; exact Work.Cusp.beta_pos _
  have hblt : b < Work.Cusp.sJ := by
    rw [hb]; exact lt_of_le_of_lt (Work.Cusp.beta_le_max _) Work.Cusp.betaMax_lt_sJ
  have hlogx : Real.log (x 3) < Real.log Work.Cusp.sJ := Real.log_lt_log hxpos h2
  have hlogb : Real.log b < Real.log Work.Cusp.sJ := Real.log_lt_log hbpos hblt
  have hne : Real.log b - Real.log Work.Cusp.sJ ≠ 0 := by linarith
  have hD : (2 : ℝ) * (Real.log b - Real.log Work.Cusp.sJ) ≠ 0 :=
    mul_ne_zero (by norm_num) hne
  rw [Work.Cusp.cuspInvOuter_nrm_fst, ← hb]
  have hkey : (1 + (Real.log (x 3) - Real.log b) / (2 * (Real.log b - Real.log Work.Cusp.sJ)))
      - 1 / 2
      = (Real.log (x 3) - Real.log Work.Cusp.sJ) / (2 * (Real.log b - Real.log Work.Cusp.sJ)) := by
    field_simp
    ring
  have hpos : 0 < (Real.log (x 3) - Real.log Work.Cusp.sJ)
      / (2 * (Real.log b - Real.log Work.Cusp.sJ)) :=
    div_pos_of_neg_of_neg (by linarith) (by linarith)
  have ht : 1 / 2 < 1 + (Real.log (x 3) - Real.log b)
      / (2 * (Real.log b - Real.log Work.Cusp.sJ)) := by linarith
  exact lt_of_lt_of_le ht (le_abs_self _)

theorem jCoordM_fiber_mixed (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P Q : Work.RTOwed.JPin a v) {q r : Work.Cusp.E4}
    (hq : q ∈ Work.RTOwed.jBox v P.cU P.k P.W P.kx P.δ)
    (hr : r ∈ Work.RTOwed.jBox v Q.cU Q.k Q.W Q.kx Q.δ)
    (hq0 : q 0 ≤ Work.Cusp.rJ) (hr0 : Work.Cusp.rJ < r 0) :
    Work.RTOwed.jCoordM a v (D v) P.cU P.k P.W P.kx P.δ ⟨q, hq⟩
      ≠ Work.RTOwed.jCoordM a v (D v) Q.cU Q.k Q.W Q.kx Q.δ ⟨r, hr⟩ := by
  intro heq
  -- the outer point `r` has `¬ r 0 ≤ r_J`
  have hr1 : ¬ r 0 ≤ Work.Cusp.rJ := not_le.mpr hr0
  -- its UHS image lies in the collar box of `Q`
  have hbox' : polarToUHS v r ∈ cuspBoxTop v Q.kx Q.δ :=
    Work.RTOwed.polarToUHS_mem_cuspBoxTop v Q.kx Q.δ hr.2.2.2.2.2 hr0 hr.2.1
  -- and its height is below the junction height `s_J`
  have hx3 : (polarToUHS v r) 3 < sJ := by
    rw [Work.RTOwed.polarToUHS_three v r,
      show sJ = Real.exp (R0 - rJ) from by simp only [sJ, R0, rJ]; norm_num]
    exact Real.exp_lt_exp.mpr (by linarith)
  -- unfold the two branches
  unfold Work.RTOwed.jCoordM at heq
  rw [dite_eq_left hq0, dite_eq_right hr1] at heq
  by_cases hlt : (polarToUHS v r) 3 < beta (xOf (polarToUHS v r))
  · -- the collar point is strictly below the ceiling: it is a point of the chimney `M̄`
    unfold cuspCoordMTop at heq
    rw [dite_eq_left hlt] at heq
    obtain ⟨hxT, -⟩ := Work.Cusp.incMbar_eq_incW_imp a v heq.symm
    exact absurd hxT ((D v).mbarLow_not_TsetTop Q.kx Q.δ hbox' hlt)
  · -- the collar point is on or above the ceiling: it has layer parameter `> 1/2`
    unfold cuspCoordMTop at heq
    rw [dite_eq_right hlt] at heq
    have hpair := a.incW_injective v heq
    have hE : (cuspInvInner v q).1 = (cuspInvOuter v (polarToUHS v r)).1 := by
      have hc := congrArg (fun z : Work.Space.SquarePt × a.Torus v => (z.1 : Work.Cusp.E2)) hpair
      simpa using hc
    have hleft : nrm (cuspInvInner v q).1 ≤ 1 / 2 := by
      rw [cuspInvInner_nrm v q
        (Work.RTOwed.jBox_subset_polarBox v P.cU P.k P.W P.kx P.δ hq) hq0]
      rw [div_le_iff₀ (by norm_num [rJ] : (0 : ℝ) < 2 * rJ)]
      have : (1 / 2 : ℝ) * (2 * rJ) = rJ := by norm_num [rJ]
      linarith
    have hright : 1 / 2 < nrm (cuspInvOuter v (polarToUHS v r)).1 :=
      jnrm_cuspInvOuter_gt_half hbox'.2.1 hx3
    rw [← hE] at hright
    linarith

end Work.RTOWed
