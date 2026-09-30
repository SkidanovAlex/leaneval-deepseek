/-
# The perimeter parameter of the inner-chart inverse is `Int.fract (uqOf v q)`

The inner-chart inverse `cuspInvInner v` (`Work.Cusp.Basic`) of the polar chart recovers the layer
parameter `t = ‖p‖∞` and the point `p = t • bndOfU uu` of the filling square, where
`uu = uqOf v q` (`Work.Cusp.Charts`) is the recovered perimeter coordinate.  The perimeter parameter
`u` of a positive multiple of `bndOfU x` is `Int.fract x`: `u` is invariant under positive
rescaling (`u_smul`) and `u (bndOfU x) = Int.fract x` (`uPerim_bndOfU`, `nrm_bndOfU`).

It therefore only remains to see that the recovered layer parameter `t` is positive on the polar
box `1/4 < r < r_J + 1`.  On the inner branch `r ≤ r_J` one has `t = r/(2 r_J) > 0` because
`r > 1/4`, and on the collar branch `r_J < r` one has
`t = 1 + (R₀ − r − log b)/(2 (log b − log s_J)) > 1/2` by `cuspInvRate_gt_half` (`b = β (cuspX v uu y)`
satisfies `0 < b < s_J` by `beta_pos` and `beta_le_max`/`betaMax_lt_sJ`).
-/
import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.u_smul
import Submission.Work.Cusp.nrm_bndOfU
import Submission.Work.Cusp.uPerim_bndOfU
import Submission.Work.Cusp.beta_pos
import Submission.Work.Cusp.beta_le_max
import Submission.Work.Cusp.betaMax_lt_sJ
import Submission.Work.Cusp.ThetaPolar_cuspInvInner

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.Cusp

open scoped Real InnerProductSpace

/-- `u (bndOfU t) = Int.fract t`. -/
private lemma u_bndOfU_aux (t : ℝ) : u (bndOfU t) = Int.fract t := by
  rw [u, show bnd (bndOfU t) = bndOfU t by rw [bnd, nrm_bndOfU t, inv_one, one_smul]]
  exact uPerim_bndOfU t

/-- `u (t • bndOfU x) = Int.fract x` for `t > 0`. -/
private lemma u_smul_bndOfU_aux {t : ℝ} (ht : 0 < t) (x : ℝ) :
    u (t • bndOfU x) = Int.fract x := by
  rw [u_smul ht, u_bndOfU_aux]

theorem cuspInvInner_uqOf (v : Fin 5) (q : E4) (hq : q ∈ polarBox) :
    u (cuspInvInner v q).1 = Int.fract (uqOf v q) := by
  have hq0 : 0 < q 0 := by have h := hq.1; linarith
  simp only [cuspInvInner]
  set y : E2 := invY v !₂[q 2, q 3] with hy
  set uu : ℝ := (q 1 - 2 * π * (⟪cuspY v y, slope v⟫_ℝ / ‖slope v‖ ^ 2)) / (2 * π) with huu
  set b : ℝ := beta (cuspX v uu y) with hb
  set t : ℝ := (if q 0 ≤ rJ then q 0 / (2 * rJ)
      else 1 + (R0 - q 0 - Real.log b) / (2 * (Real.log b - Real.log sJ))) with ht
  have hconv : uqOf v q = uu := by rw [huu, uqOf, ← hy]; ring
  have ht_pos : 0 < t := by
    rw [ht]
    by_cases hc0 : q 0 ≤ rJ
    · rw [if_pos hc0]
      exact div_pos hq0 (by norm_num [rJ])
    · rw [if_neg hc0]
      have hbpos : 0 < b := by rw [hb]; exact beta_pos _
      have hblt : b < sJ := by rw [hb]; exact lt_of_le_of_lt (beta_le_max _) betaMax_lt_sJ
      have hloglt : Real.log b < Real.log sJ := Real.log_lt_log hbpos hblt
      have hgt : rJ < q 0 := not_le.mp hc0
      have hcollar := cuspInvRate_gt_half hloglt hgt
      linarith
  rw [hconv]
  exact u_smul_bndOfU_aux ht_pos uu

end Work.Cusp
