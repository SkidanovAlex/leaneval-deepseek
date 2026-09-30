/-
# `cuspInvInner` is a left inverse of the polar chart `ThetaPolar`

`ThetaPolar v p y = (r, θ, w₁, w₂)` is the inner (polar) chart of the `v`-th cusp
(`Work.Cusp.Basic`) and `cuspInvInner v` is its explicit inverse: it recovers `y = invY v (w)`
from `w`, the perimeter parameter `u(p)` from `θ`, and the layer parameter `‖p‖∞` from `r`.

This file proves the round-trip identity `cuspInvInner v (ThetaPolar v p y) = (p, y)` for **all**
`(p,y) : E2 × E2` (no stratum hypothesis needed): the recovery steps are exact everywhere, only
the final radial projection `p = ‖p‖∞ • bnd p` being trivial at the core point `p = 0`.
-/
import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.invY_wOf
import Submission.Work.Cusp.nrm_u_injOn
import Submission.Work.Cusp.collarHeight_half
import Submission.Work.Cusp.collarHeight_pos
import Submission.Work.Cusp.collarHeight_strictAntiOn
import Submission.Work.Cusp.beta_pos
import Submission.Work.Cusp.beta_le_max
import Submission.Work.Cusp.betaMax_lt_sJ

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.Cusp

open scoped Real InnerProductSpace

/-- The radial coordinate of the polar chart with the ceiling made explicit: `2 r_J ‖p‖∞` in the
inner region `‖p‖∞ ≤ 1/2` and `R₀ − log (collarHeight ‖p‖∞ β)` in the collar, where `collarS` has
been unfolded. -/
private lemma radial_eq_collar (v : Fin 5) (p y : E2) :
    radial v p y = (if nrm p ≤ 1/2 then 2 * rJ * nrm p
      else R0 - Real.log (collarHeight (nrm p) (beta (cuspX v (u p) y)))) := by
  rw [radial, collarS]

/-- **The layer parameter is recovered from the radial coordinate.**  For a ceiling value
`b ∈ (0, s_J)`, inverting the two-branch profile

`f(t) = if t ≤ 1/2 then 2 r_J t else R₀ − log (collarHeight t b)`

by the two-branch inverse of `cuspInvInner` returns the layer parameter `t`.  The junction
`t = 1/2` maps to `r = r_J`, so the selection criterion `f t ≤ r_J` picks the correct branch on
both sides, and above the junction the logarithm identity
`log (collarHeight t b) = (2t−1) log b + (2−2t) log s_J` collapses the expression to `t`. -/
private lemma invT (t b : ℝ) (hb : 0 < b) (hb' : b < sJ) :
    (if (if t ≤ 1/2 then 2 * rJ * t else R0 - Real.log (collarHeight t b)) ≤ rJ
      then (if t ≤ 1/2 then 2 * rJ * t else R0 - Real.log (collarHeight t b)) / (2 * rJ)
      else 1 + (R0 - (if t ≤ 1/2 then 2 * rJ * t else R0 - Real.log (collarHeight t b))
            - Real.log b) / (2 * (Real.log b - Real.log sJ))) = t := by
  have hsJlog : Real.log sJ = 1 / 2 := by rw [sJ, Real.log_exp]
  have hR0 : R0 - 1 / 2 = rJ := by norm_num [R0, rJ]
  have hlog_lt : Real.log b < Real.log sJ := Real.log_lt_log hb hb'
  have hlog_ne : Real.log b - Real.log sJ ≠ 0 := sub_ne_zero.mpr (ne_of_lt hlog_lt)
  by_cases ht : t ≤ 1/2
  · have hrJpos : (0 : ℝ) < 2 * rJ := by norm_num [rJ]
    have hrJne : (2 : ℝ) * rJ ≠ 0 := ne_of_gt hrJpos
    have hle : 2 * rJ * t ≤ rJ := by
      calc 2 * rJ * t = (2 * rJ) * t := by ring
        _ ≤ (2 * rJ) * (1 / 2) := mul_le_mul_of_nonneg_left ht (by positivity)
        _ = rJ := by ring
    rw [ite_eq_left ht, ite_eq_left hle]
    rw [show 2 * rJ * t = t * (2 * rJ) from by ring, mul_div_cancel_right₀ t hrJne]
  · have ht' : 1 / 2 < t := not_le.mp ht
    have hcH : collarHeight t b < sJ := by
      have h' := collarHeight_strictAntiOn b hb hb' (Set.mem_univ (1 / 2)) (Set.mem_univ t) ht'
      simp only at h'
      rwa [collarHeight_half] at h'
    have hlog_cH : Real.log (collarHeight t b) < 1 / 2 := by
      have h' := Real.log_lt_log (collarHeight_pos t b hb) hcH
      rwa [hsJlog] at h'
    have hgt : rJ < R0 - Real.log (collarHeight t b) := by linarith [hlog_cH, hR0]
    rw [ite_eq_right ht, ite_eq_right (not_le.mpr hgt)]
    rw [show R0 - (R0 - Real.log (collarHeight t b)) - Real.log b
          = Real.log (collarHeight t b) - Real.log b from by ring]
    rw [show Real.log (collarHeight t b)
          = (2 * t - 1) * Real.log b + (2 - 2 * t) * Real.log sJ from by
        rw [collarHeight, Real.log_exp]]
    rw [show (2 * t - 1) * Real.log b + (2 - 2 * t) * Real.log sJ - Real.log b
          = -(2 - 2 * t) * (Real.log b - Real.log sJ) from by ring]
    rw [mul_div_mul_right _ _ hlog_ne]
    ring

/-- **The inverse of the inner (polar) chart is a left inverse of the chart.**  Reading the four
polar coordinates `(r,θ,w₁,w₂) = ThetaPolar v p y` back: `w = wOf v y` recovers `y = invY v w`,
`θ` recovers `u p`, `r` recovers `‖p‖∞` (`invT`), and `‖p‖∞ • bndOfU (u p) = ‖p‖∞ • bnd p = p`
(`nrmu_bndOfU_uPerim`, `smul_bnd`). -/
theorem cuspInvInner_ThetaPolar (v : Fin 5) (p y : E2) :
    cuspInvInner v (ThetaPolar v p y) = (p, y) := by
  have hy : invY v !₂[(ThetaPolar v p y).ofLp 2, (ThetaPolar v p y).ofLp 3] = y := by
    rw [show (!₂[(ThetaPolar v p y).ofLp 2, (ThetaPolar v p y).ofLp 3] : E2) = wOf v y from by
          ext i; fin_cases i <;> simp [ThetaPolar],
        invY_wOf]
  have h2 : (cuspInvInner v (ThetaPolar v p y)).2 = y := by
    dsimp only [cuspInvInner]; exact hy
  refine Prod.ext ?_ h2
  dsimp only [cuspInvInner]
  rw [show (ThetaPolar v p y).ofLp 0 = radial v p y from by simp [ThetaPolar],
      show (ThetaPolar v p y).ofLp 1 = thetaAng v p y from by simp [ThetaPolar],
      show (!₂[(ThetaPolar v p y).ofLp 2, (ThetaPolar v p y).ofLp 3] : E2) = wOf v y from by
          ext i; fin_cases i <;> simp [ThetaPolar],
      invY_wOf]
  have huu : (thetaAng v p y - 2 * π * (⟪cuspY v y, slope v⟫_ℝ / ‖slope v‖ ^ 2)) / (2 * π)
      = u p := by
    rw [thetaAng]
    field_simp
    ring
  rw [huu]
  have hBpos : 0 < beta (cuspX v (u p) y) := beta_pos _
  have hBlt : beta (cuspX v (u p) y) < sJ := lt_of_le_of_lt (beta_le_max _) betaMax_lt_sJ
  rw [show radial v p y = (if nrm p ≤ 1/2 then 2 * rJ * nrm p
        else R0 - Real.log (collarHeight (nrm p) (beta (cuspX v (u p) y)))) from
      radial_eq_collar v p y]
  rw [invT (nrm p) (beta (cuspX v (u p) y)) hBpos hBlt]
  rcases eq_or_ne p 0 with hp | hp
  · subst hp
    simp [nrm]
  · rw [show bndOfU (u p) = bnd p from nrmu_bndOfU_uPerim (nrm_bnd hp)]
    exact smul_bnd p

end Work.Cusp
