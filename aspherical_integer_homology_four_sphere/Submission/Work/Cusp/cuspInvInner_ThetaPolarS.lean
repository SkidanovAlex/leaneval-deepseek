/-
# `cuspInvInner` is a left inverse of the shifted polar chart `ThetaPolarS`

`ThetaPolarS v c p y` is the polar chart of the `v`-th cusp with the angle coordinate read off the
`c`-shifted perimeter lift `uS c` (`Work.Cusp.Charts`), and `cuspInvInner v` is the explicit inverse
of the inner charts.  This file proves the round-trip identity for **all** `(p,y) : E2 × E2` (no
stratum hypothesis):

`cuspInvInner v (ThetaPolarS v c p y) = (p, y)`.

The recovery steps are those of the unshifted identity `cuspInvInner_ThetaPolar`: `w = wOf v y`
recovers `y = invY v w`, the angle coordinate recovers the *shifted* lift `uS c p`, and the radial
coordinate recovers `‖p‖∞`.  The only two places where the shift is felt are:

* the perimeter coordinate `u(p)` computed from `θ` is `uS c p`, not `u p`; the difference is an
  integer (`uS_lift`), and the point `bndOfU (uS c p) = bndOfU (u p + m) = bndOfU (u p) = bnd p`
  is unchanged (`bndOfU_add_int`), while the ceiling `β (cuspX v (uS c p) y)` used in the collar
  branch *is* unchanged because `cuspX v (u p + m) y = cuspX v (u p) y + m σ_v` and `σ_v` is a
  period of `β` (`beta_add_smul_slope`).
-/
import Mathlib
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.ThetaPolarS_continuousOn
import Submission.Work.Cusp.cuspInvInner_ThetaPolar
import Submission.Work.Cusp.invY_wOf
import Submission.Work.Cusp.nrm_bndOfU
import Submission.Work.Cusp.nrm_smul
import Submission.Work.Cusp.uPerim_bndOfU
import Submission.Work.Cusp.bndOfU_add_int
import Submission.Work.Cusp.u_smul
import Submission.Work.Cusp.beta_pos
import Submission.Work.Cusp.beta_le_max
import Submission.Work.Cusp.betaMax_lt_sJ
import Submission.Work.Cusp.radial_eq_inner
import Submission.Work.Cusp.radial_collar
import Submission.Work.Cusp.slope_ne_zero
import Submission.Work.Cusp.smul_bnd
import Submission.Work.Cusp.nrm_bnd
import Submission.Work.Cusp.bnd_eq_self
import Submission.Work.Cusp.collarHeight_half
import Submission.Work.Cusp.collarHeight_pos
import Submission.Work.Cusp.uS_lift
import Submission.Work.Cusp.beta_add_smul_slope

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.Cusp

open scoped Real InnerProductSpace

/-- Shifting the perimeter parameter by an integer moves `cuspX` by that integer multiple of the
slope `σ_v = κ_{v,1} + b_v κ_{v,2} + c_v κ_{v,3}`. -/
private lemma cuspX_add_int (v : Fin 5) (t : ℝ) (m : ℤ) (y : E2) :
    cuspX v (t + (m : ℝ)) y = cuspX v t y + (m : ℝ) • slope v := by
  rw [cuspX, cuspX, add_smul]
  abel

/-- **The ceiling is unchanged by an integer shift of the perimeter parameter.**  Shifting `u` by the
integer `m` moves `cuspX v u y` by `m σ_v` (`cuspX_add_int`), and `σ_v` is a period of `β`
(`beta_add_smul_slope`). -/
private lemma beta_cuspX_add_int (v : Fin 5) (t : ℝ) (m : ℤ) (y : E2) :
    beta (cuspX v (t + (m : ℝ)) y) = beta (cuspX v t y) := by
  rw [cuspX_add_int, beta_add_smul_slope]

/-- The radial coordinate of the (possibly shifted) polar chart with the collar branch made
explicit: `2 r_J ‖p‖∞` in the inner region `‖p‖∞ ≤ 1/2` and `R₀ − log (collarHeight ‖p‖∞ β)` in the
collar, where `collarS` has been unfolded. -/
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

/-- **The inverse of the inner (polar) chart is a left inverse of the shifted polar chart.**  Reading
the four coordinates `(r,θ,w₁,w₂) = ThetaPolarS v c p y` back: `w = wOf v y` recovers
`y = invY v w`, `θ` recovers the shifted lift `uS c p`, and `r` recovers `‖p‖∞` (`invT`), the
ceiling `β` of the collar branch being the same for the shifted and unshifted lifts
(`beta_cuspX_add_int`).  Finally `‖p‖∞ • bndOfU (uS c p) = ‖p‖∞ • bndOfU (u p) = ‖p‖∞ • bnd p = p`,
because `uS c p − u p ∈ ℤ` (`uS_lift`, `bndOfU_add_int`). -/
theorem cuspInvInner_ThetaPolarS (v : Fin 5) (c : ℝ) (p y : E2) :
    cuspInvInner v (ThetaPolarS v c p y) = (p, y) := by
  obtain ⟨m, hm⟩ := uS_lift c p
  have hw : (!₂[(ThetaPolarS v c p y).ofLp 2, (ThetaPolarS v c p y).ofLp 3] : E2)
      = wOf v y := by
    ext i; fin_cases i <;> simp [ThetaPolarS]
  have hy : invY v !₂[(ThetaPolarS v c p y).ofLp 2, (ThetaPolarS v c p y).ofLp 3] = y := by
    rw [hw, invY_wOf]
  have h2 : (cuspInvInner v (ThetaPolarS v c p y)).2 = y := by
    dsimp only [cuspInvInner]; exact hy
  refine Prod.ext ?_ h2
  dsimp only [cuspInvInner]
  rw [show (ThetaPolarS v c p y).ofLp 0 = radial v p y from by simp [ThetaPolarS],
      show (ThetaPolarS v c p y).ofLp 1
        = 2 * π * uS c p + 2 * π * inner ℝ (cuspY v y) (slope v) / ‖slope v‖ ^ 2 from by
          simp [ThetaPolarS],
      hw, invY_wOf]
  have huu : (2 * π * uS c p + 2 * π * inner ℝ (cuspY v y) (slope v) / ‖slope v‖ ^ 2
      - 2 * π * (inner ℝ (cuspY v y) (slope v) / ‖slope v‖ ^ 2)) / (2 * π) = uS c p := by
    rw [mul_div_assoc]
    rw [add_sub_cancel_right]
    rw [div_eq_iff (ne_of_gt (by positivity : (0 : ℝ) < 2 * π))]
    ring
  rw [huu]
  have hb_eq : beta (cuspX v (uS c p) y) = beta (cuspX v (u p) y) := by
    rw [hm]; exact beta_cuspX_add_int v (u p) m y
  have hBpos : 0 < beta (cuspX v (u p) y) := beta_pos _
  have hBlt : beta (cuspX v (u p) y) < sJ := lt_of_le_of_lt (beta_le_max _) betaMax_lt_sJ
  rw [hb_eq, radial_eq_collar v p y]
  rw [invT (nrm p) (beta (cuspX v (u p) y)) hBpos hBlt]
  rcases eq_or_ne p 0 with hp | hp
  · subst hp
    simp [nrm]
  · have hbnd : bndOfU (uS c p) = bnd p := by
      rw [hm, bndOfU_add_int]
      exact nrmu_bndOfU_uPerim (nrm_bnd hp)
    rw [hbnd, smul_bnd]

end Work.Cusp
