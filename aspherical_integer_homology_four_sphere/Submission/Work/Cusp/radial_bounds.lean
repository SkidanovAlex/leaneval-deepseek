import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.radial_eq_inner
import Submission.Work.Cusp.radial_collar
import Submission.Work.Cusp.beta_pos
import Submission.Work.Cusp.beta_le_max
import Submission.Work.Cusp.betaMax_lt_sJ
import Submission.Work.Cusp.nrm_nonneg

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Bounds for the metric radial coordinate `r` of the filling piece

`radial v p y` (`Work.Cusp.Basic`) is the metric radial coordinate of the filling of the `v`-th
cusp, in polar coordinates `(r,θ,w₁,w₂)`:

* in the inner region `‖p‖∞ ≤ 1/2` it is the linear function `r = 2 r_J ‖p‖∞`, ranging over
  `[0, r_J]` with `r_J = 3`;
* in the collar `1/2 < ‖p‖∞` it is the UHS value `r = R₀ − log (collarS v p y)`, where
  `collarS v p y = collarHeight ‖p‖∞ (β (cuspX v (u p) y))` is the UHS height of the outer chart.

Here we prove the two bounds that make this coordinate usable:

* `0 ≤ radial v p y` for **every** `p : E2` (no assumption `p ∈ Sq`);
* `radial v p y ≤ r_J` on the closed inner disk `‖p‖∞ ≤ 1/2`, i.e. the whole inner chart sits in
  the unit ball `r ≤ r_J` of the warped metric;
* `r_J < radial v p y` on the open collar `1/2 < ‖p‖∞`, i.e. the two strata only meet at the
  junction layer `‖p‖∞ = 1/2`, where both equal `r_J`.

The collar bound is the analytic heart: it says that the collar height stays below the junction
height `s_J`.  Writing `E = (2t−1) log b + (2−2t) log s_J` for the exponent of `collarHeight t b`
(with `t = ‖p‖∞` and `b = β (cuspX v (u p) y)`) one has the exact identity

`E − log s_J = (2t−1) (log b − log s_J)`,

so the sign is decided by the *single* comparison `log b < log s_J`, i.e. `β < s_J`, uniformly in
`t` as long as `1/2 < t`.  Positivity of `β` (`beta_pos`) supplies `log b`, and `β ≤ βMax < s_J`
(`beta_le_max`, `betaMax_lt_sJ`) supplies the strict comparison.
-/

namespace Work.Cusp

/-- **The collar height is strictly below the junction height `s_J`.**

Writing `E = (2t−1) log b + (2−2t) log s_J` for the exponent of `collarHeight t b`, one has
`E − log s_J = (2t−1)(log b − log s_J)`, which is negative as soon as `t > 1/2` and `b < s_J`
(no lower bound on `b` beyond positivity is needed to make `log b` meaningful). -/
theorem collarHeight_lt_sJ {t b : ℝ} (ht : 1 / 2 < t) (hb : 0 < b) (hbs : b < sJ) :
    collarHeight t b < sJ := by
  have hsJpos : 0 < sJ := by rw [sJ]; exact Real.exp_pos _
  have hlog : Real.log b < Real.log sJ := Real.log_lt_log hb hbs
  have hE : (2 * t - 1) * Real.log b + (2 - 2 * t) * Real.log sJ < Real.log sJ := by
    have hkey : (2 * t - 1) * Real.log b + (2 - 2 * t) * Real.log sJ - Real.log sJ
        = (2 * t - 1) * (Real.log b - Real.log sJ) := by ring
    have hprod : (2 * t - 1) * (Real.log b - Real.log sJ) < 0 :=
      mul_neg_of_pos_of_neg (by linarith) (by linarith)
    linarith
  rw [collarHeight]
  calc Real.exp ((2 * t - 1) * Real.log b + (2 - 2 * t) * Real.log sJ)
      < Real.exp (Real.log sJ) := Real.exp_lt_exp.mpr hE
    _ = sJ := Real.exp_log hsJpos

/-- **The collar height is at most the junction height `s_J`** (non-strict form of
`collarHeight_lt_sJ`, valid for `t ≥ 1/2`). -/
theorem collarHeight_le_sJ {t b : ℝ} (ht : 1 / 2 ≤ t) (hb : 0 < b) (hbs : b < sJ) :
    collarHeight t b ≤ sJ := by
  have hsJpos : 0 < sJ := by rw [sJ]; exact Real.exp_pos _
  have hlog : Real.log b < Real.log sJ := Real.log_lt_log hb hbs
  have hE : (2 * t - 1) * Real.log b + (2 - 2 * t) * Real.log sJ ≤ Real.log sJ := by
    have hkey : (2 * t - 1) * Real.log b + (2 - 2 * t) * Real.log sJ - Real.log sJ
        = (2 * t - 1) * (Real.log b - Real.log sJ) := by ring
    have hprod : (2 * t - 1) * (Real.log b - Real.log sJ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    linarith
  rw [collarHeight]
  calc Real.exp ((2 * t - 1) * Real.log b + (2 - 2 * t) * Real.log sJ)
      ≤ Real.exp (Real.log sJ) := Real.exp_le_exp.mpr hE
    _ = sJ := Real.exp_log hsJpos

/-- **The height of the outer chart is at most the junction height.**  Immediate from
`collarHeight_le_sJ` and the ceiling bounds `0 < β ≤ βMax < s_J`. -/
theorem collarS_le_sJ (v : Fin 5) (p y : E2) (h : 1 / 2 ≤ nrm p) :
    collarS v p y ≤ sJ := by
  have hb : 0 < beta (cuspX v (u p) y) := beta_pos _
  have hbs : beta (cuspX v (u p) y) < sJ := lt_of_le_of_lt (beta_le_max _) betaMax_lt_sJ
  show collarHeight (nrm p) (beta (cuspX v (u p) y)) ≤ sJ
  exact collarHeight_le_sJ h hb hbs

/-- **The height of the outer chart is strictly below the junction height** on the open collar. -/
theorem collarS_lt_sJ (v : Fin 5) (p y : E2) (h : 1 / 2 < nrm p) :
    collarS v p y < sJ := by
  have hb : 0 < beta (cuspX v (u p) y) := beta_pos _
  have hbs : beta (cuspX v (u p) y) < sJ := lt_of_le_of_lt (beta_le_max _) betaMax_lt_sJ
  show collarHeight (nrm p) (beta (cuspX v (u p) y)) < sJ
  exact collarHeight_lt_sJ h hb hbs

/-- The logarithm of the junction height: `log s_J = 1/2`, since `s_J = e^{1/2}`. -/
theorem log_sJ : Real.log sJ = 1 / 2 := by
  rw [sJ]; exact Real.log_exp (1 / 2)

/-- **In the collar the radial coordinate exceeds the junction radius `r_J`.**

For `1/2 < ‖p‖∞` the outer chart has height `collarS v p y < s_J`, so
`radial = R₀ − log (collarS v p y) > R₀ − log s_J = 7/2 − 1/2 = 3 = r_J`. -/
theorem radial_gt_rJ (v : Fin 5) (p y : E2) (h : 1 / 2 < nrm p) :
    rJ < radial v p y := by
  have hlt : collarS v p y < sJ := collarS_lt_sJ v p y h
  have hc0 : 0 < collarS v p y := by
    show 0 < collarHeight (nrm p) (beta (cuspX v (u p) y)); exact Real.exp_pos _
  have hlogs : Real.log (collarS v p y) < 1 / 2 := by
    rw [← log_sJ]; exact Real.log_lt_log hc0 hlt
  rw [radial_collar v p y (le_of_lt h)]
  unfold R0 rJ
  linarith

/-- **Bounds for the metric radial coordinate of the filling piece.**

For all `p y : E2` (no membership hypothesis on `p`): the radial coordinate is nonnegative, it is
at most the junction radius `r_J` on the closed inner disk `‖p‖∞ ≤ 1/2`, and strictly larger than
`r_J` on the open collar `1/2 < ‖p‖∞`. -/
theorem radial_bounds (v : Fin 5) (p y : Work.Cusp.E2) :
    0 ≤ Work.Cusp.radial v p y ∧ (Work.Cusp.nrm p ≤ 1 / 2 → Work.Cusp.radial v p y ≤ Work.Cusp.rJ) ∧
      (1 / 2 < Work.Cusp.nrm p → Work.Cusp.rJ < Work.Cusp.radial v p y) := by
  rcases lt_or_ge (1 / 2 : ℝ) (nrm p) with hgt | hle
  · -- collar `1/2 < ‖p‖∞`: `r_J < radial`, so `radial > 0`, and the inner layer is empty
    have hgt' : rJ < radial v p y := radial_gt_rJ v p y hgt
    have hrJpos : 0 < rJ := by unfold rJ; norm_num
    exact ⟨le_of_lt (lt_trans hrJpos hgt'), (fun h => absurd h (not_le.mpr hgt)), fun _ => hgt'⟩
  · -- inner region `‖p‖∞ ≤ 1/2`: `radial = 2 r_J ‖p‖∞`, a nonnegative multiple of `‖p‖∞`
    have hr : radial v p y = 2 * rJ * nrm p := radial_eq_inner v p y hle
    have hn : 0 ≤ nrm p := nrm_nonneg p
    refine ⟨?_, ?_, ?_⟩
    · rw [hr]; unfold rJ; linarith
    · intro _; rw [hr]; unfold rJ; linarith
    · intro h; exact absurd h (not_lt.mpr hle)

end Work.Cusp
