/-
# The outer cusp chart `Θ_v` inverts `cuspInvOuter` on the cusp source

`cuspInvOuter v q` (`Work.Cusp.Basic`) is the explicit inverse of the outer chart `ThetaOuter v`:
given a UHS coordinate `q = (x,s)` with `x = xOf q`, it recovers

* the layer parameter `t = ‖p‖∞` from the height `s = collarHeight t (β x)` by inverting the
  exponential `collarHeight t b = exp ((2t-1) log b + (2-2t) log s_J)`, i.e.
  `t = 1 + (log s - log b)/(2 (log b - log s_J))`;
* the direction from the meridian coordinate `outerU v x` of `x` through `bndOfU`;
* the phase `y = outerY v x` from the `κ_{v,2},κ_{v,3}` coordinates of `x`.

This file proves that on the *cusp source* `cuspSource v c δ` (the part of the cusp box lying above
the ceiling `s = β x`, in which the height satisfies `β x ≤ s < s_J`) the round trip returns the
point: `ThetaOuter v (cuspInvOuter v q).1 (cuspInvOuter v q).2 = q`.

The hypotheses are used exactly as follows.

* `0 ≤ outerU v x` and `outerU v x < 1` (from `cuspBox`) make the fractional part in `bndOfU`
  harmless: `Int.fract (outerU v x) = outerU v x`, so the perimeter parameter `u` of the recovered
  layer point is again `outerU v x`.
* `β x ≤ q 3` (the defining extra condition of `cuspSource`) together with `q 3 < s_J` (from
  `cuspBox`) gives `β x < s_J`, so the denominator `2 (log β x - log s_J)` is nonzero and the
  height inverse is legitimate; and it gives `1/2 ≤ t ≤ 1`, in particular `t > 0`, so that the
  radial projection `bnd (t • bndOfU u)` is `bndOfU u` again.

The `x`-part of `Θ_v` is then `cuspX v (outerU v x) (outerY v x) = x` (`cuspX_outerU_outerY`) and
the `s`-part is `collarHeight t (β x) = q 3` by the logarithm computation.
-/
import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.cuspX_outerU_outerY
import Submission.Work.Cusp.uPerim_bndOfU
import Submission.Work.Cusp.nrm_bndOfU
import Submission.Work.Cusp.nrm_smul
import Submission.Work.Cusp.beta_pos

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.Cusp

open scoped Real InnerProductSpace

/-! ### Two one-dimensional computations -/

/-- **The height inverse.**  `t = 1 + (log s - log b) / (2 (log b - log s_J))` is the layer
parameter whose collar height is `s`:

`(2t-1) log b + (2-2t) log s_J = (log s - log b)/(log b - log s_J) · (log b - log s_J) = log s`,

so `collarHeight t b = exp (log s) = s`, provided `b ≠ s_J` (the denominator is nonzero) and
`s > 0`. -/
private lemma collarHeight_of_log (t b s : ℝ) (_hb : 0 < b) (hs : 0 < s)
    (hd : Real.log b - Real.log sJ ≠ 0)
    (ht : t = 1 + (Real.log s - Real.log b) / (2 * (Real.log b - Real.log sJ))) :
    collarHeight t b = s := by
  have harg : (2 * t - 1) * Real.log b + (2 - 2 * t) * Real.log sJ = Real.log s := by
    rw [ht]; field_simp; ring
  rw [collarHeight, harg, Real.exp_log hs]

/-- **The layer parameter is at least `1/2`.**  For `0 < b ≤ s < s_J` the parameter
`t = 1 + (log s - log b)/(2 (log b - log s_J))` satisfies `t ≥ 1/2`; equivalently `log s ≤ log s_J`
is the statement `t - 1/2 = (log s_J - log s)/(2 (log s_J - log b)) ≥ 0`. -/
private lemma one_half_le_collarInv (b s : ℝ) (hb : 0 < b) (hs : 0 < s) (hbs : b ≤ s)
    (hsj : s < sJ) :
    1 / 2 ≤ 1 + (Real.log s - Real.log b) / (2 * (Real.log b - Real.log sJ)) := by
  have hb_lt_sJ : b < sJ := lt_of_le_of_lt hbs hsj
  have hlog_le : Real.log s ≤ Real.log sJ := Real.log_le_log hs (le_of_lt hsj)
  have hlogb_le : Real.log b ≤ Real.log s := Real.log_le_log hb hbs
  have hD2 : 2 * (Real.log b - Real.log sJ) < 0 := by
    have := Real.log_lt_log hb hb_lt_sJ
    linarith
  have key : -(1 / 2 : ℝ) ≤ (Real.log s - Real.log b) / (2 * (Real.log b - Real.log sJ)) := by
    rw [le_div_iff_of_neg hD2]
    linarith
  linarith

/-! ### The round trip -/

theorem ThetaOuter_cuspInvOuter (v : Fin 5) (c : E3) (δ : ℝ) (q : E4)
    (hq : q ∈ cuspSource v c δ) : ThetaOuter v (cuspInvOuter v q).1 (cuspInvOuter v q).2 = q := by
  -- the two halves of the hypothesis: the box and the ceiling condition
  obtain ⟨hbox, hbeta_le⟩ := hq
  obtain ⟨-, hs1, hq3_lt, hu0, hu1⟩ := hbox
  -- the components of the inverse
  set x : E3 := xOf q with hx
  set b : ℝ := beta x with hb
  set uu : ℝ := outerU v x with huu
  set y : E2 := outerY v x with hy
  set t : ℝ := 1 + (Real.log (q 3) - Real.log b) / (2 * (Real.log b - Real.log sJ)) with ht
  have hs1pos : 0 < s1 := by rw [s1]; norm_num
  have hq3pos : 0 < q 3 := lt_trans hs1pos hs1
  have hbpos : 0 < b := by rw [hb]; exact beta_pos x
  have hb_le : b ≤ q 3 := by rw [hb, hx]; exact hbeta_le
  have hb_lt_sJ : b < sJ := lt_of_le_of_lt hb_le hq3_lt
  have hlog_ne : Real.log b - Real.log sJ ≠ 0 :=
    sub_ne_zero.mpr (ne_of_lt (Real.log_lt_log hbpos hb_lt_sJ))
  have ht_ge : 1 / 2 ≤ t := by
    rw [ht]
    exact one_half_le_collarInv b (q 3) hbpos hq3pos hb_le hq3_lt
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht_ge
  -- `cuspInvOuter v q` is `(t • bndOfU uu, y)`
  have hcinv : cuspInvOuter v q = (t • bndOfU uu, y) := by
    rw [ht, hb, huu, hy, hx]
    rfl
  -- the recovered perimeter parameter is in `[0,1)`, hence `Int.fract uu = uu`
  have huu_mem : uu ∈ Set.Ico 0 1 := by
    refine ⟨?_, ?_⟩ <;> rw [huu, hx] <;> assumption
  -- the layer point `t • bndOfU uu` has perimeter parameter `uu`
  have hup : u (t • bndOfU uu) = uu := by
    have hbnd : bnd (t • bndOfU uu) = bndOfU uu := by
      rw [bnd, nrm_smul, nrm_bndOfU, mul_one, abs_of_pos htpos, smul_smul,
        inv_mul_cancel₀ (ne_of_gt htpos), one_smul]
    rw [u, hbnd, uPerim_bndOfU, (Int.fract_eq_self).mpr huu_mem]
  -- the horizontal part of `Θ_v` recovers `x`
  have hcX : cuspX v (u (t • bndOfU uu)) y = xOf q := by
    rw [hup, huu, hy, ← hx]
    exact cuspX_outerU_outerY v x
  -- the sup norm of the layer point is `t`
  have hnrm : nrm (t • bndOfU uu) = t := by
    rw [nrm_smul, nrm_bndOfU, mul_one, abs_of_pos htpos]
  -- the height of `Θ_v` recovers `q 3`
  have hcol : collarS v (t • bndOfU uu) y = q 3 := by
    rw [collarS, hnrm, hcX, ht, ← hx, ← hb]
    exact collarHeight_of_log _ b (q 3) hbpos hq3pos hlog_ne rfl
  rw [hcinv]
  ext i
  fin_cases i <;> simp [ThetaOuter, hcX, hcol, xOf]

end Work.Cusp
