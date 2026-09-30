/-
# The height of the inverse outer chart

`cuspInvOuter v q` is the explicit inverse of the outer cusp chart `ThetaOuter v` of the filling
piece: from the UHS coordinates `q = (x, s)` it recovers the layer parameter `t = ‖p‖∞` from the
height `s = collarHeight t (β x)` and the angle from the `σ_v`-coordinate of `x`,
`(p,y) = (t • bndOfU (outerU v x), outerY v x)`, where

`t = 1 + (log s − log β(x)) / (2 (log β(x) − log s_J))`.

On the source box `cuspSource v c δ` (where `s` lies strictly between the ceiling `β(x)` and the
junction `s_J` and the `σ_v`-coordinate of `x` lies in `[0,1)`) this `t` really is the layer
parameter, so the UHS height `collarS v p y` of the reconstructed point is the input height:

  `collarS v (cuspInvOuter v q).1 (cuspInvOuter v q).2 = q 3`.

This file records that round-trip on the height coordinate.  It is the `s`-component of the
round-trip `ThetaOuter_cuspInvOuter`, and the input to the injectivity of the outer chart.
-/
import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.nrm_bnd
import Submission.Work.Cusp.nrm_bndOfU
import Submission.Work.Cusp.uPerim_bndOfU
import Submission.Work.Cusp.bnd_eq_self
import Submission.Work.Cusp.u_smul
import Submission.Work.Cusp.cuspX_outerU_outerY
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

open scoped Real InnerProductSpace

namespace Work.Cusp

/-- **The inverse of `collarHeight`.**  If `t` is the value that `collarHeight_inv` recovers from a
height `s` and a ceiling `b`, then plugging `t` back into `collarHeight` returns `s`.  This is the
round-trip companion of `collarHeight_inv`: writing `L = log s`, `B = log b`, `J = log s_J` and
`D = B − J ≠ 0`, one has `2t − 1 = (L − J)/D` and `2 − 2t = (B − L)/D`, so
`(2t−1)·B + (2−2t)·J = J + (L−J) = L`. -/
theorem collarHeight_of_log (b s : ℝ) (hs : 0 < s)
    (hne : Real.log b ≠ Real.log sJ) :
    collarHeight (1 + (Real.log s - Real.log b) / (2 * (Real.log b - Real.log sJ))) b = s := by
  have hD : Real.log b - Real.log sJ ≠ 0 := sub_ne_zero.mpr hne
  rw [collarHeight]
  have hexp : (2 * (1 + (Real.log s - Real.log b) / (2 * (Real.log b - Real.log sJ))) - 1)
        * Real.log b
      + (2 - 2 * (1 + (Real.log s - Real.log b) / (2 * (Real.log b - Real.log sJ))))
        * Real.log sJ = Real.log s := by
    field_simp
    ring
  rw [hexp, Real.exp_log hs]

theorem cuspInvOuter_height (v : Fin 5) (c : E3) (δ : ℝ) (q : E4) (hq : q ∈ cuspSource v c δ) :
    collarS v (cuspInvOuter v q).1 (cuspInvOuter v q).2 = q 3 := by
  -- ## Unpack the source hypothesis
  simp only [cuspSource, Set.mem_ofPred_eq] at hq
  obtain ⟨hbox, hbeta⟩ := hq
  simp only [cuspBox, Set.mem_ofPred_eq] at hbox
  obtain ⟨hside, hs1, hsJ, hu0, hu1⟩ := hbox
  -- `cuspInvOuter` writes the horizontal part as the literal `!₂[q 0, q 1, q 2]`, which is
  -- definitionally `xOf q`; transport the source bounds across that.
  have hbeta_lit : beta (!₂[q 0, q 1, q 2]) ≤ q 3 := by simpa only [xOf] using hbeta
  have hu0_lit : 0 ≤ outerU v (!₂[q 0, q 1, q 2]) := by simpa only [xOf] using hu0
  have hu1_lit : outerU v (!₂[q 0, q 1, q 2]) < 1 := by simpa only [xOf] using hu1
  -- ## Unfold the inverse chart and name its three ingredients
  simp only [cuspInvOuter]
  set X : E3 := !₂[q 0, q 1, q 2] with hX
  set B : ℝ := beta X with hB
  set T : ℝ := 1 + (Real.log (q 3) - Real.log B) / (2 * (Real.log B - Real.log sJ)) with hT
  -- ## The ceiling is positive and strictly below the junction
  have hBpos : 0 < B := by rw [hB]; exact beta_pos X
  have hBlt : B < sJ := by
    rw [hB]; exact lt_of_le_of_lt (beta_le_max X) betaMax_lt_sJ
  have hlogB_lt : Real.log B < Real.log sJ := Real.log_lt_log hBpos hBlt
  have hne : Real.log B ≠ Real.log sJ := ne_of_lt hlogB_lt
  have hq3pos : 0 < q 3 := lt_trans (by rw [s1]; norm_num) hs1
  -- ## The recovered layer parameter is positive: `T ∈ [1/2, 1]`
  have hq3le : Real.log (q 3) ≤ Real.log sJ := Real.log_le_log hq3pos (le_of_lt hsJ)
  have hTsub : T - 1 / 2
      = (Real.log (q 3) - Real.log sJ) / (2 * (Real.log B - Real.log sJ)) := by
    rw [hT]; field_simp; ring
  have hTge : (1 / 2 : ℝ) ≤ T := by
    have hratio : 0 ≤ (Real.log (q 3) - Real.log sJ) / (2 * (Real.log B - Real.log sJ)) := by
      rw [(neg_div_neg_eq (Real.log (q 3) - Real.log sJ)
        (2 * (Real.log B - Real.log sJ))).symm]
      exact div_nonneg (by linarith) (by linarith)
    linarith
  have hTpos : 0 < T := by linarith
  -- ## The two coordinates of the reconstructed point
  have hnrm : nrm (T • bndOfU (outerU v X)) = T := by
    rw [nrm_smul_aux, nrm_bndOfU, mul_one, abs_of_pos hTpos]
  have hw : u (T • bndOfU (outerU v X)) = outerU v X := by
    rw [u_smul hTpos]
    simp only [u]
    rw [bnd_eq_self (nrm_bndOfU (outerU v X)), uPerim_bndOfU]
    exact Int.fract_eq_self.mpr ⟨hu0_lit, hu1_lit⟩
  have hbeta2 : beta (cuspX v (u (T • bndOfU (outerU v X))) (outerY v X)) = B := by
    rw [hw, hB]
    exact congrArg beta (cuspX_outerU_outerY v X)
  -- ## Assemble
  rw [collarS, hnrm, hbeta2, hT]
  exact collarHeight_of_log B (q 3) hq3pos hne

end Work.Cusp
