import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.BoseBogFS.phiC_du_bound
import Submission.Work.BoseBogFS.phiC_dv_bound
import Submission.Work.BoseBogFS.phiC_hasDerivAt_u
import Submission.Work.BoseBogFS.phiC_hasDerivAt_v
import Submission.Work.BoseBogFS.phiC_rpart_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.phiC_osc_le` — the master oscillation bound of the clean bracket

For the clean bracket `phiC u v r = v²/(u+v+√(u²+2uv)) − v²/(2r²)` (the scaled clean summand
`psiSc`, see `Work.BoseBogFS.phiC_defs`) this module proves the two-point oscillation bound:
for `u_lo ≤ u_· ≤ u_hi`, `v_lo ≤ v_· ≤ v_hi`, `r_lo ≤ r_· ≤ r_hi` with `0 < u_lo`,
`u_lo² + 2u_lo v_lo > 0`, `u_hi ≤ r_lo²`,

  `|phiC u_n v_n r_n − phiC u_x v_x r_x|`
  `  ≤ 2·(M²/(S_lo D_lo))·(u_hi−u_lo) + 2·B·(v_hi−v_lo) + M²·(1/r_lo² − 1/r_hi²)`,

where `M = max |v_lo| |v_hi|`, `D_lo = √(u_lo²+2u_lo v_lo)`, `S_lo = u_lo + v_lo + D_lo` and

  `B = M(2(r_hi²−u_lo)+2M)/(r_lo² S_lo) + M²(1 + u_hi/D_lo)/S_lo²`.

## Proof

The bracket is handled coordinate by coordinate.  Writing
`Δ = [phiC u_n v_n r_n − phiC u_x v_n r_n] + [phiC u_x v_n r_n − phiC u_x v_n r_x]
      + [phiC u_x v_n r_x − phiC u_x v_x r_x]`, the three terms are bounded by

* (`u`-piece, `Work.BoseBogFS.phiC_hasDerivAt_u` + `Work.BoseBogFS.phiC_du_bound`)
  `|∂_u phiC| = v²/(S·D) ≤ M²/(S_lo D_lo)`, via the mean value theorem on `[u_n,u_x]`;
* (`r`-piece, `Work.BoseBogFS.phiC_rpart_le`) the exact `1/r²`-difference;
* (`v`-piece, `Work.BoseBogFS.phiC_hasDerivAt_v` + `Work.BoseBogFS.phiC_dv_bound`)
  the pointwise bound `|∂_v phiC| ≤ M(2(r_hi²−u_lo)+3M)/(r_lo²S_lo) + M²(1+u_hi/D_lo)/S_lo²`,
  via the mean value theorem on `[min v_n v_x, max v_n v_x]`.

The `v`-derivative bound loses a factor `≤ 2` against the bracket `B` above
(`2(r_hi²−u_lo)+3M ≤ 4(r_hi²−u_lo)+4M`), and the `u`-piece is `≤ 2` times its coefficient;
this is exactly the slack in the stated right-hand side.
-/

namespace Work.BoseBogFS

open scoped Real Topology BigOperators

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## The two one-dimensional oscillation bounds -/

/-- The `u`-direction oscillation of `phiC` at fixed `v` (and arbitrary `r`). -/
private lemma phiC_u_osc {u_lo u_hi v_lo v_hi u_n u_x v r : ℝ}
    (hul : 0 < u_lo) (hulh : u_lo ≤ u_hi) (hW : 0 < u_lo ^ 2 + 2 * u_lo * v_lo)
    (hun : u_lo ≤ u_n) (hun2 : u_n ≤ u_hi) (hux : u_lo ≤ u_x) (hux2 : u_x ≤ u_hi)
    (hvn : v_lo ≤ v) (hvn2 : v ≤ v_hi) :
    |phiC u_n v r - phiC u_x v r|
      ≤ (max |v_lo| |v_hi|) ^ 2
          / ((u_lo + v_lo + Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo))
              * Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo)) * (u_hi - u_lo) := by
  have hden : 0 < (u_lo + v_lo + Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo))
      * Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo) := by
    have h1 : 0 < u_lo + v_lo := by nlinarith [hul, hW]
    have h2 : 0 < Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo) := Real.sqrt_pos.mpr hW
    exact mul_pos (by linarith) h2
  have hZ0 : 0 ≤ (max |v_lo| |v_hi|) ^ 2
      / ((u_lo + v_lo + Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo))
          * Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo)) := div_nonneg (sq_nonneg _) hden.le
  have huvl : 0 < u_lo + 2 * v_lo := by nlinarith [hul, hW]
  have hbd : ∀ w ∈ Set.Icc u_lo u_hi,
      ‖(-(v ^ 2 / ((w + v + Real.sqrt (w ^ 2 + 2 * w * v))
        * Real.sqrt (w ^ 2 + 2 * w * v))) : ℝ)‖
        ≤ (max |v_lo| |v_hi|) ^ 2
          / ((u_lo + v_lo + Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo))
              * Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo)) := by
    intro w hw
    rw [Real.norm_eq_abs, abs_neg]
    exact phiC_du_bound (u_hi := u_hi) hul hW hw.1 hvn hvn2
  have hdv : ∀ w ∈ Set.Icc u_lo u_hi, HasDerivWithinAt (fun w : ℝ => phiC w v r)
      (-(v ^ 2 / ((w + v + Real.sqrt (w ^ 2 + 2 * w * v))
        * Real.sqrt (w ^ 2 + 2 * w * v)))) (Set.Icc u_lo u_hi) w := by
    intro w hw
    have h1 : 0 < w := lt_of_lt_of_le hul hw.1
    have h2 : 0 < w + 2 * v := by linarith [hw.1, hvn, huvl]
    exact (phiC_hasDerivAt_u h1 h2).hasDerivWithinAt
  rcases le_total u_n u_x with hle | hle
  · have hsub : Set.Icc u_n u_x ⊆ Set.Icc u_lo u_hi := Set.Icc_subset_Icc hun hux2
    have hder' : ∀ w ∈ Set.Icc u_n u_x, HasDerivWithinAt (fun w : ℝ => phiC w v r)
        (-(v ^ 2 / ((w + v + Real.sqrt (w ^ 2 + 2 * w * v))
          * Real.sqrt (w ^ 2 + 2 * w * v)))) (Set.Icc u_n u_x) w :=
      fun w hw => (hdv w (hsub hw)).mono hsub
    have hbd' : ∀ w ∈ Set.Ico u_n u_x,
        ‖(-(v ^ 2 / ((w + v + Real.sqrt (w ^ 2 + 2 * w * v))
          * Real.sqrt (w ^ 2 + 2 * w * v))) : ℝ)‖
          ≤ (max |v_lo| |v_hi|) ^ 2
          / ((u_lo + v_lo + Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo))
              * Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo)) :=
      fun w hw => hbd w (hsub (Set.Ico_subset_Icc_self hw))
    have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' hder' hbd'
    have hx := hmvt u_x (Set.right_mem_Icc.mpr hle)
    rw [Real.norm_eq_abs] at hx
    have h1 : |phiC u_n v r - phiC u_x v r| ≤ (max |v_lo| |v_hi|) ^ 2
        / ((u_lo + v_lo + Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo))
            * Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo)) * (u_x - u_n) := by
      rw [abs_sub_comm]
      exact hx
    exact le_trans h1 (mul_le_mul_of_nonneg_left (by linarith) hZ0)
  · have hsub : Set.Icc u_x u_n ⊆ Set.Icc u_lo u_hi := Set.Icc_subset_Icc hux hun2
    have hder' : ∀ w ∈ Set.Icc u_x u_n, HasDerivWithinAt (fun w : ℝ => phiC w v r)
        (-(v ^ 2 / ((w + v + Real.sqrt (w ^ 2 + 2 * w * v))
          * Real.sqrt (w ^ 2 + 2 * w * v)))) (Set.Icc u_x u_n) w :=
      fun w hw => (hdv w (hsub hw)).mono hsub
    have hbd' : ∀ w ∈ Set.Ico u_x u_n,
        ‖(-(v ^ 2 / ((w + v + Real.sqrt (w ^ 2 + 2 * w * v))
          * Real.sqrt (w ^ 2 + 2 * w * v))) : ℝ)‖
          ≤ (max |v_lo| |v_hi|) ^ 2
          / ((u_lo + v_lo + Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo))
              * Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo)) :=
      fun w hw => hbd w (hsub (Set.Ico_subset_Icc_self hw))
    have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' hder' hbd'
    have hx := hmvt u_n (Set.right_mem_Icc.mpr hle)
    rw [Real.norm_eq_abs] at hx
    exact le_trans hx (mul_le_mul_of_nonneg_left (by linarith) hZ0)

/-- The `v`-direction oscillation of `phiC` at fixed `u ∈ [u_lo,u_hi]` and `r ∈ [r_lo,r_hi]`. -/
private lemma phiC_v_osc {u_lo u_hi v_lo v_hi r_lo r_hi u v_n v_x r : ℝ}
    (hul : 0 < u_lo) (hulh : u_lo ≤ u_hi) (hvlh : v_lo ≤ v_hi)
    (hrl : 0 < r_lo) (hrlh : r_lo ≤ r_hi) (hW : 0 < u_lo ^ 2 + 2 * u_lo * v_lo)
    (hur : u_hi ≤ r_lo ^ 2)
    (hu : u_lo ≤ u) (hu2 : u ≤ u_hi)
    (hvn : v_lo ≤ v_n) (hvn2 : v_n ≤ v_hi) (hvx : v_lo ≤ v_x) (hvx2 : v_x ≤ v_hi)
    (hr : r_lo ≤ r) (hr2 : r ≤ r_hi) :
    |phiC u v_n r - phiC u v_x r|
      ≤ ((max |v_lo| |v_hi|) * (2 * (r_hi ^ 2 - u_lo) + 3 * (max |v_lo| |v_hi|))
            / (r_lo ^ 2 * (u_lo + v_lo + Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo)))
          + (max |v_lo| |v_hi|) ^ 2
              * (1 + u_hi / Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo))
              / (u_lo + v_lo + Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo)) ^ 2)
        * (v_hi - v_lo) := by
  have hC0 : 0 ≤ (max |v_lo| |v_hi|) * (2 * (r_hi ^ 2 - u_lo) + 3 * (max |v_lo| |v_hi|))
        / (r_lo ^ 2 * (u_lo + v_lo + Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo)))
      + (max |v_lo| |v_hi|) ^ 2 * (1 + u_hi / Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo))
        / (u_lo + v_lo + Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo)) ^ 2 := by
    have h1 : 0 < u_lo + v_lo := by nlinarith [hul, hW]
    have h2 : 0 < Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo) := Real.sqrt_pos.mpr hW
    have hR : 0 ≤ r_hi ^ 2 - u_lo := by
      have h3 : u_lo ≤ r_hi ^ 2 := le_trans hulh (le_trans hur (by nlinarith))
      linarith
    have hM0 : 0 ≤ max |v_lo| |v_hi| := le_trans (abs_nonneg _) (le_max_left _ _)
    have hd1 : 0 < r_lo ^ 2 * (u_lo + v_lo + Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo)) := by
      have : 0 < r_lo ^ 2 := by positivity
      exact mul_pos this (by linarith)
    have hd2 : 0 < (u_lo + v_lo + Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo)) ^ 2 := by
      positivity
    have h4 : 0 ≤ 2 * (r_hi ^ 2 - u_lo) + 3 * max |v_lo| |v_hi| := by linarith
    have h5 : 0 ≤ 1 + u_hi / Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo) := by
      have h6 : 0 ≤ u_hi / Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo) :=
        div_nonneg (by linarith) (Real.sqrt_nonneg _)
      linarith
    have h6 : 0 ≤ (max |v_lo| |v_hi|) * (2 * (r_hi ^ 2 - u_lo) + 3 * max |v_lo| |v_hi|) :=
      mul_nonneg hM0 h4
    have h7 : 0 ≤ (max |v_lo| |v_hi|) ^ 2 * (1 + u_hi / Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo)) :=
      mul_nonneg (sq_nonneg _) h5
    exact add_nonneg (div_nonneg h6 hd1.le) (div_nonneg h7 hd2.le)
  have huvl2 : 0 < u_lo + 2 * v_lo := by nlinarith [hul, hW]
  have hbd : ∀ w ∈ Set.Icc v_lo v_hi,
      ‖(2 * w / (u + w + Real.sqrt (u ^ 2 + 2 * u * w))
        - w ^ 2 * (1 + u / Real.sqrt (u ^ 2 + 2 * u * w))
            / (u + w + Real.sqrt (u ^ 2 + 2 * u * w)) ^ 2
        - w / r ^ 2 : ℝ)‖
      ≤ (max |v_lo| |v_hi|) * (2 * (r_hi ^ 2 - u_lo) + 3 * (max |v_lo| |v_hi|))
            / (r_lo ^ 2 * (u_lo + v_lo + Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo)))
        + (max |v_lo| |v_hi|) ^ 2
            * (1 + u_hi / Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo))
            / (u_lo + v_lo + Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo)) ^ 2 := by
    intro w hw
    rw [Real.norm_eq_abs]
    exact phiC_dv_bound hul hulh hvlh hrl hrlh hW hur hu hu2 hw.1 hw.2 hr hr2
  have hdv : ∀ w ∈ Set.Icc v_lo v_hi, HasDerivWithinAt (fun w : ℝ => phiC u w r)
      (2 * w / (u + w + Real.sqrt (u ^ 2 + 2 * u * w))
        - w ^ 2 * (1 + u / Real.sqrt (u ^ 2 + 2 * u * w))
            / (u + w + Real.sqrt (u ^ 2 + 2 * u * w)) ^ 2
        - w / r ^ 2) (Set.Icc v_lo v_hi) w := by
    intro w hw
    have h1 : 0 < u := lt_of_lt_of_le hul hu
    have h2 : 0 < u + 2 * w := by linarith [hw.1, hu, huvl2]
    have h3 : r ≠ 0 := by
      have : 0 < r := lt_of_lt_of_le hrl hr
      exact ne_of_gt this
    exact (phiC_hasDerivAt_v h1 h2 h3).hasDerivWithinAt
  rcases le_total v_n v_x with hle | hle
  · have hsub : Set.Icc v_n v_x ⊆ Set.Icc v_lo v_hi := Set.Icc_subset_Icc hvn hvx2
    have hder' : ∀ w ∈ Set.Icc v_n v_x, HasDerivWithinAt (fun w : ℝ => phiC u w r)
        (2 * w / (u + w + Real.sqrt (u ^ 2 + 2 * u * w))
          - w ^ 2 * (1 + u / Real.sqrt (u ^ 2 + 2 * u * w))
              / (u + w + Real.sqrt (u ^ 2 + 2 * u * w)) ^ 2
          - w / r ^ 2) (Set.Icc v_n v_x) w :=
      fun w hw => (hdv w (hsub hw)).mono hsub
    have hbd' : ∀ w ∈ Set.Ico v_n v_x,
        ‖(2 * w / (u + w + Real.sqrt (u ^ 2 + 2 * u * w))
          - w ^ 2 * (1 + u / Real.sqrt (u ^ 2 + 2 * u * w))
              / (u + w + Real.sqrt (u ^ 2 + 2 * u * w)) ^ 2
          - w / r ^ 2 : ℝ)‖
        ≤ (max |v_lo| |v_hi|) * (2 * (r_hi ^ 2 - u_lo) + 3 * (max |v_lo| |v_hi|))
              / (r_lo ^ 2 * (u_lo + v_lo + Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo)))
          + (max |v_lo| |v_hi|) ^ 2
              * (1 + u_hi / Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo))
              / (u_lo + v_lo + Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo)) ^ 2 :=
      fun w hw => hbd w (hsub (Set.Ico_subset_Icc_self hw))
    have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' hder' hbd'
    have hx := hmvt v_x (Set.right_mem_Icc.mpr hle)
    rw [Real.norm_eq_abs] at hx
    have h1 : |phiC u v_n r - phiC u v_x r| ≤
        ((max |v_lo| |v_hi|) * (2 * (r_hi ^ 2 - u_lo) + 3 * (max |v_lo| |v_hi|))
              / (r_lo ^ 2 * (u_lo + v_lo + Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo)))
          + (max |v_lo| |v_hi|) ^ 2
              * (1 + u_hi / Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo))
              / (u_lo + v_lo + Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo)) ^ 2) * (v_x - v_n) := by
      rw [abs_sub_comm]
      exact hx
    exact le_trans h1 (mul_le_mul_of_nonneg_left (by linarith) hC0)
  · have hsub : Set.Icc v_x v_n ⊆ Set.Icc v_lo v_hi := Set.Icc_subset_Icc hvx hvn2
    have hder' : ∀ w ∈ Set.Icc v_x v_n, HasDerivWithinAt (fun w : ℝ => phiC u w r)
        (2 * w / (u + w + Real.sqrt (u ^ 2 + 2 * u * w))
          - w ^ 2 * (1 + u / Real.sqrt (u ^ 2 + 2 * u * w))
              / (u + w + Real.sqrt (u ^ 2 + 2 * u * w)) ^ 2
          - w / r ^ 2) (Set.Icc v_x v_n) w :=
      fun w hw => (hdv w (hsub hw)).mono hsub
    have hbd' : ∀ w ∈ Set.Ico v_x v_n,
        ‖(2 * w / (u + w + Real.sqrt (u ^ 2 + 2 * u * w))
          - w ^ 2 * (1 + u / Real.sqrt (u ^ 2 + 2 * u * w))
              / (u + w + Real.sqrt (u ^ 2 + 2 * u * w)) ^ 2
          - w / r ^ 2 : ℝ)‖
        ≤ (max |v_lo| |v_hi|) * (2 * (r_hi ^ 2 - u_lo) + 3 * (max |v_lo| |v_hi|))
              / (r_lo ^ 2 * (u_lo + v_lo + Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo)))
          + (max |v_lo| |v_hi|) ^ 2
              * (1 + u_hi / Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo))
              / (u_lo + v_lo + Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo)) ^ 2 :=
      fun w hw => hbd w (hsub (Set.Ico_subset_Icc_self hw))
    have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' hder' hbd'
    have hx := hmvt v_n (Set.right_mem_Icc.mpr hle)
    rw [Real.norm_eq_abs] at hx
    exact le_trans hx (mul_le_mul_of_nonneg_left (by linarith) hC0)

/-! ## The master oscillation bound -/

theorem phiC_osc_le {u_lo u_hi v_lo v_hi r_lo r_hi : ℝ}
    (hul : 0 < u_lo) (hulh : u_lo ≤ u_hi) (hvlh : v_lo ≤ v_hi)
    (hrl : 0 < r_lo) (hrlh : r_lo ≤ r_hi)
    (hW : 0 < u_lo ^ 2 + 2 * u_lo * v_lo)
    (hSl : 0 < u_lo + v_lo + Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo))
    (hur : u_hi ≤ r_lo ^ 2)
    {u_n v_n r_n u_x v_x r_x : ℝ}
    (hun : u_lo ≤ u_n) (hun2 : u_n ≤ u_hi) (hux : u_lo ≤ u_x) (hux2 : u_x ≤ u_hi)
    (hvn : v_lo ≤ v_n) (hvn2 : v_n ≤ v_hi) (hvx : v_lo ≤ v_x) (hvx2 : v_x ≤ v_hi)
    (hrn : r_lo ≤ r_n) (hrn2 : r_n ≤ r_hi) (hrx : r_lo ≤ r_x) (hrx2 : r_x ≤ r_hi) :
    |phiC u_n v_n r_n - phiC u_x v_x r_x|
      ≤ 2 * ((max |v_lo| |v_hi|) ^ 2
            / ((u_lo + v_lo + Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo))
                * Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo))) * (u_hi - u_lo)
        + 2 * ((max |v_lo| |v_hi|) * (2 * max 0 (r_hi ^ 2 - u_lo) + 2 * max |v_lo| |v_hi|)
              / (r_lo ^ 2 * (u_lo + v_lo + Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo)))
            + (max |v_lo| |v_hi|) ^ 2
              * (1 + u_hi / Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo))
              / (u_lo + v_lo + Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo)) ^ 2) * (v_hi - v_lo)
        + 2 * ((max |v_lo| |v_hi|) ^ 2 / 2) * (1 / r_lo ^ 2 - 1 / r_hi ^ 2) := by
  set M := max |v_lo| |v_hi| with hM
  set D := Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo) with hD
  set S := u_lo + v_lo + D with hS
  have hDpos : 0 < D := by rw [hD]; exact Real.sqrt_pos.mpr hW
  have hSpos : 0 < S := by rw [hS]; linarith [hDpos, hSl]
  have hM0 : 0 ≤ M := by rw [hM]; exact le_trans (abs_nonneg _) (le_max_left _ _)
  have hR : 0 ≤ r_hi ^ 2 - u_lo := by
    have h3 : u_lo ≤ r_hi ^ 2 := le_trans hulh (le_trans hur (by nlinarith))
    linarith
  have hmax : max 0 (r_hi ^ 2 - u_lo) = r_hi ^ 2 - u_lo := max_eq_right hR
  set Bt := M * (2 * max 0 (r_hi ^ 2 - u_lo) + 2 * M) / (r_lo ^ 2 * S)
      + M ^ 2 * (1 + u_hi / D) / S ^ 2 with hBt
  set A1 := M * (2 * (r_hi ^ 2 - u_lo) + 3 * M) / (r_lo ^ 2 * S)
      + M ^ 2 * (1 + u_hi / D) / S ^ 2 with hA1
  set Cb := M ^ 2 / 2 * (1 / r_lo ^ 2 - 1 / r_hi ^ 2) with hCb
  rw [hmax] at hBt
  -- the three pieces
  have h1 : |phiC u_n v_n r_n - phiC u_x v_n r_n| ≤ M ^ 2 / (S * D) * (u_hi - u_lo) := by
    simpa only [hM, hD, hS] using phiC_u_osc hul hulh hW hun hun2 hux hux2 hvn hvn2
  have h2 : |phiC u_x v_n r_n - phiC u_x v_n r_x| ≤ Cb := by
    have h := phiC_rpart_le (v_lo := v_lo) (v_hi := v_hi) hrl hrlh hvn hvn2 hrn hrn2 hrx hrx2
    have heq : phiC u_x v_n r_n - phiC u_x v_n r_x
        = v_n ^ 2 / (2 * r_x ^ 2) - v_n ^ 2 / (2 * r_n ^ 2) := by
      simp only [phiC]; ring
    rw [heq, abs_sub_comm]
    simpa only [hM, hCb] using h
  have h3 : |phiC u_x v_n r_x - phiC u_x v_x r_x| ≤ A1 * (v_hi - v_lo) := by
    simpa only [hM, hD, hS, hA1] using
      phiC_v_osc hul hulh hvlh hrl hrlh hW hur hux hux2 hvn hvn2 hvx hvx2 hrx hrx2
  -- the chain
  have htri : |phiC u_n v_n r_n - phiC u_x v_x r_x|
      ≤ |phiC u_n v_n r_n - phiC u_x v_n r_n| + |phiC u_x v_n r_n - phiC u_x v_n r_x|
        + |phiC u_x v_n r_x - phiC u_x v_x r_x| := by
    have hdecomp : phiC u_n v_n r_n - phiC u_x v_x r_x
        = (phiC u_n v_n r_n - phiC u_x v_n r_n) + (phiC u_x v_n r_n - phiC u_x v_n r_x)
          + (phiC u_x v_n r_x - phiC u_x v_x r_x) := by ring
    rw [hdecomp]
    have h4 := abs_add_le (phiC u_n v_n r_n - phiC u_x v_n r_n)
      (phiC u_x v_n r_n - phiC u_x v_n r_x)
    have h5 := abs_add_le ((phiC u_n v_n r_n - phiC u_x v_n r_n)
      + (phiC u_x v_n r_n - phiC u_x v_n r_x)) (phiC u_x v_n r_x - phiC u_x v_x r_x)
    linarith
  -- nonnegativity and the comparison A1 ≤ 2Bt
  have hZ0 : 0 ≤ M ^ 2 / (S * D) := div_nonneg (sq_nonneg _) (mul_pos hSpos hDpos).le
  have hdu : 0 ≤ u_hi - u_lo := by linarith
  have hdv : 0 ≤ v_hi - v_lo := by linarith
  have hC0 : 0 ≤ Cb := by
    rw [hCb]
    have h1 : 0 < r_lo ^ 2 := by positivity
    have h2 : 1 / r_hi ^ 2 ≤ 1 / r_lo ^ 2 :=
      one_div_le_one_div_of_le h1 (by nlinarith)
    have h3 : 0 ≤ 1 / r_lo ^ 2 - 1 / r_hi ^ 2 := by linarith
    exact mul_nonneg (div_nonneg (sq_nonneg _) (by norm_num)) h3
  have hA1le : A1 ≤ 2 * Bt := by
    rw [hA1, hBt]
    have hden : 0 < r_lo ^ 2 * S := mul_pos (pow_pos hrl 2) hSpos
    have hden2 : 0 < S ^ 2 := pow_pos hSpos 2
    have hR' : 0 ≤ r_hi ^ 2 - u_lo := hR
    have h1 : M * (2 * (r_hi ^ 2 - u_lo) + 3 * M) ≤ 2 * (M * (2 * (r_hi ^ 2 - u_lo) + 2 * M)) := by
      nlinarith [hM0, hR']
    have h2 : M ^ 2 * (1 + u_hi / D) ≤ 2 * (M ^ 2 * (1 + u_hi / D)) := by
      have h5 : 0 ≤ u_hi / D := div_nonneg (by linarith) hDpos.le
      have : 0 ≤ M ^ 2 * (1 + u_hi / D) := mul_nonneg (sq_nonneg _) (by linarith)
      linarith
    have h3 : M * (2 * (r_hi ^ 2 - u_lo) + 3 * M) / (r_lo ^ 2 * S)
        ≤ 2 * (M * (2 * (r_hi ^ 2 - u_lo) + 2 * M)) / (r_lo ^ 2 * S) :=
      div_le_div_of_nonneg_right h1 hden.le
    have h4 : M ^ 2 * (1 + u_hi / D) / S ^ 2 ≤ 2 * (M ^ 2 * (1 + u_hi / D)) / S ^ 2 :=
      div_le_div_of_nonneg_right h2 hden2.le
    have h5 : 2 * (M * (2 * (r_hi ^ 2 - u_lo) + 2 * M) / (r_lo ^ 2 * S)
        + M ^ 2 * (1 + u_hi / D) / S ^ 2)
        = 2 * (M * (2 * (r_hi ^ 2 - u_lo) + 2 * M)) / (r_lo ^ 2 * S)
          + 2 * (M ^ 2 * (1 + u_hi / D)) / S ^ 2 := by ring
    rw [h5]
    linarith
  have key : |phiC u_n v_n r_n - phiC u_x v_x r_x|
      ≤ 2 * (M ^ 2 / (S * D)) * (u_hi - u_lo) + 2 * Bt * (v_hi - v_lo) + 2 * Cb := by
    have e1 : M ^ 2 / (S * D) * (u_hi - u_lo) ≤ 2 * (M ^ 2 / (S * D)) * (u_hi - u_lo) := by
      nlinarith [hZ0, hdu]
    have e3 : A1 * (v_hi - v_lo) ≤ 2 * Bt * (v_hi - v_lo) :=
      mul_le_mul_of_nonneg_right hA1le hdv
    have e2 : Cb ≤ 2 * Cb := by linarith
    linarith [htri, h1, h2, h3, e1, e2, e3]
  have e : 2 * (M ^ 2 / 2) * (1 / r_lo ^ 2 - 1 / r_hi ^ 2) = 2 * Cb := by
    rw [hCb]; ring
  rw [e]
  exact key

end Work.BoseBogFS
