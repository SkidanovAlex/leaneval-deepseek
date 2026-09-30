/-
# The height of the unslabbed collar coordinate is the height of the point

`cuspInvOuter v q` is the explicit inverse of the outer cusp chart on a UHS coordinate `q = (x,s)`:
the layer parameter `t = 1 + (log s − log β(x)) / (2 (log β(x) − log s_J))`, the direction
`bndOfU (outerU v x)` and the phase `outerY v x`.

The *unslabbed* collar source `cuspSourceTop v c δ` has no meridian slab: only the box of side `2δ`
and the height window `(s₁, sTop)`, on or above the ceiling.  The key point of this file is that the
UHS height of the recovered point

  `collarS v (cuspInvOuter v q).1 (cuspInvOuter v q).2`

is still the height `q 3` of `q`, even though the recovered meridian parameter `u (t • bndOfU u₀)`
is only the *fractional part* of `outerU v x`.  The reason is `beta_cuspX_fract`: the ceiling at
`cuspX v (Int.fract u) y` equals the ceiling at `cuspX v u y`, because `cuspX v u y` differs from
`cuspX v (Int.fract u) y` by the *integer* vector `⌊u⌋ σ_v` and `β` is invariant under integer
translations.  (`cX_outerU_outerY` then identifies `cuspX v (outerU v x) (outerY v x)` with `x`.)

The layer parameter is strictly positive — that is what makes `nrm (t • bndOfU u) = t` — by
`β(x) · s < s_J²` (`Work.Cusp.beta_mul_sTop_lt_sJ_sq`), i.e. exactly the comparison which the
height window `(s₁, sTop)` was chosen for.
-/
import Mathlib
import Submission.Work.Cusp.TopBox
import Submission.Work.Cusp.TopWindow
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.beta_cuspX_fract
import Submission.Work.Cusp.bnd_eq_self
import Submission.Work.Cusp.u_smul
import Submission.Work.Cusp.uPerim_bndOfU
import Submission.Work.Cusp.nrm_smul
import Submission.Work.Cusp.nrm_bndOfU
import Submission.Work.Cusp.beta_pos
import Submission.Work.Cusp.beta_le_max
import Submission.Work.Cusp.betaMax_lt_sJ
import Submission.Work.Cusp.cuspX_outerU_outerY
import Submission.Work.Cusp.cuspInvOuter_height

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

/-- **The height round trip of the unslabbed collar coordinate.**  For a point `q` of the collar
source (the box of side `2δ` with height in `(s₁, sTop)`, on or above the ceiling), the UHS height of
the point recovered by `cuspInvOuter v q` is the height `q 3` of `q`. -/
theorem cuspInvOuter_heightTop (v : Fin 5) (c : E3) (δ : ℝ) (q : E4)
    (hq : q ∈ cuspSourceTop v c δ) :
    collarS v (cuspInvOuter v q).1 (cuspInvOuter v q).2 = q 3 := by
  obtain ⟨hbox, hbeta⟩ := hq
  obtain ⟨-, hs1, hlt⟩ := hbox
  -- unfold the inverse and name its three ingredients
  simp only [cuspInvOuter]
  set X : E3 := !₂[q 0, q 1, q 2] with hX
  set B : ℝ := beta X with hB
  set T : ℝ := 1 + (Real.log (q 3) - Real.log B) / (2 * (Real.log B - Real.log sJ)) with hT
  have hBpos : 0 < B := by rw [hB]; exact beta_pos X
  have hB_lt_sJ : B < sJ := by
    rw [hB]; exact lt_of_le_of_lt (beta_le_max X) betaMax_lt_sJ
  have hq3pos : 0 < q 3 := lt_trans (by norm_num [s1]) hs1
  have hne : Real.log B ≠ Real.log sJ := ne_of_lt (Real.log_lt_log hBpos hB_lt_sJ)
  -- the recovered layer parameter is positive: `β(x) · s < s_J²`
  have hprod : q 3 * B < sJ ^ 2 := by
    have h1 : q 3 * B < sTop * B := mul_lt_mul_of_pos_right (by simpa only [xOf, hX] using hlt) hBpos
    have h2 : sTop * B ≤ sTop * betaMax :=
      mul_le_mul_of_nonneg_left (by rw [hB]; exact beta_le_max X) (le_of_lt sTop_pos)
    have h3 : sTop * betaMax < sJ ^ 2 := by
      rw [mul_comm]; exact betaMax_mul_sTop_lt_sJ_sq
    linarith
  have hTpos : 0 < T := by
    rw [hT, hB]
    have hJ : 0 < 2 * (Real.log sJ - Real.log (beta X)) := by
      have h := Real.log_lt_log hBpos hB_lt_sJ
      linarith
    rw [show (1 : ℝ) + (Real.log (q 3) - Real.log (beta X)) /
          (2 * (Real.log (beta X) - Real.log sJ))
        = 1 - (Real.log (q 3) - Real.log (beta X)) /
            (2 * (Real.log sJ - Real.log (beta X))) by
      have hden : 2 * (Real.log (beta X) - Real.log sJ)
          = -(2 * (Real.log sJ - Real.log (beta X))) := by ring
      rw [hden, div_neg]
      ring]
    rw [sub_pos, div_lt_one hJ]
    have hp : Real.log (q 3 * beta X) < Real.log (sJ ^ 2) :=
      Real.log_lt_log (mul_pos hq3pos hBpos) hprod
    rw [Real.log_mul (ne_of_gt hq3pos) (ne_of_gt hBpos), Real.log_pow] at hp
    push_cast at hp
    linarith
  -- the two coordinates of the recovered point
  have hnrm : nrm (T • bndOfU (outerU v X)) = T := by
    rw [nrm_smul, nrm_bndOfU, mul_one, abs_of_pos hTpos]
  have hw : u (T • bndOfU (outerU v X)) = Int.fract (outerU v X) := by
    rw [u_smul hTpos]
    simp only [u]
    rw [bnd_eq_self (nrm_bndOfU (outerU v X)), uPerim_bndOfU]
  have hbeta2 : beta (cuspX v (u (T • bndOfU (outerU v X))) (outerY v X)) = B := by
    rw [hw, beta_cuspX_fract, hB]
    exact congrArg beta (cuspX_outerU_outerY v X)
  rw [collarS, hnrm, hbeta2, hT]
  exact collarHeight_of_log B (q 3) hq3pos hne

end Work.Cusp
