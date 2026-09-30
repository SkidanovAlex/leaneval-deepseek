/-
# The round-trip identity `Θ_v (cuspInvInner q) = q` for the inner (polar) chart

`cuspInvInner v : E4 → E2 × E2` is the explicit inverse of the polar chart
`ThetaPolar v : E2 × E2 → E4` of the filling piece `W_v` of the `v`-th cusp
(`Work.Cusp.Basic`), and this file proves that it is a *right* inverse on the polar box
`polarBox = {1/4 < r < r_J + 1}` restricted to the points whose recovered perimeter
coordinate `uqOf v q` lies in `[0,1)`:

`ThetaPolar v (cuspInvInner v q).1 (cuspInvInner v q).2 = q`.

The companion identity `cuspInvInner_ThetaPolar` (`cuspInvInner v (ThetaPolar v p y) = (p,y)`)
is the other composition, and is the content of the polar chart being a chart.

## The three coordinates

Write `y = invY v (q₂,q₃)` (the recovery of the torus coordinates from the `w`-coordinates),
`u = uqOf v q = (q₁ − 2π⟪y,σ⟫/‖σ‖²)/2π` (the recovered perimeter coordinate) and
`b = β (cuspX v u y)`, and let `p = t • bndOfU u` where the layer parameter `t = ‖p‖∞` is
recovered from `q 0 = r` by the two branches of `cuspInvInner`:

* `r ≤ r_J`: `t = r/(2 r_J)`, and then `t ≤ 1/2`, so `p` is in the inner disk and
  `r = radial v p y = 2 r_J ‖p‖∞ = r`;
* `r_J < r`: `t = 1 + (R₀ − r − log b)/(2 (log b − log s_J))`.  The two facts we need are
  `t > 1/2` and `log (collarS v p y) = log (collarHeight t b) = R₀ − r`, so that
  `radial v p y = R₀ − log (collarS v p y) = r` (the collar branch of `radial`).  Both are
  algebra with the single relation `s_J = e^{1/2}` (`log_sJ`): writing `L = log b`,
  `S = log s_J = 1/2` and `N = R₀ − r − L`, one has `t = 1 + N/(2(L−S))`, and

  * `t − 1/2 = (R₀ − r − S)/(2 (L − S)) = (r_J − r)/(2(L − S))`, which is `> 0` exactly
    because `r > r_J` (and `L − S < 0`, i.e. `β < s_J`, `betaMax_lt_sJ`);
  * `(2t − 1) L + (2 − 2t) S = L + N = R₀ − r`.

The second coordinate `q₁` is the definitions unravelled: `θ = 2π u + 2π (⟪y,σ⟫/‖σ‖²)` and
`u` was *defined* as the solution of that equation (`hu`, the hypothesis `uqOf v q ∈ [0,1)` is
what makes `u` the honest perimeter coordinate, via `uPerim_bndOfU`).  The last two coordinates
are `wOf_invY`, the inverse relation of `wOf` and `invY`.

All the ingredients are already in the neighbouring modules (`nrm_bndOfU`, `uPerim_bndOfU`,
`bnd_eq_self`, `u_smul`, `nrm_smul`, `wOf_invY`, `beta_pos`, `beta_le_max`, `betaMax_lt_sJ`,
`log_sJ`, `radial_eq_inner`, `radial_collar`); here we put them together.
-/
import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.nrm_bndOfU
import Submission.Work.Cusp.uPerim_bndOfU
import Submission.Work.Cusp.bnd_eq_self
import Submission.Work.Cusp.u_smul
import Submission.Work.Cusp.nrm_smul
import Submission.Work.Cusp.wOf_invY
import Submission.Work.Cusp.radial_bounds

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.Cusp

open scoped Real InnerProductSpace

/-! ### The algebra of the collar branch of `cuspInvInner` -/

/-- **The recovered layer parameter is `> 1/2` in the collar branch.**  For `L − S < 0` and
`N < S − L` (here `L = log b`, `S = log s_J = 1/2` and `N = R₀ − r − L`) one has
`1/2 < 1 + N/(2(L−S))`: indeed the difference from `1/2` is `(N − (S − L))/(2(L−S))`, a quotient
of two negative numbers. -/
private lemma collarRate_gt_half {L S N : ℝ} (hA : L - S < 0) (hN : N < S - L) :
    1 / 2 < 1 + N / (2 * (L - S)) := by
  have hc : 2 * (L - S) < 0 := by linarith
  have h : -1 / 2 < N / (2 * (L - S)) := by
    rw [lt_div_iff_of_neg hc]
    linarith
  linarith

/-- The collar branch of the recovered layer parameter exceeds the junction layer `1/2`:
`1/2 < 1 + (R₀ − r − log b)/(2 (log b − log s_J))` whenever `log b < log s_J` and `r > r_J`.

Indeed the difference from `1/2` is `(R₀ − r − log s_J)/(2 (log b − log s_J)) = (r_J − r)/(2(·))`,
a quotient of two negative numbers, using `R₀ − log s_J = r_J` (`R0`, `log_sJ`, `rJ`). -/
theorem cuspInvRate_gt_half {b r : ℝ} (hL : Real.log b < Real.log sJ) (hr : rJ < r) :
    1 / 2 < 1 + (R0 - r - Real.log b) / (2 * (Real.log b - Real.log sJ)) := by
  refine collarRate_gt_half (by linarith) ?_
  have h1 : R0 - r < Real.log sJ := by
    rw [log_sJ, R0] at *
    rw [rJ] at hr
    linarith
  linarith

/-- **The collar height recovered from the layer parameter is the height `R₀ − r`**:
if `t = 1 + (R₀ − r − log b)/(2 (log b − log s_J))` then `log (collarHeight t b) = R₀ − r`.
This is the identity `collarHeight t b = b^{2t−1} s_J^{2−2t}` inverted for `t`. -/
theorem log_collarHeight_cuspInvRate {b r : ℝ} (hA : Real.log b - Real.log sJ ≠ 0) :
    Real.log (collarHeight (1 + (R0 - r - Real.log b) / (2 * (Real.log b - Real.log sJ))) b)
      = R0 - r := by
  rw [collarHeight, Real.log_exp]
  have h2 : (2:ℝ) * (Real.log b - Real.log sJ) ≠ 0 := by
    intro h; exact hA (by linarith)
  have h2t : 2 * (1 + (R0 - r - Real.log b) / (2 * (Real.log b - Real.log sJ))) - 1
      = 1 + (R0 - r - Real.log b) / (Real.log b - Real.log sJ) := by
    field_simp
    ring
  have h2mt : 2 - 2 * (1 + (R0 - r - Real.log b) / (2 * (Real.log b - Real.log sJ)))
      = -((R0 - r - Real.log b) / (Real.log b - Real.log sJ)) := by
    field_simp
    ring
  rw [h2t, h2mt]
  field_simp
  ring

/-! ### The round trip on the polar box -/

/-- **The main computation, for arbitrary names of the intermediate quantities.**  If `y`, `u`,
`b`, `t` are the quantities of `cuspInvInner` (`y = invY v (q₂,q₃)`,
`u = (q₁ − 2π(⟪y,σ⟫/‖σ‖²))/2π`, `b = β (cuspX v u y)` and `t` the recovered layer parameter),
and `u ∈ [0,1)`, `q 0 > 0`, then `ThetaPolar v (t • bndOfU u) y = q`. -/
private theorem thetaPolar_cuspInvInner_aux (v : Fin 5) (q : E4) (y : E2) (uu t b : ℝ)
    (hy : y = invY v !₂[q 2, q 3])
    (huu : uu = (q 1 - 2 * π * (⟪cuspY v y, slope v⟫_ℝ / ‖slope v‖ ^ 2)) / (2 * π))
    (hb : b = beta (cuspX v uu y))
    (hu : 0 ≤ uu ∧ uu < 1) (hq0 : 0 < q 0)
    (ht : t = if q 0 ≤ rJ then q 0 / (2 * rJ)
      else 1 + (R0 - q 0 - Real.log b) / (2 * (Real.log b - Real.log sJ))) :
    ThetaPolar v (t • bndOfU uu) y = q := by
  have hbpos : 0 < b := by rw [hb]; exact beta_pos _
  have hblt : b < sJ := by rw [hb]; exact lt_of_le_of_lt (beta_le_max _) betaMax_lt_sJ
  have hloglt : Real.log b - Real.log sJ < 0 := by
    have := Real.log_lt_log hbpos hblt
    linarith
  have hAne : Real.log b - Real.log sJ ≠ 0 := ne_of_lt hloglt
  -- the layer parameter is positive
  have htpos : 0 < t := by
    rw [ht]
    split_ifs with hle
    · exact div_pos hq0 (by rw [rJ]; norm_num)
    · have hgt : rJ < q 0 := not_le.mp hle
      have hN : R0 - q 0 - Real.log b < Real.log sJ - Real.log b := by
        have h1 : R0 - q 0 < Real.log sJ := by
          rw [log_sJ, R0] at *
          rw [rJ] at hgt
          linarith
        linarith
      have := collarRate_gt_half hloglt hN
      linarith
  -- `p = t • bndOfU uu` has sup norm `t` and perimeter parameter `uu`
  have hnrm : nrm (t • bndOfU uu) = t := by
    rw [nrm_smul, nrm_bndOfU, mul_one, abs_of_pos htpos]
  have hu_p : u (t • bndOfU uu) = uu := by
    rw [u, bnd_smul_of_pos htpos, bnd_eq_self (nrm_bndOfU uu), uPerim_bndOfU,
      Int.fract_eq_self.mpr hu]
  have hcollarS : collarS v (t • bndOfU uu) y = collarHeight t b := by
    rw [collarS, hnrm, hu_p, hb]
  -- the first coordinate `r = radial v p y`
  have hrad : radial v (t • bndOfU uu) y = q 0 := by
    by_cases hle : q 0 ≤ rJ
    · have ht1 : t = q 0 / (2 * rJ) := by rw [ht, if_pos hle]
      have hle' : nrm (t • bndOfU uu) ≤ 1 / 2 := by
        rw [hnrm, ht1]
        rw [div_le_iff₀ (by rw [rJ]; norm_num)]
        linarith
      rw [radial_eq_inner v _ y hle', hnrm, ht1, rJ]
      ring
    · have hgt : rJ < q 0 := not_le.mp hle
      have ht1 : t = 1 + (R0 - q 0 - Real.log b) / (2 * (Real.log b - Real.log sJ)) := by
        rw [ht, if_neg hle]
      have hhalf : 1 / 2 < t := by
        rw [ht1]
        exact cuspInvRate_gt_half (by linarith) hgt
      have hge : 1 / 2 ≤ nrm (t • bndOfU uu) := by rw [hnrm]; linarith
      rw [radial_collar v _ y hge, hcollarS, ht1, log_collarHeight_cuspInvRate hAne]
      ring
  -- the second coordinate `θ = thetaAng v p y`
  have htheta : thetaAng v (t • bndOfU uu) y = q 1 := by
    rw [thetaAng, hu_p]
    have hcancel : 2 * π * uu = q 1 - 2 * π * (⟪cuspY v y, slope v⟫_ℝ / ‖slope v‖ ^ 2) := by
      rw [huu, ← mul_div_assoc, mul_div_cancel_left₀ _ (by positivity : (2:ℝ) * π ≠ 0)]
    rw [hcancel]
    ring
  -- the last two coordinates `w = (wOf v y 0, wOf v y 1)`
  have hw : wOf v y = !₂[q 2, q 3] := by rw [hy]; exact wOf_invY v !₂[q 2, q 3]
  have hw0 : wOf v y 0 = q 2 := by rw [hw]; simp
  have hw1 : wOf v y 1 = q 3 := by rw [hw]; simp
  rw [ThetaPolar]
  ext i
  fin_cases i
  · simpa using hrad
  · simpa using htheta
  · simpa using hw0
  · simpa using hw1

/-- **The polar chart is a right inverse of its explicit inverse.**  For `q` in the polar box
`1/4 < q 0 < r_J + 1` whose recovered perimeter coordinate `uqOf v q` is the representative in
`[0,1)`, the point `p = (cuspInvInner v q).1` (with layer parameter recovered from `q 0 = radial`)
and the recovered torus coordinates `y = (cuspInvInner v q).2` satisfy
`ThetaPolar v p y = q`. -/
theorem ThetaPolar_cuspInvInner (v : Fin 5) (q : E4) (hq : q ∈ polarBox)
    (hu : uqOf v q ∈ Set.Ico 0 1) :
    ThetaPolar v (cuspInvInner v q).1 (cuspInvInner v q).2 = q := by
  rw [Set.mem_Ico] at hu
  rw [polarBox, Set.mem_setOf_eq] at hq
  simp only [cuspInvInner]
  set y : E2 := invY v !₂[q 2, q 3] with hy
  set uu : ℝ := (q 1 - 2 * π * (⟪cuspY v y, slope v⟫_ℝ / ‖slope v‖ ^ 2)) / (2 * π) with huu
  set b : ℝ := beta (cuspX v uu y) with hb
  set t : ℝ := if q 0 ≤ rJ then q 0 / (2 * rJ)
      else 1 + (R0 - q 0 - Real.log b) / (2 * (Real.log b - Real.log sJ)) with ht
  -- `uqOf` is the same expression as `cuspInvInner`'s perimeter coordinate, up to a ring rewrite
  have hconv : uqOf v q = uu := by rw [huu, uqOf, ← hy]; ring
  have hu' : 0 ≤ uu ∧ uu < 1 := by rw [← hconv]; exact hu
  exact thetaPolar_cuspInvInner_aux v q y uu t b hy huu hb hu' (by linarith [hq.1]) ht

end Work.Cusp
