/-
# Injectivity of the core chart `Θ_v` (Cartesian coordinates)

`ThetaCore v p y = (r cos θ, r sin θ, w₁, w₂)` is the Cartesian form of the polar chart
`ThetaPolar v p y`, where

* `r = radial v p y` is the metric radial coordinate (`2 r_J ‖p‖∞` in the inner region,
  `R₀ − log (collarS v p y)` in the collar),
* `θ = thetaAng v p y = 2π u(p) + 2π⟪cuspY v y, σ_v⟫/‖σ_v‖²` is the angle,
* `w = wOf v y` is the `σ_v^⊥`-component of the cusp coordinate `y₂λ₂ + y₃λ₃`.

This is the injectivity of the core chart on the whole of `E2 × E2` (the chart is used on a
neighbourhood of `p = 0`, but the statement holds everywhere, since every ingredient is a function
of `(nrm p, u p, y)` and that triple determines `(p,y)`).

The proof identifies the three pieces in turn:

* the last two coordinates are `wOf v y`, and `invY v` inverts `wOf v` (`wDet v ≠ 0`), so they
  determine `y` (`invY_wOf`);
* the first two coordinates give `r` (via `r² = (r cos θ)² + (r sin θ)²` and `r ≥ 0`) and, when
  `r ≠ 0`, the angle `θ` modulo `2π`; since `θ` is `2π u(p)` plus a term depending only on `y`,
  this gives `u p = u q` (`u ∈ [0,1)`, `Real.cos_eq_one_iff`);
* finally `r` determines `‖p‖∞` once `u p` and `y` are fixed: in the inner region `r = 2r_J‖p‖∞`
  is strictly increasing, in the collar `r = R₀ − log (collarHeight ‖p‖∞ β)` is strictly monotone
  because `β < s_J`, and the two regions are separated by the junction value `r_J`;
* `(nrm p, u p)` determines `p` (`nrm u injOn`, radial projection to `∂Sq`).
-/
import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.invY_wOf
import Submission.Work.Cusp.nrm_bnd
import Submission.Work.Cusp.nrm_nonneg
import Submission.Work.Cusp.smul_bnd
import Submission.Work.Cusp.uPerim_mem
import Submission.Work.Cusp.nrm_u_injOn
import Submission.Work.Cusp.beta_pos
import Submission.Work.Cusp.beta_le_max
import Submission.Work.Cusp.betaMax_lt_sJ
import Submission.Work.Cusp.radial_eq_inner
import Submission.Work.Cusp.radial_collar
import Submission.Work.Cusp.collarHeight_pos

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.Cusp

open scoped Real InnerProductSpace

/-! ### The four coordinates of the core chart -/

/-- First coordinate of the core chart: `r cos θ`. -/
theorem ThetaCore_zero (v : Fin 5) (p y : E2) :
    (ThetaCore v p y) 0 = radial v p y * Real.cos (thetaAng v p y) := by
  simp [ThetaCore]

/-- Second coordinate of the core chart: `r sin θ`. -/
theorem ThetaCore_one (v : Fin 5) (p y : E2) :
    (ThetaCore v p y) 1 = radial v p y * Real.sin (thetaAng v p y) := by
  simp [ThetaCore]

/-- Third coordinate of the core chart: `w₁ = ⟪cuspY v y, frame2 v⟫`. -/
theorem ThetaCore_two (v : Fin 5) (p y : E2) : (ThetaCore v p y) 2 = wOf v y 0 := by
  simp [ThetaCore]

/-- Fourth coordinate of the core chart: `w₂ = ⟪cuspY v y, frame3 v⟫`. -/
theorem ThetaCore_three (v : Fin 5) (p y : E2) : (ThetaCore v p y) 3 = wOf v y 1 := by
  simp [ThetaCore]

/-! ### The perimeter parameter lives in `[0,1)` -/

/-- The perimeter parameter `u p` of *every* point of `E2` lies in `[0,1)`: for `p ≠ 0` the radial
projection `bnd p` has sup norm `1` (`nrm_bnd`), and at `p = 0` we have `bnd 0 = 0` and
`uPerim 0 = 7/8`. -/
theorem u_mem_all (p : E2) : 0 ≤ u p ∧ u p < 1 := by
  rcases eq_or_ne p 0 with h | h
  · subst h
    have hb : bnd (0 : E2) = 0 := by simp [bnd]
    rw [u, hb]
    norm_num [uPerim]
  · rw [u]
    exact uPerim_mem (nrm_bnd h)

/-! ### `(nrm, u)` determines the point -/

/-- **The two filling coordinates `(‖p‖∞, u(p))` determine `p`** on the whole of `E2` (compare
`nrm_u_injOn`, which is the same statement on the square `Sq`): for a nonzero point the radial
projection `bnd p ∈ ∂Sq = {nrm = 1}` is recovered from `u p = uPerim (bnd p)`, since `uPerim` is
injective on `∂Sq`, and then `p = ‖p‖∞ • bnd p`. -/
theorem nrm_u_inj (p q : E2) (hn : nrm p = nrm q) (hu : u p = u q) : p = q := by
  rcases eq_or_ne (nrm p) 0 with h0 | h0
  · have hq0 : nrm q = 0 := by rw [← hn]; exact h0
    rw [nrmu_nrm_eq_zero h0, nrmu_nrm_eq_zero hq0]
  · have hp : p ≠ 0 := fun h' => h0 (by rw [h']; simp [nrm])
    have hq : q ≠ 0 := by
      intro h'
      exact h0 (by rw [hn, h']; simp [nrm])
    have hb : bnd p = bnd q :=
      nrmu_uPerim_injOn (nrm_bnd hp) (nrm_bnd hq) (by simpa [u] using hu)
    calc p = nrm p • bnd p := (smul_bnd p).symm
      _ = nrm q • bnd q := by rw [hn, hb]
      _ = q := smul_bnd q

/-! ### The angle determines the perimeter parameter -/

/-- **The core angle determines `u p`.**  Two points with the same `y` and with equal `cos` and
`sin` of the core angle have the same perimeter parameter: the two angles differ by `2π(u p − u q)`,
and since both parameters lie in `[0,1)`, equality of the angles on the circle forces `u p = u q`. -/
theorem u_eq_of_angle (v : Fin 5) (p q y : E2)
    (hc : Real.cos (thetaAng v p y) = Real.cos (thetaAng v q y))
    (hs : Real.sin (thetaAng v p y) = Real.sin (thetaAng v q y)) : u p = u q := by
  -- the difference of the two angles is a multiple of `2π`
  have hcos1 : Real.cos (thetaAng v p y - thetaAng v q y) = 1 := by
    rw [Real.cos_sub, hc, hs]
    nlinarith [Real.cos_sq_add_sin_sq (thetaAng v q y)]
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff (thetaAng v p y - thetaAng v q y)).mp hcos1
  have hdiff : thetaAng v p y - thetaAng v q y = 2 * π * (u p - u q) := by
    rw [thetaAng, thetaAng]; ring
  have hpi : (2 * π : ℝ) ≠ 0 := by positivity
  have hd : (n : ℝ) = u p - u q := by
    have h := hn
    rw [hdiff, mul_comm (2 * π) (u p - u q)] at h
    exact mul_right_cancel₀ hpi h
  have hu := u_mem_all p
  have hq := u_mem_all q
  have hlt : (n : ℝ) < 1 := by rw [hd]; linarith [hu.2, hq.1]
  have hgt : (-1 : ℝ) < (n : ℝ) := by rw [hd]; linarith [hu.1, hq.2]
  have hn0 : n = 0 := by
    have h1 : n < (1 : ℤ) := by exact_mod_cast hlt
    have h2 : (-1 : ℤ) < n := by exact_mod_cast hgt
    omega
  rw [show (n : ℝ) = 0 by rw [hn0]; norm_num] at hd
  linarith

/-! ### The bounds on the radial coordinate -/

/-- The collar height of a point of the collar (`1/2 < ‖p‖∞`) is strictly below the junction
height `s_J`: the exponent of `collarHeight` is a convex combination of `log β(x)` and `log s_J`
with the coefficient `2‖p‖∞ − 1 > 0` in front of the smaller number `log β(x) < log s_J`. -/
theorem collarS_lt_sJ (v : Fin 5) (p y : E2) (hp : 1 / 2 < nrm p) : collarS v p y < sJ := by
  have hsJ : 0 < sJ := by rw [sJ]; exact Real.exp_pos _
  have hb : 0 < beta (cuspX v (u p) y) := beta_pos _
  have hbsJ : beta (cuspX v (u p) y) < sJ := lt_of_le_of_lt (beta_le_max _) betaMax_lt_sJ
  have hlog : Real.log (beta (cuspX v (u p) y)) < Real.log sJ := Real.log_lt_log hb hbsJ
  have h2 : 0 < 2 * nrm p - 1 := by linarith
  have h1 : (2 * nrm p - 1) * Real.log (beta (cuspX v (u p) y))
      < (2 * nrm p - 1) * Real.log sJ := mul_lt_mul_of_pos_left hlog h2
  have hE : (2 * nrm p - 1) * Real.log (beta (cuspX v (u p) y))
      + (2 - 2 * nrm p) * Real.log sJ < Real.log sJ := by nlinarith [h1]
  calc collarS v p y
      = Real.exp ((2 * nrm p - 1) * Real.log (beta (cuspX v (u p) y))
          + (2 - 2 * nrm p) * Real.log sJ) := by rw [collarS, collarHeight]
    _ < Real.exp (Real.log sJ) := Real.exp_lt_exp.mpr hE
    _ = sJ := Real.exp_log hsJ

/-- In the collar (`1/2 < ‖p‖∞`) the radial coordinate exceeds the junction value `r_J`. -/
theorem rJ_lt_radial (v : Fin 5) (p y : E2) (hp : 1 / 2 < nrm p) : rJ < radial v p y := by
  have h := collarS_lt_sJ v p y hp
  have hpos : 0 < collarS v p y := by rw [collarS, collarHeight]; exact Real.exp_pos _
  have hlog : Real.log (collarS v p y) < Real.log sJ := Real.log_lt_log hpos h
  have hsJlog : Real.log sJ = 1 / 2 := by rw [sJ]; exact Real.log_exp (1 / 2)
  rw [radial_collar v p y (le_of_lt hp)]
  unfold R0 rJ
  linarith

/-- In the inner region (`‖p‖∞ ≤ 1/2`) the radial coordinate is at most the junction value. -/
theorem radial_le_rJ (v : Fin 5) (p y : E2) (hp : nrm p ≤ 1 / 2) : radial v p y ≤ rJ := by
  rw [radial_eq_inner v p y hp]
  unfold rJ
  linarith [nrm_nonneg p]

/-- The radial coordinate is nonnegative. -/
theorem radial_nonneg (v : Fin 5) (p y : E2) : 0 ≤ radial v p y := by
  by_cases hp : nrm p ≤ 1 / 2
  · rw [radial_eq_inner v p y hp]
    unfold rJ
    linarith [nrm_nonneg p]
  · have h := rJ_lt_radial v p y (not_le.mp hp)
    unfold rJ at h
    linarith

/-! ### Injectivity of `collarHeight` in the layer parameter -/

/-- For a ceiling value `b ∈ (0, s_J)` the collar height is injective as a function of the layer
parameter `t`: the exponent is affine in `t` with slope `2(log b − log s_J) ≠ 0`. -/
theorem collarHeight_inj (t t' b : ℝ) (hb : 0 < b) (hbne : b ≠ sJ)
    (h : collarHeight t b = collarHeight t' b) : t = t' := by
  have hsJ : 0 < sJ := by rw [sJ]; exact Real.exp_pos _
  have hlog : Real.log b ≠ Real.log sJ := fun hh => hbne (Real.log_injOn_pos hb hsJ hh)
  have hexp : (2 * t - 1) * Real.log b + (2 - 2 * t) * Real.log sJ
      = (2 * t' - 1) * Real.log b + (2 - 2 * t') * Real.log sJ :=
    Real.exp_injective (by simpa [collarHeight] using h)
  have hprod : (Real.log b - Real.log sJ) * (2 * t - 2 * t') = 0 := by nlinarith [hexp]
  rcases mul_eq_zero.mp hprod with hh | hh
  · exact absurd (sub_eq_zero.mp hh) hlog
  · linarith

/-! ### The radial coordinate determines `‖p‖∞` -/

/-- **The radial coordinate and the perimeter parameter determine `‖p‖∞`.**  With `u p = u q`
fixed, the ceiling `β(cuspX v u p y)` is the same for both points, so `r` is a strictly monotone
function of `‖p‖∞` on each of the two branches of `radial`, and the branches are separated by the
junction value `r_J` (`radial ≤ r_J` in the inner region, `r_J < radial` in the collar). -/
theorem nrm_eq_of_radial_eq (v : Fin 5) (p q y : E2) (hu : u p = u q)
    (hr : radial v p y = radial v q y) : nrm p = nrm q := by
  by_cases hp : nrm p ≤ 1 / 2
  · by_cases hq : nrm q ≤ 1 / 2
    · rw [radial_eq_inner v p y hp, radial_eq_inner v q y hq] at hr
      rw [rJ] at hr
      linarith
    · have h1 := radial_le_rJ v p y hp
      have h2 := rJ_lt_radial v q y (not_le.mp hq)
      rw [hr] at h1
      linarith
  · by_cases hq : nrm q ≤ 1 / 2
    · have h1 := radial_le_rJ v q y hq
      have h2 := rJ_lt_radial v p y (not_le.mp hp)
      rw [hr] at h2
      linarith
    · -- both points are in the collar
      have hp' : 1 / 2 ≤ nrm p := le_of_lt (not_le.mp hp)
      have hq' : 1 / 2 ≤ nrm q := le_of_lt (not_le.mp hq)
      have hb : 0 < beta (cuspX v (u q) y) := beta_pos _
      have hbne : beta (cuspX v (u q) y) ≠ sJ :=
        ne_of_lt (lt_of_le_of_lt (beta_le_max _) betaMax_lt_sJ)
      have hcs : collarHeight (nrm p) (beta (cuspX v (u p) y))
          = collarHeight (nrm q) (beta (cuspX v (u q) y)) := by
        have h := hr
        rw [radial_collar v p y hp', radial_collar v q y hq'] at h
        have hlog : Real.log (collarS v p y) = Real.log (collarS v q y) := by linarith
        rw [collarS, collarS] at hlog
        have h1 : 0 < collarHeight (nrm p) (beta (cuspX v (u p) y)) :=
          collarHeight_pos _ _ (beta_pos _)
        have h2 : 0 < collarHeight (nrm q) (beta (cuspX v (u q) y)) :=
          collarHeight_pos _ _ (beta_pos _)
        rw [← Real.exp_log h1, ← Real.exp_log h2, hlog]
      rw [hu] at hcs
      exact collarHeight_inj (nrm p) (nrm q) (beta (cuspX v (u q) y)) hb hbne hcs

/-! ### Injectivity of the core chart -/

/-- **The core chart `Θ_v` is injective on all of `E2 × E2`.** -/
theorem ThetaCore_injOn (v : Fin 5) : Set.InjOn (fun z : E2 × E2 => ThetaCore v z.1 z.2) Set.univ := by
  intro z1 _ z2 _ h
  obtain ⟨p, y⟩ := z1
  obtain ⟨q, y'⟩ := z2
  change ThetaCore v p y = ThetaCore v q y' at h
  -- ### Step 1: the `w`-coordinates determine `y`
  have h2 : wOf v y 0 = wOf v y' 0 := by
    have hh := congrArg (fun z : E4 => z 2) h
    rwa [ThetaCore_two, ThetaCore_two] at hh
  have h3 : wOf v y 1 = wOf v y' 1 := by
    have hh := congrArg (fun z : E4 => z 3) h
    rwa [ThetaCore_three, ThetaCore_three] at hh
  have hy : y = y' := by
    have hw : wOf v y = wOf v y' := by
      ext i
      fin_cases i
      · exact h2
      · exact h3
    rw [← invY_wOf v y, hw, invY_wOf v y']
  rw [← hy] at h
  -- ### Step 2: the first two coordinates determine the radial coordinate
  have h0 : radial v p y * Real.cos (thetaAng v p y) = radial v q y * Real.cos (thetaAng v q y) := by
    have hh := congrArg (fun z : E4 => z 0) h
    rwa [ThetaCore_zero, ThetaCore_zero] at hh
  have h1 : radial v p y * Real.sin (thetaAng v p y) = radial v q y * Real.sin (thetaAng v q y) := by
    have hh := congrArg (fun z : E4 => z 1) h
    rwa [ThetaCore_one, ThetaCore_one] at hh
  have hsq : ∀ (r θ : ℝ), r ^ 2 = (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 := by
    intro r θ
    rw [mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one]
  have hr2 : radial v p y ^ 2 = radial v q y ^ 2 := by
    rw [hsq (radial v p y) (thetaAng v p y), hsq (radial v q y) (thetaAng v q y), h0, h1]
  have hr : radial v p y = radial v q y := by
    have hfac : (radial v p y - radial v q y) * (radial v p y + radial v q y) = 0 := by nlinarith [hr2]
    rcases mul_eq_zero.mp hfac with hh | hh
    · linarith
    · have hp := radial_nonneg v p y
      have hq := radial_nonneg v q y
      linarith
  -- ### Step 3: the core point
  by_cases hr0 : radial v p y = 0
  · have hp0 : nrm p = 0 := by
      by_cases hp : nrm p ≤ 1 / 2
      · have hh : 2 * rJ * nrm p = 0 := by rw [← radial_eq_inner v p y hp]; exact hr0
        rw [rJ] at hh
        linarith
      · have hh := rJ_lt_radial v p y (not_le.mp hp)
        rw [rJ] at hh
        linarith
    have hq0 : nrm q = 0 := by
      rw [hr] at hr0
      by_cases hq : nrm q ≤ 1 / 2
      · have hh : 2 * rJ * nrm q = 0 := by rw [← radial_eq_inner v q y hq]; exact hr0
        rw [rJ] at hh
        linarith
      · have hh := rJ_lt_radial v q y (not_le.mp hq)
        rw [rJ] at hh
        linarith
    exact Prod.ext (by rw [nrmu_nrm_eq_zero hp0, nrmu_nrm_eq_zero hq0]) hy
  · -- ### Step 4: off the core, the angle and `‖p‖∞` are determined
    have hrpos : 0 < radial v p y := lt_of_le_of_ne (radial_nonneg v p y) (Ne.symm hr0)
    have hcos : Real.cos (thetaAng v p y) = Real.cos (thetaAng v q y) := by
      have hh : radial v p y * Real.cos (thetaAng v p y)
          = radial v p y * Real.cos (thetaAng v q y) := by rw [h0, ← hr]
      exact mul_left_cancel₀ (ne_of_gt hrpos) hh
    have hsin : Real.sin (thetaAng v p y) = Real.sin (thetaAng v q y) := by
      have hh : radial v p y * Real.sin (thetaAng v p y)
          = radial v p y * Real.sin (thetaAng v q y) := by rw [h1, ← hr]
      exact mul_left_cancel₀ (ne_of_gt hrpos) hh
    have hu : u p = u q := u_eq_of_angle v p q y hcos hsin
    have hn : nrm p = nrm q := nrm_eq_of_radial_eq v p q y hu hr
    exact Prod.ext (nrm_u_inj p q hn hu) hy

end Work.Cusp
