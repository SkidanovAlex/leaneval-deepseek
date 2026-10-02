import Mathlib
import Submission.Work.Implosion.All
import Submission.Work.Implosion.Approx
import Submission.Work.PARIMPL2.Direct.approxEcal_re_level
import Submission.Work.PARIMPL2.Direct.sinh_chart_norm

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The exit threshold of the approximate Écalle coordinate (drift form `exp(…)(…+32)`)

`approxEcal a κ u = u + κ * log (sinh (a*u)/a)` is the approximate perturbed Fatou
coordinate of the implosion chapter (`Submission/Work/Implosion/Approx.lean`).  For
`a = iλ` (`λ > 0`) and `u` in the exit window `R/4 ≤ Re u ≤ R/4 + 4` we show

  `Re (approxEcal (iλ) κ u) ≤ R + 2`

whenever `λ R² ≤ 1`, `R ≥ 128`, `|Im κ| ≤ 1/4`, `‖κ‖ (1 + log R) ≤ 3R/4`, and `Im u`
obeys the drift bound

  `|Im u| ≤ exp (40 max (Re h₁) 0 / R) *`
        `(2H + 8 + log R + 8 |Im (τ²−h₁)| (1 + log R) + 20A/R + 32)`

with `κ = τ − h₁/τ`, `‖τ−1‖ ≤ 1/8`, `|Im(τ²−h₁)| ≤ 1/2`, `8(H+2) ≤ R`, `16A/R² ≤ 3/8`.

Two estimates.

* **Case `Re κ ≤ 0`.**  The level identity `Re W = Re u + Re κ·log‖Z‖ − Im κ·arg Z`
  (`Direct.approxEcal_re_level`) plus `‖Z‖ ≥ 1` (so `log ‖Z‖ ≥ 0`) gives
  `Re W ≤ Re u + |Im κ| π ≤ R/4 + 4 + π/4 ≤ R + 2`; no drift hypothesis is needed.

* **Case `Re κ > 0`.**  Then `h₁ = τ² − τκ` and `τ = 1 + δ`, `‖δ‖ ≤ 1/8`, give
  `Re h₁ ≤ 83/64 − (7/8) Re κ ≤ 83/64`, hence `exp (40 max (Re h₁) 0 / R) ≤ 7/4`.
  Combining this with the explicit bounds `2H + 8 ≤ R/4 + 4`, `log R ≤ R/128 + 3.853`,
  `8 |Im(τ²−h₁)| (1 + log R) ≤ 4 (1 + log R)` and `20A/R ≤ 15R/32` yields
  `|Im u| ≤ (7/4)(97R/128 + 60) ≤ 9R/4`.
  The exact chart formula `‖Z‖² = (sin²(λ Re u) + sinh²(λ Im u))/λ²`
  (`Direct.sinh_chart_norm`) then gives `‖Z‖² ≤ 5.15 R²`, so `log ‖Z‖ ≤ log R + 33/40`.
  With `Re κ ≤ 3R/(4(1+log R))` the key numeric inequality
  `(3R/(4(1+log R)))(log R + 33/40) ≤ 3R/4 − (2 + π/4)`
  (`Direct`-style arithmetic from `(1 + log R)/R` small) closes the estimate.
-/

set_option maxHeartbeats 4000000

namespace Work.PARIMPL2.Direct

open Complex

/-! ## Elementary real-analysis helpers -/

private lemma val_sinh_le_mul_cosh (s : ℝ) (hs : 0 ≤ s) :
    Real.sinh s ≤ s * Real.cosh s := by
  have hmono : MonotoneOn (fun s : ℝ => s * Real.cosh s - Real.sinh s) (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact ((continuous_id.mul Real.continuous_cosh).sub Real.continuous_sinh).continuousOn
    · intro x hx
      exact ((differentiableAt_id.mul Real.differentiableAt_cosh).sub
        Real.differentiableAt_sinh).differentiableWithinAt
    · intro x hx
      rw [interior_Ici, Set.mem_Ioi] at hx
      have hd : HasDerivAt (fun s : ℝ => s * Real.cosh s - Real.sinh s) (x * Real.sinh x) x := by
        have h1 : HasDerivAt (fun s : ℝ => s * Real.cosh s)
            (1 * Real.cosh x + x * Real.sinh x) x :=
          (hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)
        have h2 : HasDerivAt Real.sinh (Real.cosh x) x := Real.hasDerivAt_sinh x
        convert h1.sub h2 using 1
        ring
      rw [hd.deriv]
      exact mul_nonneg hx.le (Real.sinh_nonneg_iff.mpr hx.le)
  have h := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hs) hs
  simp only [zero_mul, Real.cosh_zero, Real.sinh_zero, sub_zero] at h
  linarith

/-- `cosh t * (1 - t²/2) ≤ 1` for `0 ≤ t ≤ 1`. -/
private lemma val_cosh_mul_le_one (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    Real.cosh t * (1 - t ^ 2 / 2) ≤ 1 := by
  have hmono : MonotoneOn (fun t : ℝ => 1 - Real.cosh t * (1 - t ^ 2 / 2)) (Set.Icc 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) ?_ ?_ ?_
    · exact (continuous_const.sub (Real.continuous_cosh.mul
        (continuous_const.sub (continuous_id.pow 2 |>.div_const 2)))).continuousOn
    · intro x hx
      exact ((Real.differentiableAt_cosh).mul
        ((differentiableAt_id.pow 2 |>.div_const 2).const_sub 1)).const_sub 1
        |>.differentiableWithinAt
    · intro x hx
      rw [interior_Icc, Set.mem_Ioo] at hx
      have hd : HasDerivAt (fun t : ℝ => 1 - Real.cosh t * (1 - t ^ 2 / 2))
          (x * Real.cosh x - Real.sinh x * (1 - x ^ 2 / 2)) x := by
        have h2 : HasDerivAt (fun t : ℝ => (1 - t ^ 2 / 2)) (-x) x := by
          have hp : HasDerivAt (fun t : ℝ => t ^ 2 / 2) x x := by
            have hh : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
              have h := (hasDerivAt_id x).pow 2
              convert h using 1
              · funext t; simp [id_eq]
              · simp
            have h2' := hh.div_const 2
            convert h2' using 1
            ring
          have := (hasDerivAt_const x (1:ℝ)).sub hp
          convert this using 1
          ring
        have h1 : HasDerivAt Real.cosh (Real.sinh x) x := Real.hasDerivAt_cosh x
        have h3 := h1.mul h2
        have h4 := (hasDerivAt_const x (1:ℝ)).sub h3
        convert h4 using 1
        ring
      rw [hd.deriv]
      have hs0 : 0 ≤ Real.sinh x := Real.sinh_nonneg_iff.mpr hx.1.le
      have hx2 : x ^ 2 / 2 ≤ 1 := by nlinarith [hx.2.le]
      have hle : Real.sinh x * (1 - x^2/2) ≤ Real.sinh x := by nlinarith [hs0, hx2, sq_nonneg x]
      have h2 := val_sinh_le_mul_cosh x hx.1.le
      linarith
  have h := hmono (Set.mem_Icc.mpr ⟨le_rfl, zero_le_one⟩) (Set.mem_Icc.mpr ⟨h0,h1⟩) h0
  simpa using h

/-- `cosh t ≤ 1 + t²` for `0 ≤ t ≤ 1`. -/
private lemma val_cosh_le_one_add_sq (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    Real.cosh t ≤ 1 + t^2 := by
  have h := val_cosh_mul_le_one t h0 h1
  have hpos : 0 < 1 - t^2/2 := by nlinarith
  have h2 : Real.cosh t ≤ 1/(1 - t^2/2) := (le_div_iff₀ hpos).mpr h
  have h3 : 1/(1 - t^2/2) ≤ 1 + t^2 := by
    rw [div_le_iff₀ hpos]
    rw [show (1 + t^2) * (1 - t^2/2) = 1 + t^2/2 - t^4/2 by ring]
    have h2' : t^2 ≤ 1 := by nlinarith
    have h4 : t^4 ≤ t^2 := by nlinarith [sq_nonneg t, h2', sq_nonneg (t^2)]
    linarith
  linarith

/-- `|sinh t| ≤ |t| (1 + t²)` for `|t| ≤ 1`. -/
private lemma val_abs_sinh_le (t : ℝ) (ht : |t| ≤ 1) :
    |Real.sinh t| ≤ |t| * (1 + t^2) := by
  rw [Real.abs_sinh]
  have h0 : 0 ≤ |t| := abs_nonneg t
  have h1 : Real.sinh |t| ≤ |t| * Real.cosh |t| := val_sinh_le_mul_cosh |t| h0
  have h2 : Real.cosh |t| ≤ 1 + |t|^2 := val_cosh_le_one_add_sq |t| h0 ht
  have h3 : |t|^2 = t^2 := sq_abs t
  nlinarith [h1, h2, h0]

/-! ## Numeric facts -/

private lemma val_log128_le : Real.log 128 ≤ 4.853 := by
  have h : (128:ℝ) = 2^7 := by norm_num
  rw [h, Real.log_pow]
  nlinarith [Real.log_two_lt_d9]

private lemma val_log_le_linear (R : ℝ) (hR : 128 ≤ R) : Real.log R ≤ R/128 + 3.853 := by
  have hR0 : 0 < R := by linarith
  have h1 : Real.log 128 ≤ 4.853 := val_log128_le
  have h2 : Real.log (R/128) ≤ R/128 - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have h3 : Real.log R = Real.log 128 + Real.log (R/128) := by
    rw [← Real.log_mul (by norm_num : (128:ℝ) ≠ 0) (by positivity : (R/128) ≠ 0)]
    congr 1
    ring
  linarith

private lemma val_exp_half_le : Real.exp (1/2) ≤ 7/4 := by
  have h5 : Real.exp (1/2)^2 = Real.exp 1 := by
    rw [sq, ← Real.exp_add]; norm_num
  nlinarith [h5, Real.exp_one_lt_three, Real.exp_pos (1/2)]

/-- `log 5.15 ≤ 33/20`, so `(log ‖Z‖²)/2 ≤ log R + 33/40` when `‖Z‖² ≤ 5.15 R²`. -/
private lemma val_log_515_le : Real.log (5.15:ℝ) ≤ 33/20 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 33/20) 7
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

/-! ## The chart point `Z = sinh(iλu)/(iλ)` -/

/-- `|sinh t| ≤ |t| (1 + t²)` in the specific form used for the chart bound. -/
private lemma val_chart_norm_sq_le_M (lam M : ℝ) (hlam : 0 < lam) (hM0 : 0 ≤ M)
    (hlamM : lam * M ≤ 1/32) (u : ℂ) (hy : |u.im| ≤ M) :
    ‖Complex.sinh ((lam:ℂ)*Complex.I*u) / ((lam:ℂ)*Complex.I)‖^2
      ≤ u.re^2 + M^2*(1+(lam*M)^2)^2 := by
  rw [sinh_chart_norm]
  have hsin : Real.sin (lam*u.re)^2 ≤ (lam*u.re)^2 := by
    rw [← sq_abs (Real.sin (lam*u.re)), ← sq_abs (lam*u.re)]
    exact pow_le_pow_left₀ (abs_nonneg _) Real.abs_sin_le_abs 2
  have hlamM1 : lam * M ≤ 1 := by linarith
  have hyabs : |lam * u.im| ≤ lam * M := by
    rw [abs_mul, abs_of_pos hlam]
    exact mul_le_mul_of_nonneg_left hy hlam.le
  have hy1 : |lam * u.im| ≤ 1 := le_trans hyabs hlamM1
  have hsinh_abs : |Real.sinh (lam*u.im)| ≤ lam*M*(1+(lam*M)^2) := by
    have h := val_abs_sinh_le (lam*u.im) hy1
    have h1 : 1 + (lam*u.im)^2 ≤ 1 + (lam*M)^2 := by
      have hh : (lam*u.im)^2 ≤ (lam*M)^2 := by
        calc (lam*u.im)^2 = |lam*u.im|^2 := (sq_abs _).symm
          _ ≤ (lam*M)^2 := pow_le_pow_left₀ (abs_nonneg _) hyabs 2
      linarith
    have h2 : |lam*u.im| * (1+(lam*u.im)^2) ≤ (lam*M) * (1+(lam*u.im)^2) :=
      mul_le_mul_of_nonneg_right hyabs (by positivity)
    have h3 : (lam*M)*(1+(lam*u.im)^2) ≤ (lam*M)*(1+(lam*M)^2) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith
  have hsinh : Real.sinh (lam*u.im)^2 ≤ (lam*M*(1+(lam*M)^2))^2 := by
    rw [← sq_abs (Real.sinh (lam*u.im))]
    exact pow_le_pow_left₀ (abs_nonneg _) hsinh_abs 2
  rw [div_le_iff₀ (by positivity : (0:ℝ) < lam^2)]
  nlinarith [hsin, hsinh, hlam, sq_nonneg lam]

/-- The chart point of the exit window with the drift bound `|Im u| ≤ 9R/4` has
`‖Z‖² ≤ 5.15 R²`. -/
private lemma val_chart_norm_sq_le_515 (lam R : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R)
    (hlamR : lam * R^2 ≤ 1) (u : ℂ) (hx1 : R/4 ≤ u.re) (hx2 : u.re ≤ R/4 + 4)
    (hy : |u.im| ≤ 9*R/4) :
    ‖Complex.sinh ((lam:ℂ)*Complex.I*u) / ((lam:ℂ)*Complex.I)‖^2 ≤ 5.15*R^2 := by
  have hR0 : 0 < R := by linarith
  have hM0 : 0 ≤ 9*R/4 := by linarith
  have hlam_le : lam ≤ 1/R^2 := by rw [le_div_iff₀ (by positivity)]; linarith
  have hlamM : lam * (9*R/4) ≤ 1/32 := by
    have h1 : lam * (9*R/4) ≤ (1/R^2)*(9*R/4) :=
      mul_le_mul_of_nonneg_right hlam_le (by linarith)
    have h2 : (1/R^2)*(9*R/4) = 9/(4*R) := by field_simp
    have h3 : 9/(4*R) ≤ 1/32 := by rw [div_le_iff₀ (by positivity)]; linarith
    linarith
  have hbase := val_chart_norm_sq_le_M lam (9*R/4) hlam hM0 hlamM u hy
  have hlt : lam*(9*R/4) ≤ 9/512 := by
    have h2 : lam*(9*R/4) ≤ (1/R^2)*(9*R/4) :=
      mul_le_mul_of_nonneg_right hlam_le (by linarith)
    have h3 : (1/R^2)*(9*R/4) = 9/(4*R) := by field_simp
    have h4 : 9/(4*R) ≤ 9/512 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith
  have hsq : (lam*(9*R/4))^2 ≤ (9/512)^2 := pow_le_pow_left₀ (by positivity) hlt 2
  have hfac : (1+(lam*(9*R/4))^2)^2 ≤ 1.001 := by
    have h6 : 1 + (lam*(9*R/4))^2 ≤ 1 + (9/512)^2 := by linarith
    nlinarith [h6, sq_nonneg (lam*(9*R/4))]
  have hM2 : (9*R/4)^2 * (1+(lam*(9*R/4))^2)^2 ≤ (9*R/4)^2 * 1.001 :=
    mul_le_mul_of_nonneg_left hfac (by positivity)
  have hure : u.re^2 ≤ (9*R/32)^2 := by
    have h1 : R/4+4 ≤ 9*R/32 := by linarith
    have h2 : 0 ≤ u.re := by linarith
    nlinarith [hx1, hx2, h1, h2]
  nlinarith [hbase, hM2, hure, hR]

/-- `1 ≤ ‖sinh(iλu)/(iλ)‖` on the exit window. -/
private lemma val_one_le_chart (lam R : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R) (hlamR : lam*R^2 ≤ 1)
    (u : ℂ) (hx1 : R/4 ≤ u.re) (hx2 : u.re ≤ R/4+4) :
    1 ≤ ‖Complex.sinh ((lam:ℂ)*Complex.I*u)/((lam:ℂ)*Complex.I)‖ := by
  have hR0 : 0 < R := by linarith
  have hx0 : 0 < u.re := by linarith
  have hlam_le : lam ≤ 1/R^2 := by rw [le_div_iff₀ (by positivity)]; linarith
  have hlx0 : 0 < lam*u.re := mul_pos hlam hx0
  have hlx1 : lam*u.re ≤ Real.pi/2 := by
    have h1 : lam*u.re ≤ lam*(R/4+4) := mul_le_mul_of_nonneg_left hx2 hlam.le
    have h2 : lam*(R/4+4) ≤ (1/R^2)*(R/4+4) :=
      mul_le_mul_of_nonneg_right hlam_le (by linarith)
    have h3 : (1/R^2)*(R/4+4) ≤ Real.pi/2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [Real.pi_gt_three, hR]
    linarith
  have hsinlb : (2/Real.pi)*(lam*u.re) ≤ Real.sin (lam*u.re) := Real.mul_le_sin hlx0.le hlx1
  have hkey : (1:ℝ) ≤ ‖Complex.sinh (((lam:ℂ)*Complex.I)*u)/((lam:ℂ)*Complex.I)‖^2 := by
    rw [sinh_chart_norm]
    rw [le_div_iff₀ (by positivity : (0:ℝ) < lam^2)]
    have h2 : ((2/Real.pi)*(lam*u.re))^2 ≤ Real.sin (lam*u.re)^2 :=
      pow_le_pow_left₀ (by positivity) hsinlb 2
    have h3 : lam^2 ≤ ((2/Real.pi)*(lam*u.re))^2 := by
      have hpi2 : 2/Real.pi*(Real.pi/2) = 1 := by field_simp
      have hx : Real.pi/2 ≤ u.re := by nlinarith [Real.pi_lt_four, hx1, hR]
      have h1 : lam ≤ 2/Real.pi*(lam*u.re) := by
        calc lam = lam*1 := by ring
          _ = lam*(2/Real.pi*(Real.pi/2)) := by rw [hpi2]
          _ ≤ lam*(2/Real.pi*u.re) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx (by positivity)) hlam.le
          _ = 2/Real.pi*(lam*u.re) := by ring
      exact pow_le_pow_left₀ hlam.le h1 2
    nlinarith [h2, h3, sq_nonneg (Real.sinh (lam*u.im)), sq_nonneg lam]
  nlinarith [hkey, norm_nonneg (Complex.sinh (((lam:ℂ)*Complex.I)*u)/((lam:ℂ)*Complex.I))]

/-- The logarithm of the chart point is bounded by `log R + 33/40`, from the drift
bound `|Im u| ≤ 9R/4`. -/
private lemma val_log_chart_le (lam R : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R) (hlamR : lam*R^2 ≤ 1)
    (u : ℂ) (hx1 : R/4 ≤ u.re) (hx2 : u.re ≤ R/4+4) (hy : |u.im| ≤ 9*R/4) :
    Real.log ‖Complex.sinh (((lam:ℂ)*Complex.I)*u)/((lam:ℂ)*Complex.I)‖ ≤ Real.log R + 33/40 := by
  set Z : ℂ := Complex.sinh (((lam:ℂ)*Complex.I)*u)/((lam:ℂ)*Complex.I) with hZdef
  have hge1 : 1 ≤ ‖Z‖ := by rw [hZdef]; exact val_one_le_chart lam R hlam hR hlamR u hx1 hx2
  have hZ2 : ‖Z‖^2 ≤ 5.15*R^2 := by
    rw [hZdef]; exact val_chart_norm_sq_le_515 lam R hlam hR hlamR u hx1 hx2 hy
  have hlog : Real.log (‖Z‖^2) ≤ Real.log (5.15*R^2) := Real.log_le_log (by nlinarith) hZ2
  rw [Real.log_pow, Real.log_mul (by norm_num : (5.15:ℝ) ≠ 0) (by positivity : (R^2:ℝ) ≠ 0),
    Real.log_pow] at hlog
  have h515 : Real.log (5.15:ℝ) ≤ 33/20 := val_log_515_le
  have hlogR0 : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
  linarith

/-! ## The key numeric inequality -/

/-- `(3R/(4(1+log R)))(log R + 33/40) ≤ 3R/4 − (2 + π/4)` for `R ≥ 128`. -/
private lemma val_key (R : ℝ) (hR : 128 ≤ R) :
    (3*R/(4*(1+Real.log R))) * (Real.log R + 33/40) ≤ 3*R/4 - (2 + Real.pi/4) := by
  have hR0 : 0 < R := by linarith
  have hlog : Real.log R ≤ R/128 + 3.853 := val_log_le_linear R hR
  have hLpos : 0 < 1 + Real.log R := by
    have h := Real.log_nonneg (show (1:ℝ) ≤ R by linarith); linarith
  have hlin : 1 + Real.log R ≤ (59/1280)*R := by nlinarith [hlog, hR]
  have hpi : 2 + Real.pi/4 ≤ 2.7875 := by nlinarith [Real.pi_lt_d2]
  have hnum : (2 + Real.pi/4)*(1 + Real.log R) ≤ 21*R/160 := by
    have h1 : (2 + Real.pi/4)*(1 + Real.log R) ≤ 2.7875*((59/1280)*R) :=
      mul_le_mul hpi hlin (by linarith) (by norm_num)
    have h2 : 2.7875*((59/1280)*R) ≤ 21*R/160 := by nlinarith [hR0]
    linarith
  have h21 : 2 + Real.pi/4 ≤ 21*R/(160*(1+Real.log R)) := by
    rw [le_div_iff₀ (by positivity)]
    linarith [hnum]
  have hsplit : (3*R/(4*(1+Real.log R))) * (Real.log R + 33/40)
      = 3*R/4 - 21*R/(160*(1+Real.log R)) := by
    field_simp
    ring
  linarith [h21, hsplit.le, hsplit.ge]

/-! ## The target -/

theorem approxEcalReLeAtExit4 (lam R H A : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R) (hlamR : lam * R ^ 2 ≤ 1)
    (τ h1 κ : ℂ) (hτ1 : ‖τ - 1‖ ≤ 1 / 8) (hκ : κ = τ - h1 / τ) (hκI : |κ.im| ≤ 1 / 4)
    (hcim : |(τ ^ 2 - h1).im| ≤ 1 / 2)
    (hκlog : ‖κ‖ * (1 + Real.log R) ≤ 3 * R / 4)
    (hH : 0 ≤ H) (hHR : 8 * (H + 2) ≤ R) (hA0 : 0 ≤ A) (hAr : 16 * A / R ^ 2 ≤ 3 / 8)
    (u : ℂ) (hx1 : R / 4 ≤ u.re) (hx2 : u.re ≤ R / 4 + 4)
    (hy : |u.im| ≤ Real.exp (40 * max h1.re 0 / R) *
      (2 * H + 8 + Real.log R + 8 * |(τ ^ 2 - h1).im| * (1 + Real.log R) + 20 * A / R + 32)) :
    (Work.Implosion.approxEcal ((lam : ℂ) * Complex.I) κ u).re ≤ R + 2 := by
  have hR0 : 0 < R := by linarith
  set Z : ℂ := Complex.sinh (((lam:ℂ)*Complex.I)*u) / ((lam:ℂ)*Complex.I) with hZdef
  have hdecomp : (Work.Implosion.approxEcal ((lam:ℂ)*Complex.I) κ u).re
      = u.re + (κ * Complex.log Z).re := by
    rw [Work.Implosion.approxEcal_apply, Complex.add_re, ← hZdef]
  have hlogre : (κ * Complex.log Z).re = κ.re * Real.log ‖Z‖ - κ.im * Z.arg := by
    rw [Complex.mul_re, Complex.log_re, Complex.log_im]
  have hZge1 : 1 ≤ ‖Z‖ := by rw [hZdef]; exact val_one_le_chart lam R hlam hR hlamR u hx1 hx2
  have harg : -κ.im * Z.arg ≤ Real.pi/4 := by
    have h3 : -(κ.im * Z.arg) ≤ |κ.im * Z.arg| := neg_le_abs _
    rw [abs_mul] at h3
    have h4 : |κ.im| * |Z.arg| ≤ (1/4)*Real.pi :=
      mul_le_mul hκI (Complex.abs_arg_le_pi Z) (abs_nonneg _) (by norm_num)
    nlinarith [h3, h4]
  by_cases hkre : κ.re ≤ 0
  · -- Case `Re κ ≤ 0`: no drift hypothesis needed.
    have hlog0 : 0 ≤ Real.log ‖Z‖ := Real.log_nonneg hZge1
    have h1 : κ.re * Real.log ‖Z‖ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hkre hlog0
    rw [hdecomp, hlogre]
    linarith [hx2, h1, harg, Real.pi_lt_four]
  · -- Case `Re κ > 0`.
    simp only [not_le] at hkre
    -- `h1 = τ² - τκ`
    have hτne : τ ≠ 0 := by
      intro h0; rw [h0] at hτ1; norm_num at hτ1
    have hh1 : h1 = τ^2 - τ*κ := by
      have hmul : τ * κ = τ^2 - h1 := by rw [hκ]; field_simp
      calc h1 = τ^2 - (τ^2 - h1) := by ring
        _ = τ^2 - τ*κ := by rw [← hmul]
    -- `Re h1 ≤ 83/64`
    have hh1_64 : h1.re ≤ 83/64 := by
      set δ := τ - 1 with hδdef
      have hτ : τ = 1 + δ := by rw [hδdef]; ring
      have hδn : ‖δ‖ ≤ 1/8 := by rw [hδdef]; simpa using hτ1
      have hexp : h1 = 1 + 2*δ + δ^2 - κ - δ*κ := by
        have htmp : τ^2 - τ*κ = 1 + 2*δ + δ^2 - κ - δ*κ := by rw [hτ]; ring
        rw [hh1, htmp]
      have h1' : h1.re = 1 - κ.re + (2*δ).re + (δ^2).re - (δ*κ).re := by
        rw [hexp]
        simp only [Complex.add_re, Complex.sub_re, Complex.one_re]
        ring
      have hA : (2*δ).re ≤ 1/4 := by
        calc (2*δ).re ≤ ‖2*δ‖ := Complex.re_le_norm _
          _ = 2 * ‖δ‖ := by rw [Complex.norm_mul]; norm_num
          _ ≤ 1/4 := by linarith
      have hB : (δ^2).re ≤ 1/64 := by
        calc (δ^2).re ≤ ‖δ^2‖ := Complex.re_le_norm _
          _ = ‖δ‖^2 := by rw [Complex.norm_pow]
          _ ≤ (1/8)^2 := pow_le_pow_left₀ (norm_nonneg _) hδn 2
          _ = 1/64 := by norm_num
      have hC : -(δ*κ).re ≤ (1/8)*‖κ‖ := by
        have h1'' : -(δ*κ).re ≤ ‖δ*κ‖ := le_trans (neg_le_abs _) (Complex.abs_re_le_norm _)
        rw [Complex.norm_mul] at h1''
        nlinarith [h1'', hδn, norm_nonneg κ]
      have hkn : ‖κ‖ ≤ κ.re + 1/4 := by
        have h1'' : ‖κ‖ ≤ |κ.re| + |κ.im| := Complex.norm_le_abs_re_add_abs_im κ
        rw [abs_of_pos hkre] at h1''
        linarith [h1'', hκI]
      rw [h1']
      linarith [hA, hB, hC, hkn, hkre]
    -- `exp (40 max(Re h1,0)/R) ≤ 7/4`
    have hE : Real.exp (40 * max h1.re 0 / R) ≤ 7/4 := by
      have hmax : max h1.re 0 ≤ 83/64 := max_le hh1_64 (by norm_num)
      have hexp_le : 40 * max h1.re 0 / R ≤ 1/2 := by
        rw [div_le_iff₀ hR0]; nlinarith [hmax, hR]
      have h1' : Real.exp (40 * max h1.re 0 / R) ≤ Real.exp (1/2) := Real.exp_le_exp.mpr hexp_le
      linarith [h1', val_exp_half_le]
    -- the drift allowance `S`
    have hSbound : 2 * H + 8 + Real.log R + 8 * |(τ ^ 2 - h1).im| * (1 + Real.log R) + 20 * A / R + 32
        ≤ 97*R/128 + 60 := by
      have h2H8 : 2 * H + 8 ≤ R/4 + 4 := by linarith [hHR]
      have hlog : Real.log R ≤ R/128 + 3.853 := val_log_le_linear R hR
      have hlog0 : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
      have him : 8 * |(τ ^ 2 - h1).im| * (1 + Real.log R) ≤ 4 * (1 + Real.log R) := by
        have h1' : 8 * |(τ ^ 2 - h1).im| ≤ 4 := by nlinarith [hcim, abs_nonneg ((τ ^ 2 - h1).im)]
        have h2' : 0 ≤ 1 + Real.log R := by linarith
        nlinarith [h1', h2']
      have him2 : 4 * (1 + Real.log R) ≤ 4 + R/32 + 15.412 := by nlinarith [hlog]
      have h20A : 20 * A / R ≤ 15*R/32 := by
        have h1' : A ≤ 3*R^2/128 := by
          rw [div_le_iff₀ (by positivity : (0:ℝ) < R^2)] at hAr
          linarith [hAr]
        have h2' : 20*A/R ≤ 20*(3*R^2/128)/R :=
          div_le_div_of_nonneg_right (by linarith [h1']) (by linarith)
        have h3' : 20*(3*R^2/128)/R = 15*R/32 := by
          rw [div_eq_iff (ne_of_gt hR0)]; ring
        linarith [h2', h3'.le]
      linarith [h2H8, hlog, him, him2, h20A, Real.pi_lt_four]
    have hS0 : 0 ≤ 2 * H + 8 + Real.log R + 8 * |(τ ^ 2 - h1).im| * (1 + Real.log R)
        + 20 * A / R + 32 := by
      have hlog0 : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
      have h8 : 0 ≤ 8 * |(τ ^ 2 - h1).im| * (1 + Real.log R) := by positivity
      have h20 : 0 ≤ 20 * A / R := div_nonneg (by linarith) (by linarith)
      linarith
    -- `|Im u| ≤ 9R/4`
    have him9 : |u.im| ≤ 9*R/4 := by
      calc |u.im| ≤ Real.exp (40 * max h1.re 0 / R) *
            (2 * H + 8 + Real.log R + 8 * |(τ ^ 2 - h1).im| * (1 + Real.log R)
              + 20 * A / R + 32) := hy
        _ ≤ (7/4) * (2 * H + 8 + Real.log R + 8 * |(τ ^ 2 - h1).im| * (1 + Real.log R)
              + 20 * A / R + 32) := mul_le_mul_of_nonneg_right hE hS0
        _ ≤ (7/4) * (97*R/128 + 60) := mul_le_mul_of_nonneg_left hSbound (by norm_num)
        _ ≤ 9*R/4 := by nlinarith [hR]
    -- `log ‖Z‖ ≤ log R + 33/40`
    have hlogZ : Real.log ‖Z‖ ≤ Real.log R + 33/40 := by
      rw [hZdef]; exact val_log_chart_le lam R hlam hR hlamR u hx1 hx2 him9
    -- `Re κ ≤ 3R/(4(1+log R))`
    have hknorm : κ.re ≤ 3*R/(4*(1+Real.log R)) := by
      have hLpos : 0 < 1 + Real.log R := by
        have h := Real.log_nonneg (show (1:ℝ) ≤ R by linarith); linarith
      have h1' : ‖κ‖ ≤ 3*R/(4*(1+Real.log R)) := by
        rw [le_div_iff₀ (by linarith)]; linarith [hκlog]
      linarith [Complex.re_le_norm κ]
    have hkey := val_key R hR
    have hmul : κ.re * Real.log ‖Z‖ ≤ 3*R/4 - (2 + Real.pi/4) := by
      have h1' : κ.re * Real.log ‖Z‖ ≤ κ.re * (Real.log R + 33/40) :=
        mul_le_mul_of_nonneg_left hlogZ (le_of_lt hkre)
      have h2' : κ.re * (Real.log R + 33/40)
          ≤ (3*R/(4*(1+Real.log R))) * (Real.log R + 33/40) :=
        mul_le_mul_of_nonneg_right hknorm (by
          have h := Real.log_nonneg (show (1:ℝ) ≤ R by linarith); linarith)
      linarith [hkey]
    rw [hdecomp, hlogre]
    linarith [hx2, hmul, harg, Real.pi_lt_four]

end Work.PARIMPL2.Direct
