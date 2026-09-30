/-
# The core chart is a left inverse of `cuspInvCore`

`ThetaCore v p y = (r cos θ, r sin θ, w₁, w₂)` is the Cartesian form of the inner (polar) chart of
the `v`-th cusp, and `cuspInvCore v q` (`Work.Cusp.Basic`) is its explicit inverse: for
`q = (a, b, w₁, w₂)` it recovers the polar data `r = √(a²+b²)`, `θ = atan2 b a` and then runs the
inner-chart inverse `cuspInvInner v (r, θ, w₁, w₂)`.

This file proves the round-trip identity

`ThetaCore v (cuspInvCore v q).1 (cuspInvCore v q).2 = q`  for `q ∈ coreBox`,

i.e. that the Cartesian core chart takes the point recovered by `cuspInvCore` back to `q`.

The two halves of the composite `cuspInvCore` are computed first (`cuspInvCore_fst`,
`cuspInvCore_snd`), and then the four coordinates of `ThetaCore v p y` are matched against those of
`q`:

* `wOf v (invY v w) = w` (`wOf_invY`) gives the two `w`-coordinates;
* `radial v p y = r` is the definitional identity `2 r_J ‖p‖∞ = r` in the core
  (`radial_eq_inner`, `nrm (t • bndOfU u) = t` from `nrm_smul`/`nrm_bndOfU`);
* the angle of `ThetaCore` is `θ' = 2π (frac uu) + 2π c` while that of `cuspInvCore` is
  `θ = 2π uu + 2π c` with `uu = (θ − 2πc)/(2π)` (`uqOf`); the two differ by `2π⌊uu⌋`, so they have
  the same cosine and sine;
* `‖(⟨q 0, q 1⟩ : ℂ)‖ = √(q 0² + q 1²)` and `Complex.norm_mul_cos_arg`/
  `Complex.norm_mul_sin_arg` turn `r cos θ`, `r sin θ` into `q 0`, `q 1`.
-/
import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.wOf_invY
import Submission.Work.Cusp.nrm_smul
import Submission.Work.Cusp.nrm_bndOfU
import Submission.Work.Cusp.uPerim_bndOfU
import Submission.Work.Cusp.u_smul
import Submission.Work.Cusp.radial_eq_inner

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.Cusp

open scoped Real InnerProductSpace

/-- **The first component of the core inverse.**  Unfolding `cuspInvCore` and its inner-chart
inverse `cuspInvInner` on the branch `√(q 0² + q 1²) ≤ r_J`, the recovered point of the filling
square is `t • bndOfU uu` with `t = √(q 0² + q 1²)/(2 r_J)` and `uu = uqOf v (r, θ, q 2, q 3)` the
recovered perimeter coordinate. -/
private lemma cuspInvCore_fst (v : Fin 5) (q : E4)
    (h : Real.sqrt (q 0 ^ 2 + q 1 ^ 2) ≤ rJ) :
    (cuspInvCore v q).1 = (Real.sqrt (q 0 ^ 2 + q 1 ^ 2) / (2 * rJ)) •
      bndOfU (uqOf v
        !₂[Real.sqrt (q 0 ^ 2 + q 1 ^ 2), argOf (q 1) (q 0), q 2, q 3]) := by
  rw [cuspInvCore, cuspInvInner]
  rw [ite_eq_left (by simpa using h)]
  simp only [uqOf, mul_div_assoc, Matrix.cons_val_zero]

/-- **The second component of the core inverse.**  The torus coordinates `y` are recovered from the
`w`-coordinates by `invY v`, independently of the branch taken by `cuspInvInner`. -/
private lemma cuspInvCore_snd (v : Fin 5) (q : E4) :
    (cuspInvCore v q).2 = invY v !₂[q 2, q 3] := by
  rw [cuspInvCore, cuspInvInner]
  simp

/-- The perimeter parameter of the boundary point `bndOfU x` is `Int.fract x`: `bndOfU x` already
lies on `∂Sq` (`nrm_bndOfU`), so `bnd (bndOfU x) = bndOfU x`, and `uPerim (bndOfU x) = Int.fract x`
(`uPerim_bndOfU`). -/
private lemma u_bndOfU (x : ℝ) : u (bndOfU x) = Int.fract x := by
  rw [u, show bnd (bndOfU x) = bndOfU x by rw [bnd, nrm_bndOfU x, inv_one, one_smul]]
  exact uPerim_bndOfU x

/-- For a positive scaling the perimeter parameter is unchanged (`u_smul`), so
`u (t • bndOfU x) = Int.fract x`. -/
private lemma u_smul_bndOfU {t : ℝ} (ht : 0 < t) (x : ℝ) :
    u (t • bndOfU x) = Int.fract x := by
  rw [u_smul ht, u_bndOfU]

theorem ThetaCore_cuspInvCore (v : Fin 5) (q : E4) (hq : q ∈ coreBox) :
    ThetaCore v (cuspInvCore v q).1 (cuspInvCore v q).2 = q := by
  have hrlt : Real.sqrt (q 0 ^ 2 + q 1 ^ 2) < 1 / 2 := hq
  have hle : Real.sqrt (q 0 ^ 2 + q 1 ^ 2) ≤ rJ := by rw [rJ]; linarith
  rw [cuspInvCore_fst v q hle, cuspInvCore_snd v q]
  set r : ℝ := Real.sqrt (q 0 ^ 2 + q 1 ^ 2) with hr_def
  set θ : ℝ := argOf (q 1) (q 0) with hθ_def
  set y : E2 := invY v !₂[q 2, q 3] with hy_def
  set c : ℝ := ⟪cuspY v y, slope v⟫_ℝ / ‖slope v‖ ^ 2 with hc_def
  set uu : ℝ := uqOf v !₂[r, θ, q 2, q 3] with huu_def
  set t : ℝ := r / (2 * rJ) with ht_def
  set p : E2 := t • bndOfU uu with hp_def
  have hrJpos : (0 : ℝ) < rJ := by rw [show rJ = 3 from rfl]; norm_num
  have h2rJpos : (0 : ℝ) < 2 * rJ := by linarith
  have h2rJne : (2 : ℝ) * rJ ≠ 0 := ne_of_gt h2rJpos
  have hrnn : 0 ≤ r := by rw [hr_def]; positivity
  have htnn : 0 ≤ t := by rw [ht_def]; exact div_nonneg hrnn (le_of_lt h2rJpos)
  have hnrmp : nrm p = t := by
    rw [hp_def, nrm_smul, nrm_bndOfU, mul_one, abs_of_nonneg htnn]
  have htp : t ≤ 1 / 2 := by
    rw [ht_def]
    rw [show rJ = 3 from rfl]
    linarith
  have hrad : radial v p y = r := by
    rw [radial_eq_inner v p y (by rw [hnrmp]; exact htp), hnrmp, ht_def,
      mul_comm (2 * rJ) (r / (2 * rJ)), div_mul_cancel₀ r h2rJne]
  have hw : wOf v y = !₂[q 2, q 3] := by
    rw [hy_def]; exact wOf_invY v !₂[q 2, q 3]
  rcases lt_or_eq_of_le hrnn with hpos | hzero
  · have htpos : 0 < t := by rw [ht_def]; exact div_pos hpos h2rJpos
    have hup : u p = Int.fract uu := by
      rw [hp_def]; exact u_smul_bndOfU htpos uu
    have h2pi : (2 : ℝ) * π ≠ 0 := by positivity
    have huu_eq : (2 * π) * uu + 2 * π * c = θ := by
      rw [huu_def, uqOf]
      simp
      rw [← hy_def]
      rw [show (2 * π) * ⟪cuspY v y, slope v⟫_ℝ / ‖slope v‖ ^ 2 = 2 * π * c from by
        rw [hc_def]; ring]
      field_simp
      ring
    have hfract : Int.fract uu = uu - (⌊uu⌋ : ℝ) := by
      linarith [Int.fract_add_floor uu]
    have htheta : thetaAng v p y = θ - ((⌊uu⌋ : ℤ) : ℝ) * (2 * π) := by
      rw [thetaAng, hup, hfract, ← hc_def]
      linear_combination huu_eq
    have hcos : Real.cos (thetaAng v p y) = Real.cos θ := by
      rw [htheta, Real.cos_sub_int_mul_two_pi]
    have hsin : Real.sin (thetaAng v p y) = Real.sin θ := by
      rw [htheta, Real.sin_sub_int_mul_two_pi]
    have hrn : r = ‖(⟨q 0, q 1⟩ : ℂ)‖ := by
      have h2 : ‖(⟨q 0, q 1⟩ : ℂ)‖ ^ 2 = q 0 ^ 2 + q 1 ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
      rw [hr_def, ← h2, Real.sqrt_sq (norm_nonneg _)]
    have hθz : θ = Complex.arg (⟨q 0, q 1⟩ : ℂ) := by rw [hθ_def]; rfl
    have hq0 : r * Real.cos θ = q 0 := by
      rw [hrn, hθz, Complex.norm_mul_cos_arg]
    have hq1 : r * Real.sin θ = q 1 := by
      rw [hrn, hθz, Complex.norm_mul_sin_arg]
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [ThetaCore, hrad, hcos, hq0, hsin, hq1, hw]
  · have hr0 : r = 0 := hzero.symm
    have hsq : q 0 ^ 2 + q 1 ^ 2 = 0 := by
      have hs : Real.sqrt (q 0 ^ 2 + q 1 ^ 2) = 0 := by rw [← hr_def, hr0]
      have h2 : (Real.sqrt (q 0 ^ 2 + q 1 ^ 2)) ^ 2 = q 0 ^ 2 + q 1 ^ 2 :=
        Real.sq_sqrt (by positivity)
      rw [← h2, hs]; ring
    have hq0 : q 0 = 0 := by nlinarith [sq_nonneg (q 0), sq_nonneg (q 1)]
    have hq1 : q 1 = 0 := by nlinarith [sq_nonneg (q 0), sq_nonneg (q 1)]
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [ThetaCore, hrad, hr0, hq0, hq1, hw]

end Work.Cusp
