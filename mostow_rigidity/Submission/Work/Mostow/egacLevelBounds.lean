import Mathlib
import Submission.Work.Mostow.levYcFormula
import Submission.Work.Mostow.hptOf_level
import Submission.Work.Mostow.hptOf_yc
import Submission.Work.Mostow.StabHorosphereBase

/-!
# Level and flat-coordinate bounds near a horosphere point

Let `ξ ∈ Sph n` be a boundary point and `L > 0`.  The point `w = hptOf ξ 0 L` is the point of the
horosphere of `ξ` at level `L` whose normalised flat coordinate is `0` (this is `hptOf_level`).
For any point `u` of `ℍⁿ` at hyperbolic distance `≤ 1` from `w` we show

* `lev ξ u ≤ exp 1 * L`  (the level cannot have grown by more than `e`), and
* `‖yc ξ u‖ ≤ 4 / L`     (the flat coordinate stays bounded).

Both come from the horospherical form of the hyperbolic distance (`levYcFormula`)

`cosh (hdist u w) = cosh (log (lev ξ u / lev ξ w)) + (lev ξ u * lev ξ w / 2) ‖yc ξ u - yc ξ w‖²`,

which for `lev ξ w = L`, `yc ξ w = 0` reads
`cosh (hdist u w) = cosh (log (lev ξ u / L)) + (lev ξ u * L / 2) ‖yc ξ u‖²`.
Since `hdist u w ≤ 1`, the left side is at most `cosh 1`; each of the two summands is separately at
most `cosh 1`, and each is bounded below (`cosh ≥ 1`, and the second is `≥ 0`).  Hence

* `cosh (log (lev ξ u / L)) ≤ cosh 1`, i.e. `|log (lev ξ u / L)| ≤ 1`, giving
  `lev ξ u ∈ [L/e, Le]`, so `lev ξ u ≤ e L`;
* `(lev ξ u * L / 2) ‖yc ξ u‖² ≤ cosh 1 - 1`, and with `lev ξ u ≥ L/e`,
  `(L * ‖yc ξ u‖)² ≤ 2 e (cosh 1 - 1) = (e - 1)²`, so `‖yc ξ u‖ ≤ (e-1)/L ≤ 4/L`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

variable {n : ℕ}

/-- `2 (cosh 1 - 1) e = (e - 1)²`, the identity behind the flat-coordinate bound. -/
lemma two_mul_cosh_one_sub_one_mul_exp_one :
    2 * (Real.cosh 1 - 1) * Real.exp 1 = (Real.exp 1 - 1) ^ 2 := by
  have h : Real.exp 1 ≠ 0 := Real.exp_ne_zero 1
  rw [Real.cosh_eq, Real.exp_neg]
  field_simp
  ring

theorem egacLevelBounds (n : ℕ) (hI : Submission.Mostow.HypIsometryProp n)
    {ξ : Submission.Mostow.E n} (hξ : ξ ∈ Submission.Mostow.Sph n)
    {L : ℝ} (hL : 0 < L) (u : Submission.Mostow.E n)
    (hu : Submission.Mostow.hdist (Work.Mostow.hptOf ξ 0 L) u ≤ 1) :
    Work.Mostow.lev ξ u ≤ Real.exp 1 * L ∧ ‖Work.Mostow.yc ξ u‖ ≤ 4 / L := by
  have hD : HypIsoData n := HypIsoData.ofProp hI
  set w : E n := hptOf ξ 0 L with hw
  have hlevw : lev ξ w = L := (hptOf_level ξ hξ L hL 0 (by simp)).1
  have hycw : yc ξ w = 0 := (hptOf_level ξ hξ L hL 0 (by simp)).2
  have hdu : hdist w u ≤ 1 := hu
  have hdu0 : 0 ≤ hdist w u := hD.nonneg w u
  have hcosh : Real.cosh (hdist w u) ≤ Real.cosh 1 :=
    Real.cosh_le_cosh.mpr (by rw [abs_of_nonneg hdu0, abs_one]; exact hdu)
  -- the horospherical distance formula, evaluated at `w`
  have hkey : Real.cosh (hdist w u) =
      Real.cosh (Real.log (lev ξ u / L)) + (lev ξ u * L / 2) * ‖yc ξ u‖ ^ 2 := by
    have h := levYcFormula (ξ := ξ) hξ u w
    rw [hD.symm u w, hlevw, hycw, sub_zero] at h
    exact h
  have hApos : 0 < lev ξ u := lev_pos ξ hξ u
  have hAne : lev ξ u ≠ 0 := ne_of_gt hApos
  have h1 : (1 : ℝ) ≤ Real.cosh (Real.log (lev ξ u / L)) := Real.one_le_cosh _
  have h2 : 0 ≤ (lev ξ u * L / 2) * ‖yc ξ u‖ ^ 2 := by positivity
  have hterm1 : Real.cosh (Real.log (lev ξ u / L)) ≤ Real.cosh 1 := by
    linarith [hkey, hcosh, h2]
  have hterm2 : (lev ξ u * L / 2) * ‖yc ξ u‖ ^ 2 ≤ Real.cosh 1 - 1 := by
    linarith [hkey, hcosh, h1]
  -- the level lies between `L / e` and `L * e`
  have hlogabs : |Real.log (lev ξ u / L)| ≤ 1 := by
    have h := Real.cosh_le_cosh.mp hterm1
    rwa [abs_one] at h
  have hlog_up : Real.log (lev ξ u / L) ≤ 1 := le_trans (le_abs_self _) hlogabs
  have hlog_lo : -1 ≤ Real.log (lev ξ u / L) := (abs_le.mp hlogabs).1
  have hratio_pos : 0 < lev ξ u / L := div_pos hApos hL
  have hratio_le : lev ξ u / L ≤ Real.exp 1 := (Real.log_le_iff_le_exp hratio_pos).mp hlog_up
  have hratio_ge : Real.exp (-1) ≤ lev ξ u / L :=
    (Real.le_log_iff_exp_le hratio_pos).mp hlog_lo
  have hlev_le : lev ξ u ≤ Real.exp 1 * L := by
    rw [← div_mul_cancel₀ (lev ξ u) (ne_of_gt hL)]
    exact mul_le_mul_of_nonneg_right hratio_le hL.le
  -- the reciprocal estimate `L / lev ξ u ≤ e`
  have hLdivA : L / lev ξ u ≤ Real.exp 1 := by
    rw [div_le_iff₀ hApos]
    have hthis : Real.exp (-1) * L ≤ lev ξ u := by
      have h := hratio_ge
      rwa [le_div_iff₀ hL] at h
    calc L = Real.exp 1 * (Real.exp (-1) * L) := by
          rw [← mul_assoc, ← Real.exp_add, show (1 : ℝ) + -1 = 0 by norm_num, Real.exp_zero,
            one_mul]
      _ ≤ Real.exp 1 * lev ξ u := mul_le_mul_of_nonneg_left hthis (Real.exp_pos 1).le
  -- the flat-coordinate estimate
  have hterm2b : (lev ξ u * L) * ‖yc ξ u‖ ^ 2 ≤ 2 * (Real.cosh 1 - 1) := by
    have h := hterm2
    have hrw : (lev ξ u * L / 2) * ‖yc ξ u‖ ^ 2 = (lev ξ u * L * ‖yc ξ u‖ ^ 2) / 2 := by ring
    rw [hrw] at h
    linarith
  have hZ : (L * ‖yc ξ u‖) ^ 2 ≤ (Real.exp 1 - 1) ^ 2 := by
    have hLeq : (L / lev ξ u) * (lev ξ u * L * ‖yc ξ u‖ ^ 2) = (L * ‖yc ξ u‖) ^ 2 := by
      have hstep : (L / lev ξ u) * (lev ξ u * L * ‖yc ξ u‖ ^ 2) =
          (L / lev ξ u * lev ξ u) * (L * ‖yc ξ u‖ ^ 2) := by ring
      rw [hstep, div_mul_cancel₀ L hAne]
      ring
    calc (L * ‖yc ξ u‖) ^ 2
        = (L / lev ξ u) * (lev ξ u * L * ‖yc ξ u‖ ^ 2) := hLeq.symm
      _ ≤ (L / lev ξ u) * (2 * (Real.cosh 1 - 1)) :=
            mul_le_mul_of_nonneg_left hterm2b (div_nonneg hL.le hApos.le)
      _ ≤ Real.exp 1 * (2 * (Real.cosh 1 - 1)) :=
            mul_le_mul_of_nonneg_right hLdivA (by linarith [Real.one_le_cosh 1])
      _ = (Real.exp 1 - 1) ^ 2 := by
            rw [← two_mul_cosh_one_sub_one_mul_exp_one]; ring
  have hLnorm : L * ‖yc ξ u‖ ≤ Real.exp 1 - 1 := by
    have h1' : 0 ≤ L * ‖yc ξ u‖ := mul_nonneg hL.le (norm_nonneg _)
    have h2' : 0 ≤ Real.exp 1 - 1 := by
      have h := Real.exp_le_exp.mpr (show (0 : ℝ) ≤ 1 by norm_num)
      rw [Real.exp_zero] at h
      linarith
    have h := sq_le_sq.mp hZ
    rwa [abs_of_nonneg h1', abs_of_nonneg h2'] at h
  have hexp1 : Real.exp 1 - 1 ≤ 4 := by linarith [Real.exp_one_lt_three]
  have hyc_le : ‖yc ξ u‖ ≤ (Real.exp 1 - 1) / L := by
    rw [le_div_iff₀ hL, mul_comm]
    exact hLnorm
  exact ⟨hlev_le, le_trans hyc_le (div_le_div_of_nonneg_right hexp1 hL.le)⟩

end Work.Mostow
