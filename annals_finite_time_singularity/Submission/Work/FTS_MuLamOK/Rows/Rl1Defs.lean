/-
# `Submission/Work/FTS_MuLamOK/Rows/Rl1Defs.lean` — the definitions and elementary lemmas of
the open-class `rl1` estimate

Contents (all in the namespace `Work.FTS_MuLamOK.Rows`):

* `FKaddOpen` — the angular moment `FK` is additive over `F_* + f` for `z > 0`, from
  `SmoothOpen f` and `HkMem α 4 f` only.  This is one of the three inputs of
  `Rl1.splitOpen`.
* `sqrt_div_gam'` — `√(C_A/(γ-1)) = √(10·C_A)·α^{-1/2}` (`γ - 1 = α/10`), the constant
  conversion of the `gg`-rows.
* `alpha_le_sqrt'`, `sq_le_rpow_neg_three_halves` — the two elementary
  `0 < α ≤ 1`-inequalities used by the `sg`-block.
* `rpow_le_Env`, `sqrt_mul_le_Env`, `sq_le_Env` — the rate comparisons against the envelope
  `Env α f = α² + √α·|f|_{ℋ⁴} + α^{-3/2}|f|²_{ℋ⁴}`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.GalFields.RHS.smoothOpen_N_Ftot_gal
import Submission.Work.FTS.GalBasis.cc.L12_add_of_HkMem
import Submission.Work.FTS.NonlinRows.Rl1.tools
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_MuLamOK.Rows

open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **`FK(F_* + f) = FK(F_*) + FK(f)` for `z > 0`**, from `SmoothOpen f` and `HkMem α 4 f`
alone: both θ-slices are integrable on `Iθ` (`Work.Stability.integrableOn_slice_Fstar` and
`GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem`), so the Bochner integral splits
(`Work.FTS.GalFields.RHS.FK_add_of_slices`). -/
theorem FKaddOpen {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) :
    ∀ z : ℝ, 0 < z →
      Work.Construction.FK (fun z θ => Work.Construction.Fstar α z θ + f z θ) z
        = Work.Construction.FK (Work.Construction.Fstar α) z + Work.Construction.FK f z :=
  fun z hz =>
    Work.FTS.GalFields.RHS.FK_add_of_slices (a := Work.Construction.Fstar α) (b := f)
      (ne_of_gt hz) (Work.Stability.integrableOn_slice_Fstar α hα z)
      (Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hso hmem hz)

/-- `√(C_A/(γ-1)) = √(10·C_A)·α^{-1/2}`, since `γ - 1 = α/10`. -/
theorem sqrt_div_gam' {CA α : ℝ} (hCA : 0 ≤ CA) (hα : 0 < α) :
    Real.sqrt (CA / (Work.Spaces.gam α - 1)) = Real.sqrt (10 * CA) * α ^ (-(1 / 2 : ℝ)) := by
  have hα0 : α ≠ 0 := ne_of_gt hα
  have hγ : Work.Spaces.gam α - 1 = α / 10 := Work.Spaces.gam_sub_one α
  have h10 : (0 : ℝ) ≤ 10 * CA := by linarith
  have hsq : (Real.sqrt (10 * CA) * α ^ (-(1 / 2 : ℝ))) ^ 2 = CA / (Work.Spaces.gam α - 1) := by
    rw [mul_pow, Real.sq_sqrt h10, ← Real.rpow_two, ← Real.rpow_mul hα.le,
      show -(1 / 2 : ℝ) * 2 = -1 by norm_num, Real.rpow_neg_one, hγ]
    field_simp
  rw [← hsq, Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hα.le _))]

/-- `α ≤ √α` for `0 < α ≤ 1`. -/
theorem alpha_le_sqrt' {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) : α ≤ Real.sqrt α := by
  have hsq : Real.sqrt α ^ 2 = α := Real.sq_sqrt hα.le
  have hle1 : Real.sqrt α ≤ 1 := Real.sqrt_le_one.mpr hα1
  nlinarith [Real.sqrt_nonneg α]

/-- `α² ≤ α^{-3/2}` for `0 < α ≤ 1`. -/
theorem sq_le_rpow_neg_three_halves {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    α ^ 2 ≤ α ^ (-(3 / 2 : ℝ)) := by
  have h := Real.rpow_le_rpow_of_exponent_ge hα hα1 (show (-(3 / 2 : ℝ)) ≤ 2 by norm_num)
  rw [Real.rpow_two] at h
  simpa only [pow_two] using h

/-- `α^p·X² ≤ Env α f` for `p ≥ -3/2` (in particular `p = ∓1/2`), `0 < α ≤ 1`,
`X = |f|_{ℋ⁴}`. -/
theorem rpow_le_Env {α : ℝ} {f : Fn} {p : ℝ} (hp : -(3 / 2 : ℝ) ≤ p)
    (hα : 0 < α) (hα1 : α ≤ 1) :
    α ^ p * (Work.FTS.Nonlin.Xn α f) ^ 2 ≤ Work.FTS.NonlinRows.Rl1.Env α f := by
  have hX : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
  have hr : α ^ p ≤ α ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hα hα1 hp
  have h1 : α ^ p * (Work.FTS.Nonlin.Xn α f) ^ 2
      ≤ α ^ (-(3 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α f) ^ 2 :=
    mul_le_mul_of_nonneg_right hr (sq_nonneg _)
  have h2 : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α f) ^ 2 :=
    mul_nonneg (Real.rpow_nonneg hα.le _) (sq_nonneg _)
  have h3 : (0 : ℝ) ≤ Real.sqrt α * Work.FTS.Nonlin.Xn α f :=
    mul_nonneg (Real.sqrt_nonneg α) hX
  have h4 : (0 : ℝ) ≤ α ^ 2 := sq_nonneg α
  rw [Work.FTS.NonlinRows.Rl1.Env]
  linarith

/-- `√α·X ≤ Env α f`, `X = |f|_{ℋ⁴}`. -/
theorem sqrt_mul_le_Env {α : ℝ} {f : Fn} (hα : 0 < α) (hα1 : α ≤ 1) :
    Real.sqrt α * Work.FTS.Nonlin.Xn α f ≤ Work.FTS.NonlinRows.Rl1.Env α f := by
  have hX : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
  have h1 : (0 : ℝ) ≤ α ^ 2 := sq_nonneg α
  have h2 : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α f) ^ 2 :=
    mul_nonneg (Real.rpow_nonneg hα.le _) (sq_nonneg _)
  rw [Work.FTS.NonlinRows.Rl1.Env]
  linarith

/-- `α² ≤ Env α f`. -/
theorem sq_le_Env {α : ℝ} {f : Fn} (hα : 0 < α) (hα1 : α ≤ 1) :
    α ^ 2 ≤ Work.FTS.NonlinRows.Rl1.Env α f := by
  have hX : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
  have h3 : (0 : ℝ) ≤ Real.sqrt α * Work.FTS.Nonlin.Xn α f :=
    mul_nonneg (Real.sqrt_nonneg α) hX
  have h4 : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α f) ^ 2 :=
    mul_nonneg (Real.rpow_nonneg hα.le _) (sq_nonneg _)
  rw [Work.FTS.NonlinRows.Rl1.Env]
  linarith

end Work.FTS_MuLamOK.Rows
