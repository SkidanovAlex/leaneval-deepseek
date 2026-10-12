import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.BoseFixB3.Steps
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixB3/Eps/Arith` — the parameter arithmetic of `B3EpsRoot`

FS's dilute regime (ll. 1531–1545 of `Papers/fournais_solovej/final_v2.tex`) has

  `κ := (d²ℓ)⁻¹`,  `ℓ = K_ℓ(μa)^{-1/2}`,  `d = (μa³)^{6/323}`,  `M = 48`,

so that `κℓ = d⁻² ≥ 1`, `d ≤ 1`, and `(κℓ)^{-49} = d^{98} ≤ d^{94} = d^{2(M-1)}`.
These are the only arithmetic facts the `ε₂`-estimate needs; they are collected here.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixB3.Eps

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseKinLoc
open Work.BoseBoxFix

set_option autoImplicit false

/-- `κℓ = d⁻²`: the two abbreviations `kapAt = (d²ℓ)⁻¹` and `ellAt = ℓ`. -/
lemma kapAt_mul_ellAt (μ a : ℝ) (hℓ : ellAt μ a ≠ 0) :
    kapAt μ a * ellAt μ a = ((patAt μ a).d ^ 2)⁻¹ := by
  have h : sideAt μ a ≠ 0 := by simpa [ellAt] using hℓ
  rw [kapAt, ellAt]
  field_simp
  simp only [patAt]

/-- `d = (μa³)^{6/323} > 0` in the dilute regime. -/
lemma patAt_d_pos {μ a : ℝ} (h : 0 < μ * a ^ 3) : 0 < (patAt μ a).d := by
  rw [patAt_d]
  exact fsXp_pos h

/-- `d ≤ 1` for diluteness `μa³ ≤ 1`. -/
lemma patAt_d_le_one {μ a : ℝ} (h0 : 0 < μ * a ^ 3) (h1 : μ * a ^ 3 ≤ 1) :
    (patAt μ a).d ≤ 1 := by
  rw [patAt_d]
  exact fsXp_le_one h0 h1 (by norm_num)

/-- `d⁻² ≥ 1` in the dilute regime. -/
lemma patAt_d_inv_sq_ge_one {μ a : ℝ} (h0 : 0 < μ * a ^ 3) (h1 : μ * a ^ 3 ≤ 1) :
    1 ≤ ((patAt μ a).d ^ 2)⁻¹ := by
  have hd := patAt_d_pos h0
  have hd1 := patAt_d_le_one h0 h1
  have h2 : (patAt μ a).d ^ 2 ≤ 1 := by
    calc (patAt μ a).d ^ 2 = (patAt μ a).d * (patAt μ a).d := by ring
      _ ≤ 1 * 1 := mul_le_mul hd1 hd1 hd.le zero_le_one
      _ = 1 := by norm_num
  have hpos : 0 < (patAt μ a).d ^ 2 := by positivity
  exact (one_le_inv₀ hpos).mpr h2

/-- `κℓ ≥ 1` in the dilute regime (`κℓ = d⁻²`). -/
lemma kapAt_mul_ellAt_ge_one {μ a : ℝ} (h0 : 0 < μ * a ^ 3) (h1 : μ * a ^ 3 ≤ 1)
    (hℓ : ellAt μ a ≠ 0) : 1 ≤ kapAt μ a * ellAt μ a := by
  rw [kapAt_mul_ellAt μ a hℓ]
  exact patAt_d_inv_sq_ge_one h0 h1

/-- `((patAt μ a).d ^ 2)⁻¹ = (patAt μ a).d ^ (-(2 : ℤ))`. -/
lemma patAt_d_inv_sq_eq_zpow (μ a : ℝ) :
    ((patAt μ a).d ^ 2)⁻¹ = (patAt μ a).d ^ (-(2 : ℤ)) := by
  simp only [zpow_neg, zpow_natCast]
  rfl

/-- `(κℓ)^{-49} = d^{98}`. -/
lemma kapAt_ellAt_zpow_neg49 {μ a : ℝ} (hℓ : ellAt μ a ≠ 0) :
    (kapAt μ a * ellAt μ a) ^ (-(49 : ℤ)) = (patAt μ a).d ^ (98 : ℕ) := by
  rw [kapAt_mul_ellAt μ a hℓ, patAt_d_inv_sq_eq_zpow, ← zpow_mul]
  norm_num

/-- **The numerical comparison**: `(κℓ)^{-49} ≤ d^{2(M-1)}` (`= d^{94}`), since `κℓ = d⁻² ≥ 1`
and `d ≤ 1` in the dilute regime.  The exponent `49` is far above FS's requirement
`M - 1 = 47`. -/
lemma kapAt_ellAt_zpow_le_d (μ a : ℝ) (h0 : 0 < μ * a ^ 3) (h1 : μ * a ^ 3 ≤ 1)
    (hℓ : ellAt μ a ≠ 0) :
    (kapAt μ a * ellAt μ a) ^ (-(49 : ℤ))
      ≤ (patAt μ a).d ^ (2 * ((patAt μ a).M - 1)) := by
  rw [kapAt_ellAt_zpow_neg49 hℓ, patAt_M]
  have hd0 : (0 : ℝ) ≤ (patAt μ a).d := (patAt_d_pos h0).le
  have hd1 : (patAt μ a).d ≤ 1 := patAt_d_le_one h0 h1
  have hexp : 2 * (mValue - 1) = 94 := by norm_num [mValue]
  rw [hexp]
  exact pow_le_pow_of_le_one hd0 hd1 (by norm_num)

/-- `ellAt μ (a v) > 0` in the dilute regime. -/
lemma ellAt_pos (μ : ℝ) (a : ℝ) (hμ : 0 < μ) (ha : 0 < a) : 0 < ellAt μ a := by
  have hKl : 0 < (paramsAt μ a).Kl := by
    change 0 < (patAt μ a).Kl
    rw [patAt_Kl]
    exact fsXp_pos (by positivity)
  have := boxSide_pos (P := paramsAt μ a) (μ := μ) (a := a) hμ ha hKl
  simpa [ellAt, patAt, sideAt] using this

/-- `kappa` is positive. -/
lemma kapAt_pos {μ a : ℝ} (h0 : 0 < μ * a ^ 3) (hℓ : 0 < ellAt μ a) : 0 < kapAt μ a := by
  have hd := patAt_d_pos h0
  have hside : 0 < sideAt μ a := by simpa [ellAt] using hℓ
  rw [kapAt]
  exact inv_pos.mpr (mul_pos (pow_pos hd 2) hside)

end Work.BoseFixB3.Eps
