import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `6/7`-shaped Perron parameters for the twisted prime number theorem

`Work.BMF.logDeriv_LFunction_VK` (V4, amended exponent `6/7`) supplies, at the trivial
character mod `1`, the zero-free region and logarithmic-derivative bound for `ζ` in the shape

`1 - c / ((log (|t|+3))^{6/7} (log 3 + log log (|t|+3))) ≤ σ  ⟹  ζ(σ + it) ≠ 0`

This file fixes the parameter package of the twisted truncated Perron argument for that shape:
the height `T = |u| + L^2 exp(L^{1/10}) + 7`, the denominator `D = ztD (2T)` dominating the
region on the whole rectangle, the distance `δ = κ/(4D)` of the left abscissa from `1` and the
left abscissa `σ₁ = 1 - δ` itself.
-/

namespace Work.BMF

open Filter
open scoped Real Topology

noncomputable section

/-- `(log (h+3))^{6/7} · (log 3 + log log (h+3))`, the denominator of the `6/7`-shaped
Vinogradov–Korobov zero-free region at height `h`. -/
def ztD (h : ℝ) : ℝ :=
  (Real.log (h + 3)) ^ (6 / 7 : ℝ) * (Real.log 3 + Real.log (Real.log (h + 3)))

lemma one_le_log_three : (1 : ℝ) ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  exact Real.exp_one_lt_three.le

lemma lt_one_log_seven : (1 : ℝ) < Real.log 7 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  linarith [Real.exp_one_lt_three]

lemma ztD_pos {h : ℝ} (hh : 4 ≤ h) : 0 < ztD h := by
  have h7 : (7 : ℝ) ≤ h + 3 := by linarith
  have h1 : (1 : ℝ) < Real.log (h + 3) :=
    lt_of_lt_of_le lt_one_log_seven (Real.log_le_log (by norm_num) h7)
  have h2 : 0 < Real.log (Real.log (h + 3)) := Real.log_pos h1
  refine mul_pos (Real.rpow_pos_of_pos (by linarith) _) ?_
  linarith [one_le_log_three]

/-- If `log (h+3) ≤ A` with `A ≥ 1`, then `ztD h ≤ A^{6/7} (log 3 + log A)`. -/
lemma ztD_le_of_log_le {h A : ℝ} (h4 : 4 ≤ h) (hA : 1 ≤ A) (h2 : Real.log (h + 3) ≤ A) :
    ztD h ≤ A ^ (6 / 7 : ℝ) * (Real.log 3 + Real.log A) := by
  have h7 : (7 : ℝ) ≤ h + 3 := by linarith
  have hlog1 : (1 : ℝ) < Real.log (h + 3) :=
    lt_of_lt_of_le lt_one_log_seven (Real.log_le_log (by norm_num) h7)
  have hlog0 : 0 ≤ Real.log (h + 3) := le_of_lt (lt_trans zero_lt_one hlog1)
  have hp : (Real.log (h + 3)) ^ (6 / 7 : ℝ) ≤ A ^ (6 / 7 : ℝ) :=
    Real.rpow_le_rpow hlog0 h2 (by norm_num)
  have hloglog : Real.log (Real.log (h + 3)) ≤ Real.log A :=
    Real.log_le_log (by linarith) h2
  have hnn : 0 ≤ Real.log (Real.log (h + 3)) := Real.log_nonneg (le_of_lt hlog1)
  refine mul_le_mul hp (by linarith) ?_ (Real.rpow_nonneg (le_trans zero_le_one hA) _)
  linarith [one_le_log_three]

/-- The Perron height used for the twisted prime number theorem:
`T = |u| + L ^ 2 exp (L^{1/10}) + 7` with `L` the logarithm of the evaluation point. -/
def twT (L u : ℝ) : ℝ := |u| + L ^ 2 * Real.exp (L ^ (1 / 10 : ℝ)) + 7

/-- The `6/7`-shaped zero-free-region denominator at height `2 T`, which dominates the whole
twisted Perron rectangle. -/
def twD (L u : ℝ) : ℝ := ztD (2 * twT L u)

/-- `δ = κ / (4 D)`, the distance of the left abscissa from `1`. -/
def twδ (κ L u : ℝ) : ℝ := κ / (4 * twD L u)

/-- The left abscissa `σ₁ = 1 - δ` of the twisted Perron rectangle. -/
def twσ (κ L u : ℝ) : ℝ := 1 - twδ κ L u

lemma seven_le_twT (L u : ℝ) : 7 ≤ twT L u := by
  rw [twT]
  have h := abs_nonneg u
  have h2 : 0 ≤ L ^ 2 * Real.exp (L ^ (1 / 10 : ℝ)) := by positivity
  linarith

lemma abs_lt_twT (L u : ℝ) : |u| < twT L u := by
  rw [twT]
  have h := abs_nonneg u
  have h2 : 0 ≤ L ^ 2 * Real.exp (L ^ (1 / 10 : ℝ)) := by positivity
  linarith

lemma twT_pos (L u : ℝ) : 0 < twT L u := by
  have := seven_le_twT L u; linarith

lemma two_le_twT (L u : ℝ) : 2 ≤ twT L u := by
  have := seven_le_twT L u; linarith

lemma le_twT (L u : ℝ) : L ^ 2 * Real.exp (L ^ (1 / 10 : ℝ)) ≤ twT L u := by
  rw [twT]
  have h := abs_nonneg u
  linarith

lemma twD_pos (L u : ℝ) : 0 < twD L u := by
  rw [twD]
  exact ztD_pos (by have := seven_le_twT L u; linarith)

lemma twδ_pos {κ L u : ℝ} (hκ : 0 < κ) : 0 < twδ κ L u := by
  rw [twδ]
  exact div_pos hκ (by have := twD_pos L u; linarith)

end

end Work.BMF
