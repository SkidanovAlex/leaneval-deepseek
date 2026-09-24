import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Submission.Commons.Analysis.ExpLog.log_le_rpow_eventually

open Filter
open scoped Topology

namespace Commons.Analysis.Asymptotics

/-! If a function `F : ℕ → ℕ` is eventually bounded below by a positive constant
times `x / (log x)²`, then `F` is unbounded above.

The proof reduces to showing that `x ↦ x / (log x)²` tends to `+∞` at `+∞`
(along the natural numbers).  To keep the argument elementary we compare, for
large `x`, `x ^ (1/2)` with `x / (log x)²`, using the standard bound
`log x ≤ x ^ (1/4)` which holds eventually. -/

/-- For `X ≥ 2` with `log X ≤ X ^ (1/4)`, one has `X ^ (1/2) ≤ X / (log X)²`. -/
private lemma rpow_half_le_div_log_sq_of_log_le_rpow_quarter {X : ℝ}
    (hX2 : 2 ≤ X) (hlog : Real.log X ≤ X ^ (1 / 4 : ℝ)) :
    X ^ (1 / 2 : ℝ) ≤ X / (Real.log X) ^ 2 := by
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hXpos : 0 < X := by linarith
  have hlog0 : 0 ≤ Real.log X := Real.log_nonneg hX1
  have hlogpos : 0 < Real.log X := Real.log_pos (by linarith : (1 : ℝ) < X)
  have hsqpos : 0 < (Real.log X) ^ 2 := sq_pos_of_pos hlogpos
  have hlogsq_le : (Real.log X) ^ 2 ≤ X ^ (1 / 2 : ℝ) := by
    have h1 : (Real.log X) ^ 2 ≤ (X ^ (1 / 4 : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hlog0 hlog 2
    have h2 : (X ^ (1 / 4 : ℝ)) ^ 2 = X ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hXpos.le]
      congr 1
      norm_num
    exact h1.trans_eq h2
  rw [le_div_iff₀ hsqpos]
  calc
    X ^ (1 / 2 : ℝ) * (Real.log X) ^ 2 ≤ X ^ (1 / 2 : ℝ) * X ^ (1 / 2 : ℝ) := by
      exact mul_le_mul_of_nonneg_left hlogsq_le (Real.rpow_nonneg hXpos.le (1 / 2 : ℝ))
    _ = X := by
      rw [← Real.rpow_add hXpos (1 / 2 : ℝ) (1 / 2 : ℝ)]
      norm_num

/-- Eventually in `x : ℕ`, one has `x ^ (1/2) ≤ x / (log x)²`. -/
private lemma rpow_half_le_div_log_sq_nat_eventually :
    ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ (1 / 2 : ℝ) ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ 2 := by
  obtain ⟨R, hR1, hR⟩ :=
    Commons.Analysis.ExpLog.log_le_rpow_eventually (c := (1 / 4 : ℝ)) (by norm_num)
  obtain ⟨N, hN⟩ := exists_nat_ge (max R 2)
  rw [Filter.eventually_atTop]
  refine ⟨N, ?_⟩
  intro x hx
  let X : ℝ := (x : ℝ)
  have hXN : (N : ℝ) ≤ X := by
    dsimp [X]
    exact_mod_cast hx
  have hXR : R ≤ X := by
    exact le_trans (le_trans (le_max_left R 2) hN) hXN
  have hX2 : 2 ≤ X := by
    exact le_trans (le_trans (le_max_right R 2) hN) hXN
  exact rpow_half_le_div_log_sq_of_log_le_rpow_quarter (X := X) hX2 (hR X hXR)

/-- `x ↦ x ^ (1/2)` tends to `+∞` as the natural `x` grows. -/
private lemma rpow_half_nat_tendsto_atTop :
    Tendsto (fun x : ℕ => (x : ℝ) ^ (1 / 2 : ℝ)) atTop atTop := by
  exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))

/-- `x ↦ x / (log x)²` tends to `+∞` as the natural `x` grows. -/
private lemma tendsto_div_log_sq_nat_atTop :
    Tendsto (fun x : ℕ => (x : ℝ) / (Real.log (x : ℝ)) ^ 2) atTop atTop := by
  refine Filter.tendsto_atTop_mono' atTop ?_ rpow_half_nat_tendsto_atTop
  exact rpow_half_le_div_log_sq_nat_eventually

/-- For `c > 0`, `x ↦ c * x / (log x)²` tends to `+∞` as the natural `x` grows. -/
private lemma tendsto_mul_div_log_sq_nat_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℕ => c * (x : ℝ) / (Real.log (x : ℝ)) ^ 2) atTop atTop := by
  have h := (tendsto_div_log_sq_nat_atTop).const_mul_atTop hc
  convert h using 1
  ext x
  ring

theorem unbounded_of_eventually_ge_mul_div_log_sq {F : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (hF : ∀ᶠ x : ℕ in atTop, c * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 ≤ (F x : ℝ)) :
    ∀ B : ℕ, ∃ x : ℕ, B < F x := by
  intro B
  have hgt : ∀ᶠ x : ℕ in atTop, (B : ℝ) < c * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 :=
    (tendsto_mul_div_log_sq_nat_atTop hc).eventually_gt_atTop (B : ℝ)
  have hB : ∀ᶠ x : ℕ in atTop, (B : ℝ) < (F x : ℝ) := by
    filter_upwards [hF, hgt] with x hxF hxgt
    exact lt_of_lt_of_le hxgt hxF
  rw [Filter.eventually_atTop] at hB
  obtain ⟨N, hN⟩ := hB
  refine ⟨N, ?_⟩
  exact_mod_cast hN N (le_rfl)

end Commons.Analysis.Asymptotics