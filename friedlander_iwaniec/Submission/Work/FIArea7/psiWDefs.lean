/-
# `Work.FIArea7.psiWDefs` — the Abel weight `w m = P (c₀ m) / log m`

The single definition used by the proof of `Work.FIArea7.primeSumPsi`: the weight against which
the von Mangoldt partial sums `∑_{n ≤ y} Λ(n) λ(c₀ n)` are summed by parts.  For `m ≥ 2` it is
`P (c₀ m)/log m` and it is defined to be `0` for `m ≤ 1` (the value at `m = 1` is irrelevant, since
`Λ 1 = 0`).
-/
import Mathlib

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

noncomputable section

/-- The Abel weight `w m = P (c₀ m) / log m` for `m ≥ 2`, and `0` for `m ≤ 1`. -/
def psiW (P : ℝ → ℝ) (c₀ : ℝ) : ℕ → ℂ :=
  fun m => if 2 ≤ m then ((P (c₀ * (m : ℝ)) / Real.log (m : ℝ) : ℝ) : ℂ) else 0

lemma psiW_of_two_le {P : ℝ → ℝ} {c₀ : ℝ} {m : ℕ} (hm : 2 ≤ m) :
    psiW P c₀ m = ((P (c₀ * (m : ℝ)) / Real.log (m : ℝ) : ℝ) : ℂ) := by
  rw [psiW, if_pos hm]

lemma psiW_of_not_two_le {P : ℝ → ℝ} {c₀ : ℝ} {m : ℕ} (hm : ¬ 2 ≤ m) :
    psiW P c₀ m = 0 := by
  rw [psiW, if_neg hm]

lemma psiW_eq_zero_of_P_eq_zero {P : ℝ → ℝ} {c₀ : ℝ} {m : ℕ} (hm : 2 ≤ m)
    (h : P (c₀ * (m : ℝ)) = 0) : psiW P c₀ m = 0 := by
  rw [psiW_of_two_le hm, h, zero_div, Complex.ofReal_zero]

/-- `log m ≥ log 2 > 0` for `m ≥ 2`. -/
lemma log_natCast_pos_of_two_le {m : ℕ} (hm : 2 ≤ m) : 0 < Real.log (m : ℝ) :=
  Real.log_pos (by exact_mod_cast hm)

lemma log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

/-- The weight is bounded by `1/log 2` on `m ≥ 2` when `|P| ≤ 1`. -/
lemma norm_psiW_le {P : ℝ → ℝ} {c₀ : ℝ} {m : ℕ} (hm : 2 ≤ m) (h1 : ∀ u, |P u| ≤ 1) :
    ‖psiW P c₀ m‖ ≤ 1 / Real.log 2 := by
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlogm : 0 < Real.log (m : ℝ) := log_natCast_pos_of_two_le hm
  have hlog2 : 0 < Real.log 2 := log_two_pos
  have hle : Real.log 2 ≤ Real.log (m : ℝ) := Real.log_le_log (by norm_num) hm2
  rw [psiW_of_two_le hm, Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_of_pos hlogm]
  rw [div_le_div_iff₀ hlogm hlog2]
  nlinarith [h1 (c₀ * (m : ℝ)), hle, hlog2]

end

end Work.FIArea7
