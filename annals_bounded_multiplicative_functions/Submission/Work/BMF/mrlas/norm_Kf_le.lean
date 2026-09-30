import Mathlib
import Submission.Work.BMF.halasz_defs
import Submission.Work.BMF.halasz_abel

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mrlas

open Finset

/-- Trivial bound for the weighted sum `Kf f t = Σ_{n ≤ t} f n log n`:
if `‖f n‖ ≤ 1` for all `n` and `t ≥ 1` then `‖Kf f t‖ ≤ t log t`. -/
theorem norm_Kf_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) {t : ℝ} (ht : 1 ≤ t) :
    ‖Work.BMF.Kf f t‖ ≤ t * Real.log t := by
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  set N : ℕ := ⌊t⌋₊ with hN
  have hNle : (N : ℝ) ≤ t := Nat.floor_le ht0.le
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast ht)
  have hNpos : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hNpos
  unfold Work.BMF.Kf
  calc ‖∑ n ∈ Finset.Icc 1 N, f n * (Real.log n : ℂ)‖
      ≤ ∑ n ∈ Finset.Icc 1 N, ‖f n * (Real.log n : ℂ)‖ := norm_sum_le _ _
    _ = ∑ n ∈ Finset.Icc 1 N, ‖f n‖ * Real.log n := by
        refine Finset.sum_congr rfl ?_
        intro n hn
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
        have h1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        exact Real.log_nonneg (by exact_mod_cast h1)
    _ ≤ ∑ n ∈ Finset.Icc 1 N, Real.log N := by
        refine Finset.sum_le_sum ?_
        intro n hn
        have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
        have h1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        have hln : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast h1)
        have hlog : Real.log n ≤ Real.log N :=
          Real.log_le_log (by exact_mod_cast (show 0 < n by omega)) (by exact_mod_cast hnN)
        calc ‖f n‖ * Real.log n ≤ 1 * Real.log n :=
              mul_le_mul_of_nonneg_right (hf n) hln
          _ ≤ Real.log N := by rw [one_mul]; exact hlog
    _ = (N : ℝ) * Real.log N := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        simp
    _ ≤ t * Real.log t := by
        have hlog : Real.log N ≤ Real.log t :=
          Real.log_le_log (lt_of_lt_of_le one_pos hNpos) hNle
        exact mul_le_mul hNle hlog hlogN ht0.le

end Work.BMF.mrlas
