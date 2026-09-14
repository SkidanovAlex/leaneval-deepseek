import Mathlib.Algebra.Ring.IsFormallyReal
import Submission.Commons.NumberTheory.Height.NumberField.infinitePlace_val_le_mulHeight
import Submission.Commons.NumberTheory.Height.NumberField.mulHeight_sum_mul_int_le_of_nonempty

namespace Commons.NumberTheory.Height.NumberField

open _root_.NumberField

set_option linter.unusedVariables false

theorem log_abv_form_value_upper {K : Type*} [Field K] [NumberField K]
    {σ : Type*} [Fintype σ] (a : σ → K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w : NumberField.InfinitePlace K) (x : σ → ℤ) (hx : x ≠ 0),
      Real.log (w.val (∑ j : σ, a j * (x j : K))) ≤ C + C * Real.log ‖x‖ := by
  classical
  rcases isEmpty_or_nonempty σ with hσ | hσ
  · refine ⟨1, one_pos, ?_⟩
    intro w x hx
    exact absurd (funext fun j => (hσ.false j).elim) hx
  · have : Nonempty σ := hσ
    set M : ℝ := (Fintype.card σ : ℝ) ^ (Module.finrank ℚ K) *
      ∏ j : σ, Height.mulHeight₁ (a j) with hMdef
    set e : ℕ := Module.finrank ℚ K * Fintype.card σ with hedef
    set C : ℝ := max 1 (max (Real.log M) (e : ℝ)) with hCdef
    have hCpos : 0 < C := lt_of_lt_of_le one_pos (le_max_left _ _)
    have hlogM : Real.log M ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
    have heC : (e : ℝ) ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
    refine ⟨C, hCpos, ?_⟩
    intro w x hx
    -- `x ≠ 0` implies `1 ≤ ‖x‖`
    have hx1 : 1 ≤ ‖x‖ := by
      obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
        by_contra h
        push Not at h
        exact hx (funext fun j => h j)
      have h1 : (1 : ℝ) ≤ ‖x j‖ := by
        rw [Int.norm_eq_abs]
        exact_mod_cast Int.one_le_abs hj
      exact h1.trans (norm_le_pi_norm x j)
    have hxlog : 0 ≤ Real.log ‖x‖ := Real.log_nonneg hx1
    have hxpos : 0 < ‖x‖ := lt_of_lt_of_le zero_lt_one hx1
    -- the value at `w` is bounded by a constant times `‖x‖ ^ e`
    have hval : w.val (∑ j : σ, a j * (x j : K)) ≤ M * ‖x‖ ^ e := by
      calc w.val (∑ j : σ, a j * (x j : K))
          ≤ Height.mulHeight₁ (∑ j : σ, a j * (x j : K)) :=
            infinitePlace_val_le_mulHeight w _
        _ ≤ M * (max 1 ‖x‖) ^ e := by
            rw [hMdef, hedef]
            exact mulHeight_sum_mul_int_le_of_nonempty a x
        _ = M * ‖x‖ ^ e := by rw [max_eq_right hx1]
    have hMpos : 0 < M := by
      rw [hMdef]
      refine mul_pos (pow_pos ?_ _) ?_
      · exact_mod_cast Fintype.card_pos
      · exact Finset.prod_pos fun j _ =>
          lt_of_lt_of_le zero_lt_one (Height.one_le_mulHeight₁ (a j))
    by_cases hu0 : w.val (∑ j : σ, a j * (x j : K)) = 0
    · rw [hu0, Real.log_zero]
      have : 0 ≤ C * Real.log ‖x‖ := mul_nonneg hCpos.le hxlog
      linarith
    · have hu_pos : 0 < w.val (∑ j : σ, a j * (x j : K)) :=
        lt_of_le_of_ne (w.val.nonneg _) (Ne.symm hu0)
      have hlog : Real.log (w.val (∑ j : σ, a j * (x j : K))) ≤
          Real.log M + (e : ℝ) * Real.log ‖x‖ := by
        have h1 : Real.log (w.val (∑ j : σ, a j * (x j : K))) ≤
            Real.log (M * ‖x‖ ^ e) := Real.log_le_log hu_pos hval
        rwa [Real.log_mul hMpos.ne' (pow_ne_zero _ hxpos.ne'), Real.log_pow] at h1
      have hmul : (e : ℝ) * Real.log ‖x‖ ≤ C * Real.log ‖x‖ :=
        mul_le_mul_of_nonneg_right heC hxlog
      linarith

end Commons.NumberTheory.Height.NumberField