import Mathlib
import Submission.Work.BMF.tuple_setup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open MeasureTheory

/-- The rescaled triangular weight `n4Wr C₀ ξ = 12 * C₀ * max (1 - 4 * C₀ * |ξ|) 0` is continuous
and compactly supported (its support lies in `[-1/(4C₀), 1/(4C₀)]`), hence Lebesgue-integrable. -/
lemma n4Wr_integrable {C₀ : ℝ} (hC₀ : 0 < C₀) :
    MeasureTheory.Integrable (fun ξ : ℝ => n4Wr C₀ ξ) := by
  have hcont : Continuous fun ξ : ℝ => n4Wr C₀ ξ := by
    unfold n4Wr
    fun_prop
  refine hcont.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (K := Set.Icc (-(1 / (4 * C₀))) (1 / (4 * C₀))) isCompact_Icc ?_
  intro ξ hξ
  simp only [n4Wr]
  have h1 : 1 / (4 * C₀) < |ξ| := by
    by_contra h
    push Not at h
    exact hξ (by
      rw [Set.mem_Icc]
      exact ⟨by linarith [neg_abs_le ξ], by linarith [le_abs_self ξ]⟩)
  have h2 : 1 - 4 * C₀ * |ξ| < 0 := by
    have hpos : (0 : ℝ) < 4 * C₀ := by linarith
    have : 4 * C₀ * (1 / (4 * C₀)) < 4 * C₀ * |ξ| := mul_lt_mul_of_pos_left h1 hpos
    rw [mul_one_div, div_self (ne_of_gt hpos)] at this
    linarith
  rw [max_eq_right h2.le, mul_zero]

end Work.BMF
