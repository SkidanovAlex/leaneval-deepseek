import Mathlib
import Submission.Work.TMC16Core.Defs

namespace Work.TMC16Core.Basic

/-- The quasi-periodic potential is shifted by `y` in the site index when the phase `θ`
is shifted by `y * α`. -/
theorem amoPot_translate (α lam θ : ℝ) (y n : ℤ) :
    Work.TMC16Core.amoPot α lam (θ + (y : ℝ) * α) n = Work.TMC16Core.amoPot α lam θ (n + y) := by
  have h : (θ + (y : ℝ) * α) + (n : ℝ) * α = θ + ((n + y : ℤ) : ℝ) * α := by
    push_cast; ring
  unfold Work.TMC16Core.amoPot
  rw [h]

/-- The action of the Anderson operator with phase `θ + y * α` on the `y`-translate of `u`
equals the action with phase `θ` on `u`, translated back by `y`. -/
theorem amoAct_translate (α lam θ : ℝ) (u : ℤ → ℂ) (y : ℤ) :
    Work.TMC16Core.amoAct α lam (θ + (y : ℝ) * α) (fun n => u (n + y))
      = fun n => Work.TMC16Core.amoAct α lam θ u (n + y) := by
  funext n
  simp only [Work.TMC16Core.amoAct]
  rw [amoPot_translate (α := α) (lam := lam) (θ := θ) (y := y) (n := n)]
  have e1 : (n + 1) + y = (n + y) + 1 := by ring
  have e2 : (n - 1) + y = (n + y) - 1 := by ring
  rw [e1, e2]

theorem genEigen_translate {α lam θ E : ℝ} {u : ℤ → ℂ} (y : ℤ)
    (hu : Work.TMC16Core.IsGenEigen α lam θ E u) :
    Work.TMC16Core.IsGenEigen α lam (θ + (y : ℝ) * α) E (fun n => u (n + y)) := by
  obtain ⟨hu0, hueq, C, hC⟩ := hu
  refine ⟨?_, ?_, C * (1 + |(y : ℝ)|), ?_⟩
  · intro hf
    apply hu0
    ext n
    have := congrFun hf (n - y)
    simpa [sub_add_cancel] using this
  · intro n
    rw [amoAct_translate]
    exact hueq (n + y)
  · intro n
    have hC0 : 0 ≤ C := by
      have h := hC 0
      have h2 : (0 : ℝ) ≤ ‖u 0‖ := norm_nonneg _
      simp only [Int.cast_zero, abs_zero, add_zero] at h
      linarith
    have hn : ‖u (n + y)‖ ≤ C * (1 + |((n + y : ℤ) : ℝ)|) := hC (n + y)
    have hbound : 1 + |((n + y : ℤ) : ℝ)| ≤ (1 + |(y : ℝ)|) * (1 + |(n : ℝ)|) := by
      push_cast
      have ha : |(n : ℝ) + (y : ℝ)| ≤ |(n : ℝ)| + |(y : ℝ)| := abs_add_le _ _
      nlinarith [abs_nonneg ((n : ℝ)), abs_nonneg ((y : ℝ)), ha]
    calc ‖u (n + y)‖ ≤ C * (1 + |((n + y : ℤ) : ℝ)|) := hn
      _ ≤ C * ((1 + |(y : ℝ)|) * (1 + |(n : ℝ)|)) := mul_le_mul_of_nonneg_left hbound hC0
      _ = C * (1 + |(y : ℝ)|) * (1 + |(n : ℝ)|) := by ring

end Work.TMC16Core.Basic
