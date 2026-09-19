import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Submission.Commons.Analysis.Calculus.exists_contDiff_partition_unity

namespace Commons.Analysis.Calculus

theorem exists_contDiff_step (a b : ℝ) (hab : a < b) :
    ∃ Ψ : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) Ψ ∧ (∀ x, x ≤ a → Ψ x = 0) ∧
      (∀ x, b ≤ x → Ψ x = 1) ∧ (∀ x, 0 ≤ Ψ x ∧ Ψ x ≤ 1) := by
  refine ⟨fun x => Real.smoothTransition ((x - a) / (b - a)), ?_, ?_, ?_, ?_⟩
  · -- Smoothness: composition of the smooth transition with an affine map.
    apply ContDiff.comp Real.smoothTransition.contDiff
    exact (contDiff_id.sub contDiff_const).div contDiff_const (fun _ => by linarith)
  · -- Vanishes on (-∞, a].
    intro x hx
    show Real.smoothTransition ((x - a) / (b - a)) = 0
    rw [Real.smoothTransition.zero_of_nonpos]
    apply div_nonpos_of_nonpos_of_nonneg
    · linarith
    · linarith
  · -- Equals one on [b, ∞).
    intro x hx
    show Real.smoothTransition ((x - a) / (b - a)) = 1
    rw [Real.smoothTransition.one_of_one_le]
    rw [le_div_iff₀ (by linarith)]
    linarith
  · -- Bounded in [0, 1].
    intro x
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

end Commons.Analysis.Calculus