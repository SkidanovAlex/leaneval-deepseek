import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE

theorem CSq_trunc_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (ε : ℝ) (s : ℕ) (c : (ι → ℤ) → ℂ)
    (hc : Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s * ‖c k‖ ^ 2)) :
    Work.Diff.STE.CSq s (Work.Diff.STE.trunc ρ ε c) ≤ Work.Diff.STE.CSq s c := by
  have hpt : ∀ k : ι → ℤ, ‖Work.Diff.STE.trunc ρ ε c k‖ ≤ ‖c k‖ := by
    intro k
    have hρk : ‖ρ (ε • fun i => (k i : ℝ))‖ ≤ 1 := hρ _
    calc ‖Work.Diff.STE.trunc ρ ε c k‖
        = ‖ρ (ε • fun i => (k i : ℝ))‖ * ‖c k‖ := by simp [Work.Diff.STE.trunc]
      _ ≤ 1 * ‖c k‖ := mul_le_mul_of_nonneg_right hρk (norm_nonneg _)
      _ = ‖c k‖ := one_mul _
  have hterm : ∀ k : ι → ℤ,
      (Work.Diff.STE.wt k) ^ s * ‖Work.Diff.STE.trunc ρ ε c k‖ ^ 2
        ≤ (Work.Diff.STE.wt k) ^ s * ‖c k‖ ^ 2 := by
    intro k
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hpt k) 2)
      (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) s)
  have hsum : Summable (fun k : ι → ℤ =>
      (Work.Diff.STE.wt k) ^ s * ‖Work.Diff.STE.trunc ρ ε c k‖ ^ 2) :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) s) (sq_nonneg _))
      hterm hc
  calc Work.Diff.STE.CSq s (Work.Diff.STE.trunc ρ ε c)
      = ∑' k : ι → ℤ, (Work.Diff.STE.wt k) ^ s * ‖Work.Diff.STE.trunc ρ ε c k‖ ^ 2 := rfl
    _ ≤ ∑' k : ι → ℤ, (Work.Diff.STE.wt k) ^ s * ‖c k‖ ^ 2 :=
        Summable.tsum_le_tsum hterm hsum hc
    _ = Work.Diff.STE.CSq s c := rfl

end Work.Diff.STE
