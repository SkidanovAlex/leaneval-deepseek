import ChallengeDeps
import Submission.Commons.Lattice.Summable.summable_exp_neg_mul_norm_sq

open ReverseMinkowski
open scoped Real
set_option autoImplicit false

namespace Submission.RhoBasics

variable {n : ℕ}
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- The Gaussian terms over a lattice are summable whenever s ≠ 0. -/
lemma summable_rho (ℒ : Submodule ℤ ℝⁿ) [DiscreteTopology ℒ] {s : ℝ} (hs : s ≠ 0) :
    Summable (fun y : ℒ => rexp (-Real.pi * ‖y‖ ^ 2 / s ^ 2)) := by
  have hsq : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
  have hsqpos : 0 < s ^ 2 := sq_pos_of_ne_zero hs
  have hc : 0 < Real.pi / s ^ 2 := div_pos Real.pi_pos hsqpos
  have hsb : Summable (fun y : ℒ => Real.exp (-(Real.pi / s ^ 2) * ‖(y : ℝⁿ)‖ ^ 2)) :=
    Commons.Lattice.Summable.summable_exp_neg_mul_norm_sq (E := ℝⁿ) (L := ℒ) (c := Real.pi / s ^ 2) hc
  convert hsb using 1
  funext y
  congr 1
  field_simp [hsq]
  simp

/-- Gaussian mass is monotone increasing in s > 0. -/
lemma rho_mono (ℒ : Submodule ℤ ℝⁿ) [DiscreteTopology ℒ] {s₁ s₂ : ℝ}
    (hs₁ : 0 < s₁) (hss : s₁ ≤ s₂) : ρ s₁ ℒ ≤ ρ s₂ ℒ := by
  unfold ρ
  have hne₂ : s₂ ≠ 0 := ne_of_gt (lt_of_lt_of_le hs₁ hss)
  refine Summable.tsum_le_tsum ?_ (summable_rho ℒ (ne_of_gt hs₁)) (summable_rho ℒ hne₂)
  intro y
  rw [Real.exp_le_exp]
  have hsq₁ : 0 < s₁ ^ 2 := sq_pos_of_ne_zero (ne_of_gt hs₁)
  have hsq₂ : 0 < s₂ ^ 2 := sq_pos_of_ne_zero hne₂
  have h₁ : (s₁ : ℝ) ^ 2 ≤ s₂ ^ 2 := by nlinarith [sq_nonneg s₁, sq_nonneg s₂, hs₁, hss]
  have hx0 : 0 ≤ ‖y‖ ^ 2 := sq_nonneg _
  have hdv : ‖y‖ ^ 2 / s₂ ^ 2 ≤ ‖y‖ ^ 2 / s₁ ^ 2 :=
    div_le_div_of_nonneg_left hx0 hsq₁ h₁
  have hneg : -(Real.pi) ≤ 0 := by linarith [Real.pi_pos]
  calc
    -Real.pi * ‖y‖ ^ 2 / s₁ ^ 2 = -(Real.pi * (‖y‖ ^ 2 / s₁ ^ 2)) := by
      field_simp [hsq₁.ne']
    _ ≤ -(Real.pi * (‖y‖ ^ 2 / s₂ ^ 2)) := by
      have h : Real.pi * (‖y‖ ^ 2 / s₂ ^ 2) ≤ Real.pi * (‖y‖ ^ 2 / s₁ ^ 2) := by
        exact mul_le_mul_of_nonneg_left hdv Real.pi_pos.le
      linarith
    _ = -Real.pi * ‖y‖ ^ 2 / s₂ ^ 2 := by
      field_simp [hsq₂.ne']

/-- Gaussian mass is at least 1 (from the zero term) for s ≠ 0. -/
lemma rho_ge_one (ℒ : Submodule ℤ ℝⁿ) [DiscreteTopology ℒ] {s : ℝ} (hs : s ≠ 0) :
    1 ≤ ρ s ℒ := by
  classical
  unfold ρ
  have hsumn := summable_rho ℒ hs
  rw [Summable.tsum_eq_add_tsum_ite hsumn (0 : ℒ)]
  have h0 : rexp (-Real.pi * ‖(0 : ℒ)‖ ^ 2 / s ^ 2) = 1 := by
    have : ‖(0 : ℒ)‖ = 0 := by simp
    rw [this]
    have : (0 : ℝ) / s ^ 2 = 0 := by simp
    simp [this]
  rw [h0]
  have hrest : 0 ≤ (∑' (n : ℒ), if n = 0 then 0 else
      rexp (-Real.pi * ‖n‖ ^ 2 / s ^ 2)) := by
    refine tsum_nonneg ?_
    intro n
    by_cases hn : n = 0
    · simp [hn]
    · simpa [hn] using (Real.exp_pos _).le
  linarith

/-- Gaussian terms are nonnegative. -/
lemma rho_term_nonneg (ℒ : Submodule ℤ ℝⁿ) {s : ℝ} (y : ℒ) :
    0 ≤ rexp (-Real.pi * ‖y‖ ^ 2 / s ^ 2) := (Real.exp_pos _).le

end Submission.RhoBasics
