import Mathlib

set_option linter.unusedVariables false

namespace Work.KMTAreas.A7

open MeasureTheory

/-- The second iterated derivative of a compactly supported function has compact support. -/
lemma hasCompactSupport_iteratedDeriv_two {g : ℝ → ℂ} (hg : HasCompactSupport g) :
    HasCompactSupport (iteratedDeriv 2 g) := by
  have h2 : HasCompactSupport (deriv (deriv g)) := hg.deriv.deriv
  have heq : iteratedDeriv 2 g = deriv (deriv g) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rwa [heq]

/-- The second iterated derivative of a `C²` compactly supported function is integrable. -/
lemma integrable_iteratedDeriv_two {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g)
    (hc : HasCompactSupport g) : Integrable (fun y => iteratedDeriv 2 g y) :=
  (hg.continuous_iteratedDeriv' 2).integrable_of_hasCompactSupport
    (hasCompactSupport_iteratedDeriv_two hc)

theorem integral_norm_sum_bumps_le (Ai : Finset ℕ) (c : ℕ → ℂ) (φ : ℕ → ℝ → ℂ) (S : ℝ)
    (hS : 0 ≤ S) (hc : ∀ m, ‖c m‖ ≤ 2)
    (hφ : ∀ m ∈ Ai, ContDiff ℝ 2 (φ m) ∧ HasCompactSupport (φ m) ∧
      (∫ y, ‖φ m y‖) ≤ S ∧ (∫ y, ‖iteratedDeriv 2 (φ m) y‖) ≤ S) :
    (∫ y, ‖∑ m ∈ Ai, c m * φ m y‖) ≤ 2 * S * (Ai.card : ℝ) ∧
      (∫ y, ‖iteratedDeriv 2 (fun y => ∑ m ∈ Ai, c m * φ m y) y‖) ≤ 2 * S * (Ai.card : ℝ) := by
  have hφ_int : ∀ m ∈ Ai, Integrable (φ m) := fun m hm =>
    ((hφ m hm).1.continuous).integrable_of_hasCompactSupport (hφ m hm).2.1
  have hd_int : ∀ m ∈ Ai, Integrable (fun y => iteratedDeriv 2 (φ m) y) := fun m hm =>
    integrable_iteratedDeriv_two (hφ m hm).1 (hφ m hm).2.1
  constructor
  · -- first bound: the sum of the bumps
    have hF : Integrable (fun y => ∑ m ∈ Ai, c m * φ m y) :=
      integrable_finsetSum _ (fun m hm => (hφ_int m hm).const_mul (c m))
    have hRHS : Integrable (fun y => ∑ m ∈ Ai, 2 * ‖φ m y‖) :=
      integrable_finsetSum _ (fun m hm => (hφ_int m hm).norm.const_mul 2)
    have hpoint : ∀ y, ‖∑ m ∈ Ai, c m * φ m y‖ ≤ ∑ m ∈ Ai, 2 * ‖φ m y‖ := by
      intro y
      calc ‖∑ m ∈ Ai, c m * φ m y‖
          ≤ ∑ m ∈ Ai, ‖c m * φ m y‖ := norm_sum_le _ _
        _ ≤ ∑ m ∈ Ai, 2 * ‖φ m y‖ := by
            apply Finset.sum_le_sum
            intro m hm
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_right (hc m) (norm_nonneg _)
    calc ∫ y, ‖∑ m ∈ Ai, c m * φ m y‖
        ≤ ∫ y, ∑ m ∈ Ai, 2 * ‖φ m y‖ := integral_mono hF.norm hRHS hpoint
      _ = ∑ m ∈ Ai, ∫ y, 2 * ‖φ m y‖ :=
            integral_finsetSum Ai (fun m hm => (hφ_int m hm).norm.const_mul 2)
      _ = ∑ m ∈ Ai, 2 * ∫ y, ‖φ m y‖ := by
            apply Finset.sum_congr rfl
            intro m hm
            rw [integral_const_mul]
      _ ≤ ∑ m ∈ Ai, 2 * S := by
            apply Finset.sum_le_sum
            intro m hm
            exact mul_le_mul_of_nonneg_left (hφ m hm).2.2.1 (by norm_num)
      _ = 2 * S * (Ai.card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            ring
  · -- second bound: the sum of the second derivatives
    have hderiv_eq : ∀ y, iteratedDeriv 2 (fun y => ∑ m ∈ Ai, c m * φ m y) y
        = ∑ m ∈ Ai, c m * iteratedDeriv 2 (φ m) y := by
      intro y
      rw [iteratedDeriv_fun_sum]
      · apply Finset.sum_congr rfl
        intro m hm
        rw [iteratedDeriv_const_mul_field]
      · intro m hm
        exact (hφ m hm).1.contDiffAt.const_smul (c m)
    have hL : Integrable (fun y => iteratedDeriv 2 (fun y => ∑ m ∈ Ai, c m * φ m y) y) := by
      have heq : (fun y => iteratedDeriv 2 (fun y => ∑ m ∈ Ai, c m * φ m y) y)
          = fun y => ∑ m ∈ Ai, c m * iteratedDeriv 2 (φ m) y := funext hderiv_eq
      rw [heq]
      exact integrable_finsetSum _ (fun m hm => (hd_int m hm).const_mul (c m))
    have hR : Integrable (fun y => ∑ m ∈ Ai, 2 * ‖iteratedDeriv 2 (φ m) y‖) :=
      integrable_finsetSum _ (fun m hm => (hd_int m hm).norm.const_mul 2)
    have hpoint : ∀ y,
        ‖iteratedDeriv 2 (fun y => ∑ m ∈ Ai, c m * φ m y) y‖
          ≤ ∑ m ∈ Ai, 2 * ‖iteratedDeriv 2 (φ m) y‖ := by
      intro y
      rw [hderiv_eq y]
      calc ‖∑ m ∈ Ai, c m * iteratedDeriv 2 (φ m) y‖
          ≤ ∑ m ∈ Ai, ‖c m * iteratedDeriv 2 (φ m) y‖ := norm_sum_le _ _
        _ ≤ ∑ m ∈ Ai, 2 * ‖iteratedDeriv 2 (φ m) y‖ := by
            apply Finset.sum_le_sum
            intro m hm
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_right (hc m) (norm_nonneg _)
    calc ∫ y, ‖iteratedDeriv 2 (fun y => ∑ m ∈ Ai, c m * φ m y) y‖
        ≤ ∫ y, ∑ m ∈ Ai, 2 * ‖iteratedDeriv 2 (φ m) y‖ := integral_mono hL.norm hR hpoint
      _ = ∑ m ∈ Ai, ∫ y, 2 * ‖iteratedDeriv 2 (φ m) y‖ :=
            integral_finsetSum Ai (fun m hm => (hd_int m hm).norm.const_mul 2)
      _ = ∑ m ∈ Ai, 2 * ∫ y, ‖iteratedDeriv 2 (φ m) y‖ := by
            apply Finset.sum_congr rfl
            intro m hm
            rw [integral_const_mul]
      _ ≤ ∑ m ∈ Ai, 2 * S := by
            apply Finset.sum_le_sum
            intro m hm
            exact mul_le_mul_of_nonneg_left (hφ m hm).2.2.2 (by norm_num)
      _ = 2 * S * (Ai.card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            ring

end Work.KMTAreas.A7
