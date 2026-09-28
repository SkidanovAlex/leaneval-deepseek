import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MDEstimates.ell44_arith_case2b
import Submission.Work.HP.MDEstimates.ell44_arith_case2c

/-!
# Arithmetic assembly for `ell44` (the `Z⁶Δ³` vs `M⁷⁰/M⁴⁰` minimum)

We prove, for every `Z, Δ, M ≥ 1`,

  `min (Z⁶Δ³) (M⁷⁰(P) + M⁴⁰(Q)) ≤ 1000 · Z^{9/2} Δ² (Z^{3/2} + Δ^{3/2}) · min Δ (M⁵³)`

by splitting on the relative sizes of `Δ` and `M⁵³`, and of `Z³` against
`1000² M^{106} Δ`.  Each of the four regimes is a separate arithmetic fact about
`Real.rpow` monomials.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.HP.MDEstimates

/-- Regime `Δ ≤ M⁵³`: the minimum is controlled by its first argument `Z⁶Δ³`,
which is itself at most the right-hand side (with `Δ` in place of `min Δ (M⁵³)`). -/
theorem ell44_arith_case1 :
    ∀ Z Δ M : ℝ, 1 ≤ Z → 1 ≤ Δ → 1 ≤ M → Δ ≤ M^53 →
      Z^6 * Δ^3 ≤ 1000 * Z ^ ((9:ℝ)/2) * Δ^2 * (Z ^ ((3:ℝ)/2) + Δ ^ ((3:ℝ)/2)) * Δ := by
  intro Z Δ M hZ hΔ hM h1
  have hZ0 : 0 < Z := by linarith
  have hΔ0 : 0 < Δ := by linarith
  have hΔnn : (0:ℝ) ≤ Δ := hΔ0.le
  have e1 : Z ^ ((9:ℝ)/2) * Z ^ ((3:ℝ)/2) = Z^6 := by
    rw [← Real.rpow_add hZ0]
    rw [show (9:ℝ)/2 + 3/2 = ((6:ℕ):ℝ) by norm_num]
    exact Real.rpow_natCast Z 6
  have key : Z ^ ((9:ℝ)/2) * Δ^2 * Z ^ ((3:ℝ)/2) * Δ = Z^6 * Δ^3 := by
    rw [show Z ^ ((9:ℝ)/2) * Δ^2 * Z ^ ((3:ℝ)/2) * Δ
        = (Z ^ ((9:ℝ)/2) * Z ^ ((3:ℝ)/2)) * (Δ^2 * Δ) by ring]
    rw [e1]
    ring
  have mulstep : Z ^ ((9:ℝ)/2) * Δ^2 * Z ^ ((3:ℝ)/2) * Δ
      ≤ Z ^ ((9:ℝ)/2) * Δ^2 * (Z ^ ((3:ℝ)/2) + Δ ^ ((3:ℝ)/2)) * Δ := by
    apply mul_le_mul_of_nonneg_right _ hΔnn
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Real.rpow_nonneg hZ0.le _) (by positivity))
    exact le_add_of_nonneg_right (Real.rpow_nonneg hΔ0.le _)
  have hX : (0:ℝ) ≤ Z ^ ((9:ℝ)/2) * Δ^2 * (Z ^ ((3:ℝ)/2) + Δ ^ ((3:ℝ)/2)) * Δ := by
    apply mul_nonneg; apply mul_nonneg; apply mul_nonneg
    · exact Real.rpow_nonneg hZ0.le _
    · positivity
    · exact add_nonneg (Real.rpow_nonneg hZ0.le _) (Real.rpow_nonneg hΔ0.le _)
    · exact hΔnn
  calc Z^6 * Δ^3 = Z ^ ((9:ℝ)/2) * Δ^2 * Z ^ ((3:ℝ)/2) * Δ := key.symm
    _ ≤ Z ^ ((9:ℝ)/2) * Δ^2 * (Z ^ ((3:ℝ)/2) + Δ ^ ((3:ℝ)/2)) * Δ := mulstep
    _ ≤ 1000 * (Z ^ ((9:ℝ)/2) * Δ^2 * (Z ^ ((3:ℝ)/2) + Δ ^ ((3:ℝ)/2)) * Δ) :=
        le_mul_of_one_le_left hX (by norm_num)
    _ = 1000 * Z ^ ((9:ℝ)/2) * Δ^2 * (Z ^ ((3:ℝ)/2) + Δ ^ ((3:ℝ)/2)) * Δ := by ring

/-- Regime `Δ ≤ 1000 M⁵³`: the first argument `Z⁶Δ³` of the minimum is at most the
right-hand side (with `M⁵³` in place of `min Δ (M⁵³)`). -/
theorem ell44_arith_case2a :
    ∀ Z Δ M : ℝ, 1 ≤ Z → 1 ≤ Δ → 1 ≤ M → Δ ≤ 1000 * M^53 →
      Z^6 * Δ^3 ≤ 1000 * Z ^ ((9:ℝ)/2) * Δ^2 * (Z ^ ((3:ℝ)/2) + Δ ^ ((3:ℝ)/2)) * M^53 := by
  intro Z Δ M hZ hΔ hM h1
  have hZ0 : 0 < Z := by linarith
  have hΔ0 : 0 < Δ := by linarith
  have hZnn : (0:ℝ) ≤ Z := hZ0.le
  have hΔnn : (0:ℝ) ≤ Δ := hΔ0.le
  have e1 : Z ^ ((9:ℝ)/2) * Z ^ ((3:ℝ)/2) = Z^6 := by
    rw [← Real.rpow_add hZ0]
    rw [show (9:ℝ)/2 + 3/2 = ((6:ℕ):ℝ) by norm_num]
    exact Real.rpow_natCast Z 6
  have hs : Z^6 ≤ Z ^ ((9:ℝ)/2) * (Z ^ ((3:ℝ)/2) + Δ ^ ((3:ℝ)/2)) := by
    rw [mul_add, e1]
    exact le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg hZnn _) (Real.rpow_nonneg hΔnn _))
  have hfac : (0:ℝ) ≤ Z^6 * Δ^2 := by positivity
  have hstep1 : Z^6 * Δ^3 ≤ Z^6 * (1000 * M^53) * Δ^2 := by
    have := mul_le_mul_of_nonneg_left h1 hfac
    nlinarith [this]
  have hfac2 : (0:ℝ) ≤ 1000 * Δ^2 * M^53 := by positivity
  calc Z^6 * Δ^3 ≤ Z^6 * (1000 * M^53) * Δ^2 := hstep1
    _ = 1000 * Δ^2 * M^53 * Z^6 := by ring
    _ ≤ 1000 * Δ^2 * M^53 * (Z ^ ((9:ℝ)/2) * (Z ^ ((3:ℝ)/2) + Δ ^ ((3:ℝ)/2))) :=
        mul_le_mul_of_nonneg_left hs hfac2
    _ = 1000 * Z ^ ((9:ℝ)/2) * Δ^2 * (Z ^ ((3:ℝ)/2) + Δ ^ ((3:ℝ)/2)) * M^53 := by ring

theorem ell44_arith :
    ∃ K : ℝ, 0 < K ∧ ∀ Z Δ M : ℝ, 1 ≤ Z → 1 ≤ Δ → 1 ≤ M →
      min (Z ^ 6 * Δ ^ 3)
          (M ^ 70 * (Z ^ 4 * Δ ^ ((11 : ℝ) / 3) + Z ^ 4 * Δ ^ ((7 : ℝ) / 2)
              + Z ^ 6 * Δ ^ ((3 : ℝ) / 2))
            + M ^ 40 * (Z ^ 4 * Δ ^ 3 + Z ^ 6 * Δ ^ 2))
        ≤ K * Z ^ ((9 : ℝ) / 2) * Δ ^ 2 * (Z ^ ((3 : ℝ) / 2) + Δ ^ ((3 : ℝ) / 2))
            * min Δ (M ^ 53) := by
  refine ⟨1000, by norm_num, ?_⟩
  intro Z Δ M hZ hΔ hM
  by_cases h1 : Δ ≤ M^53
  · rw [min_eq_left h1]
    exact le_trans (min_le_left _ _) (ell44_arith_case1 Z Δ M hZ hΔ hM h1)
  · rw [not_le] at h1
    rw [min_eq_right (le_of_lt h1)]
    by_cases h2 : Δ ≤ 1000 * M^53
    · exact le_trans (min_le_left _ _) (ell44_arith_case2a Z Δ M hZ hΔ hM h2)
    · rw [not_le] at h2
      by_cases h3 : Z^3 ≤ 1000^2 * M^106 * Δ
      · exact le_trans (min_le_left _ _) (ell44_arith_case2b Z Δ M hZ hΔ hM h3)
      · rw [not_le] at h3
        exact le_trans (min_le_right _ _) (ell44_arith_case2c Z Δ M hZ hΔ hM h2 h3)

end Work.HP.MDEstimates
