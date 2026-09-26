import Mathlib
import Submission.Work.FunctionalEquations.TauDiffSetup

/-!
# Polynomial and exponential bounds for the comparison function `tauDiffM`

This file proves `Work.FunctionalEquations.TauDiffMBound`, the pointwise, polynomial and
exponential control of the `τ`-difference combination

`tauDiffF S x τ = F(τ,x) - τ (F(τ+1,x) - F(τ,x))`

of a solution `S` of the functional equations, given

* the strip bound `‖F τ z‖ ≤ α (Im τ)^{-β}` on `-1 ≤ Re τ ≤ 1`,
* the Dirichlet expansion `diffF S x τ = ∑_k c_k e^{2πi(k+1)τ}` on the upper half plane,
* the bound `dirichletNormSum c y ≤ 2 α (y/2)^{-β} e^{-πy}/(1 - e^{-πy})` on the norm sum of
  the coefficients.

The proof reduces an arbitrary point `τ` of the upper half plane to the fundamental strip
`-1 ≤ Re ≤ 0` (`exists_periodic_reduce`), where the strip bound applies; the
`τ`-combination is bounded by `α y^{-β} + (1+y) ‖diffF S x τ‖`, and `diffF` is bounded either
by the crude strip bound `2α y^{-β}` (for `y ≤ 1`) or, through its Dirichlet expansion, by the
norm sum `dirichletNormSum c y`.

The comparison function
`tauDiffM α β c y = 5 α y^{-β}` for `y ≤ 1` and
`α y^{-β} + (1+y) dirichletNormSum c y` for `y > 1`
is then shown to satisfy `tauDiffM α β c y ≤ A y^{-β}` for an explicit constant `A`, and to
decay faster than any power of `e^{-2πy}` at `+∞`.
-/

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology MeasureTheory
open scoped FourierTransform SchwartzMap

noncomputable section

variable {n : ℕ} [NeZero n]

/-! ## Elementary estimates -/

/-- The norm sum `dirichletNormSum c y` of a Dirichlet series with coefficients `c` is
nonnegative. -/
lemma dirichletNormSum_nonneg (c : ℕ → ℂ) (y : ℝ) : 0 ≤ dirichletNormSum c y := by
  rw [dirichletNormSum]
  exact tsum_nonneg fun k => mul_nonneg (norm_nonneg _) (Real.exp_nonneg _)

/-- `(y / 2) ^ (-β) = 2 ^ β * y ^ (-β)` for `y > 0`. -/
lemma div_two_rpow_neg_aux {y : ℝ} (hy : 0 < y) (β : ℝ) :
    (y / 2) ^ (-β) = 2 ^ β * y ^ (-β) := by
  have h2 : ((2 : ℝ)⁻¹) ^ (-β) = 2 ^ β := by
    rw [Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2)]
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    simp
  rw [div_eq_mul_inv, Real.mul_rpow hy.le (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹), h2]
  ring

/-- For `y ≥ 1` the factor `e^{-πy} / (1 - e^{-πy})` is at most its value at `y = 1`. -/
lemma exp_neg_div_le {y : ℝ} (hy : 1 ≤ y) :
    Real.exp (-(Real.pi * y)) / (1 - Real.exp (-(Real.pi * y))) ≤
      Real.exp (-Real.pi) / (1 - Real.exp (-Real.pi)) := by
  have hE : Real.exp (-(Real.pi * y)) ≤ Real.exp (-Real.pi) := by
    rw [Real.exp_le_exp]; nlinarith [Real.pi_pos, hy]
  have hd0 : 0 < 1 - Real.exp (-Real.pi) := by
    have h : Real.exp (-Real.pi) < 1 := Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos])
    linarith
  calc Real.exp (-(Real.pi * y)) / (1 - Real.exp (-(Real.pi * y)))
      ≤ Real.exp (-(Real.pi * y)) / (1 - Real.exp (-Real.pi)) :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le hd0 (by linarith)
    _ ≤ Real.exp (-Real.pi) / (1 - Real.exp (-Real.pi)) :=
        div_le_div_of_nonneg_right hE hd0.le

/-- For `y ≥ 1`, `(1 + y) e^{-πy} ≤ 2`. -/
lemma one_add_mul_exp_neg_pi_le_two {y : ℝ} (hy : 1 ≤ y) :
    (1 + y) * Real.exp (-(Real.pi * y)) ≤ 2 := by
  have hyE : y * Real.exp (-(Real.pi * y)) ≤ 1 := mul_exp_neg_pi_le_one (by linarith)
  have hE : Real.exp (-(Real.pi * y)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, hy]
  nlinarith

/-- For `y ≥ 1`, `(1 + y) e^{-πy} / (1 - e^{-πy}) ≤ 2 / (1 - e^{-π})`. -/
lemma one_add_mul_exp_neg_div_le {y : ℝ} (hy : 1 ≤ y) :
    (1 + y) * (Real.exp (-(Real.pi * y)) / (1 - Real.exp (-(Real.pi * y)))) ≤
      2 / (1 - Real.exp (-Real.pi)) := by
  have hd0 : 0 < 1 - Real.exp (-Real.pi) := by
    have h : Real.exp (-Real.pi) < 1 := Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos])
    linarith
  have hE : Real.exp (-(Real.pi * y)) ≤ Real.exp (-Real.pi) := by
    rw [Real.exp_le_exp]; nlinarith [Real.pi_pos, hy]
  calc (1 + y) * (Real.exp (-(Real.pi * y)) / (1 - Real.exp (-(Real.pi * y))))
      ≤ (1 + y) * (Real.exp (-(Real.pi * y)) / (1 - Real.exp (-Real.pi))) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left (Real.exp_pos _).le hd0 (by linarith)) (by linarith)
    _ = ((1 + y) * Real.exp (-(Real.pi * y))) / (1 - Real.exp (-Real.pi)) := by ring
    _ ≤ 2 / (1 - Real.exp (-Real.pi)) :=
        div_le_div_of_nonneg_right (one_add_mul_exp_neg_pi_le_two hy) hd0.le

/-! ## The comparison function and its bounds -/

/-- The constant `A` in the polynomial bound `tauDiffM α β c y ≤ A y^{-β}`. -/
def tauDiffConst (α β : ℝ) : ℝ :=
  5 * α + 4 * α * 2 ^ β / (1 - Real.exp (-Real.pi))

lemma tauDiffConst_nonneg {α β : ℝ} (hα : 0 ≤ α) : 0 ≤ tauDiffConst α β := by
  have hd0 : 0 < 1 - Real.exp (-Real.pi) := by
    have h : Real.exp (-Real.pi) < 1 := Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos])
    linarith
  rw [tauDiffConst]
  have hnum : 0 ≤ 4 * α * 2 ^ β :=
    mul_nonneg (mul_nonneg (by norm_num) hα) (Real.rpow_nonneg (by norm_num) β)
  exact add_nonneg (mul_nonneg (by norm_num) hα) (div_nonneg hnum hd0.le)

/-- The comparison function `tauDiffM` is nonnegative. -/
lemma tauDiffM_nonneg {α β : ℝ} (hα : 0 ≤ α) (c : ℕ → ℂ) {y : ℝ} (hy : 0 < y) :
    0 ≤ tauDiffM α β c y := by
  rw [tauDiffM]
  split_ifs with h
  · exact mul_nonneg (mul_nonneg (by norm_num) hα) (Real.rpow_nonneg hy.le _)
  · exact add_nonneg (mul_nonneg hα (Real.rpow_nonneg hy.le _))
      (mul_nonneg (by linarith) (dirichletNormSum_nonneg c y))

/-- **Polynomial bound for `tauDiffM`.**  Under the bound on the norm sum `dirichletNormSum c`
the comparison function is dominated by `tauDiffConst α β * y^{-β}`. -/
lemma tauDiffM_le_tauDiffConst_mul_rpow {α β : ℝ} (hα : 0 ≤ α)
    (c : ℕ → ℂ)
    (hPhi : ∀ y : ℝ, 0 < y → dirichletNormSum c y ≤
      2 * α * (y / 2) ^ (-β) *
        (Real.exp (-(Real.pi * y)) / (1 - Real.exp (-(Real.pi * y))))) :
    ∀ y : ℝ, 0 < y → tauDiffM α β c y ≤ tauDiffConst α β * y ^ (-β) := by
  intro y hy
  have hd0 : 0 < 1 - Real.exp (-Real.pi) := by
    have h : Real.exp (-Real.pi) < 1 := Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos])
    linarith
  have hextra_nn : 0 ≤ 4 * α * 2 ^ β / (1 - Real.exp (-Real.pi)) :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hα)
      (Real.rpow_nonneg (by norm_num) β)) hd0.le
  by_cases h1 : y ≤ 1
  · rw [tauDiffM, if_pos h1, tauDiffConst]
    have h5 : 5 * α ≤ 5 * α + 4 * α * 2 ^ β / (1 - Real.exp (-Real.pi)) := by linarith
    exact mul_le_mul_of_nonneg_right h5 (Real.rpow_nonneg hy.le _)
  · have h1' : (1 : ℝ) ≤ y := le_of_lt (not_le.mp h1)
    rw [tauDiffM, if_neg h1, tauDiffConst]
    have hS := hPhi y hy
    have hcoef : 0 ≤ 2 * α * (y / 2) ^ (-β) :=
      mul_nonneg (mul_nonneg (by norm_num) hα)
        (Real.rpow_nonneg (div_nonneg hy.le (by norm_num)) _)
    have hstep1 : (1 + y) * dirichletNormSum c y ≤
        (1 + y) * (2 * α * (y / 2) ^ (-β) *
          (Real.exp (-(Real.pi * y)) / (1 - Real.exp (-(Real.pi * y))))) :=
      mul_le_mul_of_nonneg_left hS (by linarith)
    have hstep2 : (1 + y) * (2 * α * (y / 2) ^ (-β) *
          (Real.exp (-(Real.pi * y)) / (1 - Real.exp (-(Real.pi * y)))))
        = 2 * α * (y / 2) ^ (-β) *
          ((1 + y) * (Real.exp (-(Real.pi * y)) / (1 - Real.exp (-(Real.pi * y))))) := by
      ring
    have hstep3 : 2 * α * (y / 2) ^ (-β) *
          ((1 + y) * (Real.exp (-(Real.pi * y)) / (1 - Real.exp (-(Real.pi * y)))))
        ≤ 2 * α * (y / 2) ^ (-β) * (2 / (1 - Real.exp (-Real.pi))) :=
      mul_le_mul_of_nonneg_left (one_add_mul_exp_neg_div_le h1') hcoef
    have hstep4 : 2 * α * (y / 2) ^ (-β) * (2 / (1 - Real.exp (-Real.pi)))
        = 4 * α * 2 ^ β / (1 - Real.exp (-Real.pi)) * y ^ (-β) := by
      rw [div_two_rpow_neg_aux hy β]; ring
    have hstep5 : α * y ^ (-β) ≤ 5 * α * y ^ (-β) := by
      have h : α ≤ 5 * α := by linarith
      exact mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hy.le _)
    calc α * y ^ (-β) + (1 + y) * dirichletNormSum c y
        ≤ α * y ^ (-β) + (1 + y) * (2 * α * (y / 2) ^ (-β) *
            (Real.exp (-(Real.pi * y)) / (1 - Real.exp (-(Real.pi * y))))) :=
          add_le_add_right hstep1 _
      _ = α * y ^ (-β) + 2 * α * (y / 2) ^ (-β) *
            ((1 + y) * (Real.exp (-(Real.pi * y)) / (1 - Real.exp (-(Real.pi * y))))) := by
          rw [hstep2]
      _ ≤ α * y ^ (-β) + 2 * α * (y / 2) ^ (-β) * (2 / (1 - Real.exp (-Real.pi))) :=
          add_le_add_right hstep3 _
      _ = α * y ^ (-β) + 4 * α * 2 ^ β / (1 - Real.exp (-Real.pi)) * y ^ (-β) := by
          rw [hstep4]
      _ ≤ 5 * α * y ^ (-β) + 4 * α * 2 ^ β / (1 - Real.exp (-Real.pi)) * y ^ (-β) :=
          add_le_add_left hstep5 _
      _ = (5 * α + 4 * α * 2 ^ β / (1 - Real.exp (-Real.pi))) * y ^ (-β) := by ring

/-! ## The main theorem -/

theorem TauDiffMBound {n : ℕ} [NeZero n]
    (S : Work.FE.FunctionalEquationSolution n) (x : Work.FE.E n) (c : ℕ → ℂ)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β)
    (hstrip : ∀ (τ : ℂ) (z : Work.FE.E n), 0 < τ.im → -1 ≤ τ.re → τ.re ≤ 1 →
      ‖S.F τ z‖ ≤ α * τ.im ^ (-β))
    (hc : ∀ τ : ℂ, 0 < τ.im → HasSum (fun k : ℕ =>
      c k * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((k : ℂ) + 1) * τ))
      (Work.FunctionalEquations.diffF S x τ))
    (hPhi : ∀ y : ℝ, 0 < y → Work.FunctionalEquations.dirichletNormSum c y ≤
      2 * α * (y / 2) ^ (-β) * (Real.exp (-(Real.pi * y)) / (1 - Real.exp (-(Real.pi * y))))) :
    (∀ τ : ℂ, 0 < τ.im → ‖Work.FunctionalEquations.tauDiffF S x τ‖ ≤
        Work.FunctionalEquations.tauDiffM α β c τ.im) ∧
      (∃ A β' : ℝ, 0 ≤ A ∧ 0 ≤ β' ∧ ∀ y : ℝ, 0 < y →
        Work.FunctionalEquations.tauDiffM α β c y ≤ A * y ^ (-β')) ∧
      (∀ m : ℕ, Filter.Tendsto (fun y : ℝ =>
        Work.FunctionalEquations.tauDiffM α β c y * Real.exp (-(2 * Real.pi) * y) ^ m)
        Filter.atTop (nhds 0)) := by
  refine ⟨?_, ⟨tauDiffConst α β, β, tauDiffConst_nonneg hα, hβ.le,
    tauDiffM_le_tauDiffConst_mul_rpow hα c hPhi⟩, ?_⟩
  · intro τ hτ
    obtain ⟨τ', him, hre1, hre2, heq⟩ :=
      exists_periodic_reduce (tauDiffF_periodic S x) τ hτ
    have hτ' : 0 < τ'.im := by rw [him]; exact hτ
    have hnorm_eq : ‖tauDiffF S x τ‖ = ‖tauDiffF S x τ'‖ := by rw [heq]
    have hmain := norm_tauDiffF_le S x hstrip hτ' hre1 hre2
    by_cases h1 : τ.im ≤ 1
    · have hle1 : τ'.im ≤ 1 := by rw [him]; exact h1
      have hd := norm_diffF_le S x hstrip τ' hτ'
      have hstep0 : (1 + τ'.im) * ‖diffF S x τ'‖ ≤ (1 + τ'.im) * (2 * α * τ'.im ^ (-β)) :=
        mul_le_mul_of_nonneg_left hd (by linarith)
      have hstep : ‖tauDiffF S x τ'‖ ≤ (3 + 2 * τ'.im) * (α * τ'.im ^ (-β)) := by
        calc ‖tauDiffF S x τ'‖
            ≤ α * τ'.im ^ (-β) + (1 + τ'.im) * ‖diffF S x τ'‖ := hmain
          _ ≤ α * τ'.im ^ (-β) + (1 + τ'.im) * (2 * α * τ'.im ^ (-β)) :=
              add_le_add_right hstep0 _
          _ = (3 + 2 * τ'.im) * (α * τ'.im ^ (-β)) := by ring
      have h5 : (3 + 2 * τ'.im) * (α * τ'.im ^ (-β)) ≤ 5 * (α * τ'.im ^ (-β)) := by
        have hc0 : 0 ≤ α * τ'.im ^ (-β) := mul_nonneg hα (Real.rpow_nonneg hτ'.le _)
        have h32 : 3 + 2 * τ'.im ≤ 5 := by linarith
        exact mul_le_mul_of_nonneg_right h32 hc0
      calc ‖tauDiffF S x τ‖ = ‖tauDiffF S x τ'‖ := hnorm_eq
        _ ≤ 5 * (α * τ'.im ^ (-β)) := le_trans hstep h5
        _ = tauDiffM α β c τ.im := by
            rw [tauDiffM, if_pos h1, him]; ring
    · have h2 : ‖diffF S x τ'‖ ≤ dirichletNormSum c τ'.im :=
        norm_le_dirichletNormSum (g := diffF S x) hc hτ'
      have hstep0 : (1 + τ'.im) * ‖diffF S x τ'‖ ≤
          (1 + τ'.im) * dirichletNormSum c τ'.im :=
        mul_le_mul_of_nonneg_left h2 (by linarith)
      have hstep : ‖tauDiffF S x τ'‖ ≤
          α * τ'.im ^ (-β) + (1 + τ'.im) * dirichletNormSum c τ'.im :=
        calc ‖tauDiffF S x τ'‖
            ≤ α * τ'.im ^ (-β) + (1 + τ'.im) * ‖diffF S x τ'‖ := hmain
          _ ≤ α * τ'.im ^ (-β) + (1 + τ'.im) * dirichletNormSum c τ'.im :=
              add_le_add_right hstep0 _
      calc ‖tauDiffF S x τ‖ = ‖tauDiffF S x τ'‖ := hnorm_eq
        _ ≤ α * τ'.im ^ (-β) + (1 + τ'.im) * dirichletNormSum c τ'.im := hstep
        _ = tauDiffM α β c τ.im := by rw [tauDiffM, if_neg h1, him]
  · intro m
    have hbdd : ∀ y : ℝ, 0 < y → tauDiffM α β c y ≤ tauDiffConst α β * y ^ (-β) :=
      tauDiffM_le_tauDiffConst_mul_rpow hα c hPhi
    refine squeeze_zero'
      (g := fun y : ℝ => tauDiffConst α β * y ^ (-β) * Real.exp (-(2 * Real.pi) * y) ^ m)
      ?_ ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
      exact mul_nonneg (tauDiffM_nonneg hα c hy) (pow_nonneg (Real.exp_nonneg _) m)
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
      exact mul_le_mul_of_nonneg_right (hbdd y hy) (pow_nonneg (Real.exp_nonneg _) m)
    · simpa [mul_assoc] using (tendsto_rpow_neg_mul_exp hβ m).const_mul (tauDiffConst α β)

end

end Work.FunctionalEquations
