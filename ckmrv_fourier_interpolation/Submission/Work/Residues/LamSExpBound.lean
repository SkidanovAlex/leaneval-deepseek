/-
# Exponential decay of the explicit branch `Λ_S` of `log λ_S`

`Λ_S(z) = 4 log θ₀₁(z) - 4 log θ₀₀(z)` (CKMRV, Section 2.1.5) is a logarithm of
`λ_S = θ₀₁⁴/θ₀₀⁴` on the half plane `W = {im z > 1/2}`.  On `W ∩ {im z ≥ 1}` both theta
functions are exponentially close to `1`: Mathlib's estimate

  `‖θ₀₀ z - 1‖ ≤ 2 e^{-π im z} / (1 - e^{-π im z})`

together with `e^{-π im z} ≤ e^{-π} ≤ 1/8` gives `‖θ₀₀ z - 1‖ ≤ (16/7) e^{-π im z} ≤ 1/2`, so
the principal logarithm expands with `‖log (1 + w)‖ ≤ (3/2) ‖w‖` for `‖w‖ ≤ 1/2`:

  `‖log θ₀₀ z‖ ≤ (24/7) e^{-π im z}`,

and the same bound holds for `θ₀₁ z = θ₀₀(z+1)` (Mathlib's `jacobiTheta₂ (1/2) z = θ₀₀ (z+1)`,
which has the same imaginary part).  Adding the two contributions with weight `4` gives
`‖Λ_S z‖ ≤ (192/7) e^{-π im z}`, so `C = 28` works.
-/
import Mathlib
import Submission.Work.Kernels.LogLambda.LambdaLaws
import Submission.Work.Kernels.LogLambda.LogGrowth.Lfun_sub_pi_I_bound

namespace Work.Residues

open Work.Kernels.LogLambda

/-- For `y ≥ 1`, `2 e^{-πy}/(1 - e^{-πy}) ≤ (16/7) e^{-πy}`: indeed `e^{-πy} ≤ e^{-π} ≤ 1/8`,
so `1 - e^{-πy} ≥ 7/8`. -/
lemma two_div_one_sub_mul_le (y : ℝ) (hy : 1 ≤ y) :
    2 / (1 - Real.exp (-Real.pi * y)) * Real.exp (-Real.pi * y)
      ≤ (16 / 7) * Real.exp (-Real.pi * y) := by
  have he : Real.exp (-Real.pi * y) ≤ 1 / 8 :=
    LogGrowth.exp_le_inv_eight_of_le_neg_pi (by nlinarith [Real.pi_pos, hy])
  have hepos : 0 < Real.exp (-Real.pi * y) := Real.exp_pos _
  have hden : 0 < 1 - Real.exp (-Real.pi * y) := by linarith
  have h : 2 / (1 - Real.exp (-Real.pi * y)) ≤ 16 / 7 := by
    rw [div_le_div_iff₀ hden (by norm_num)]
    linarith
  exact mul_le_mul_of_nonneg_right h hepos.le

/-- `‖θ₀₀ z - 1‖ ≤ (16/7) e^{-π im z}` for `im z ≥ 1`. -/
lemma thetaC00_sub_one_le_exp (z : ℂ) (hz : 1 ≤ z.im) :
    ‖thetaC00 z - 1‖ ≤ (16 / 7) * Real.exp (-Real.pi * z.im) := by
  have h1 : ‖thetaC00 z - 1‖
      ≤ 2 / (1 - Real.exp (-Real.pi * z.im)) * Real.exp (-Real.pi * z.im) := by
    show ‖jacobiTheta z - 1‖ ≤ _
    exact norm_jacobiTheta_sub_one_le (by linarith)
  exact h1.trans (two_div_one_sub_mul_le z.im hz)

/-- `‖log θ₀₀ z‖ ≤ (24/7) e^{-π im z}` for `im z ≥ 1`. -/
lemma norm_log_thetaC00_le_exp (z : ℂ) (hz : 1 ≤ z.im) :
    ‖Complex.log (thetaC00 z)‖ ≤ (24 / 7) * Real.exp (-Real.pi * z.im) := by
  have h3 := thetaC00_sub_one_le_exp z hz
  have he : Real.exp (-Real.pi * z.im) ≤ 1 / 8 :=
    LogGrowth.exp_le_inv_eight_of_le_neg_pi (by nlinarith [Real.pi_pos, hz])
  have h4 : ‖thetaC00 z - 1‖ ≤ 1 / 2 := by
    nlinarith [h3, he, Real.exp_pos (-Real.pi * z.im)]
  have h5 := Complex.norm_log_one_add_half_le_self (z := thetaC00 z - 1) h4
  rw [show (1 : ℂ) + (thetaC00 z - 1) = thetaC00 z by ring] at h5
  calc ‖Complex.log (thetaC00 z)‖ ≤ 3 / 2 * ‖thetaC00 z - 1‖ := h5
    _ ≤ 3 / 2 * ((16 / 7) * Real.exp (-Real.pi * z.im)) := by linarith
    _ = (24 / 7) * Real.exp (-Real.pi * z.im) := by ring

/-- `‖θ₀₁ z - 1‖ ≤ (16/7) e^{-π im z}` for `im z ≥ 1`. -/
lemma thetaC01_sub_one_le_exp (z : ℂ) (hz : 1 ≤ z.im) :
    ‖thetaC01 z - 1‖ ≤ (16 / 7) * Real.exp (-Real.pi * z.im) := by
  have him : (z + 1).im = z.im := by simp
  have h1 : ‖thetaC01 z - 1‖
      ≤ 2 / (1 - Real.exp (-Real.pi * z.im)) * Real.exp (-Real.pi * z.im) := by
    have h := norm_jacobiTheta_sub_one_le (τ := z + 1) (by rw [him]; linarith)
    rw [him] at h
    show ‖jacobiTheta₂ (1 / 2) z - 1‖ ≤ _
    rw [Work.Kernels.ClassicalFacts.jacobiTheta₂_half_eq_jacobiTheta_add_one]
    exact h
  exact h1.trans (two_div_one_sub_mul_le z.im hz)

/-- `‖log θ₀₁ z‖ ≤ (24/7) e^{-π im z}` for `im z ≥ 1`. -/
lemma norm_log_thetaC01_le_exp (z : ℂ) (hz : 1 ≤ z.im) :
    ‖Complex.log (thetaC01 z)‖ ≤ (24 / 7) * Real.exp (-Real.pi * z.im) := by
  have h3 := thetaC01_sub_one_le_exp z hz
  have he : Real.exp (-Real.pi * z.im) ≤ 1 / 8 :=
    LogGrowth.exp_le_inv_eight_of_le_neg_pi (by nlinarith [Real.pi_pos, hz])
  have h4 : ‖thetaC01 z - 1‖ ≤ 1 / 2 := by
    nlinarith [h3, he, Real.exp_pos (-Real.pi * z.im)]
  have h5 := Complex.norm_log_one_add_half_le_self (z := thetaC01 z - 1) h4
  rw [show (1 : ℂ) + (thetaC01 z - 1) = thetaC01 z by ring] at h5
  calc ‖Complex.log (thetaC01 z)‖ ≤ 3 / 2 * ‖thetaC01 z - 1‖ := h5
    _ ≤ 3 / 2 * ((16 / 7) * Real.exp (-Real.pi * z.im)) := by linarith
    _ = (24 / 7) * Real.exp (-Real.pi * z.im) := by ring

theorem LamSExpBound :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z ∈ Work.Kernels.LogLambda.W → 1 ≤ z.im →
      ‖Work.Kernels.LogLambda.LamS z‖ ≤ C * Real.exp (-(Real.pi * z.im)) := by
  refine ⟨28, by norm_num, ?_⟩
  intro z _ hz
  have h1 := norm_log_thetaC01_le_exp z hz
  have h2 := norm_log_thetaC00_le_exp z hz
  have hpos : 0 < Real.exp (-Real.pi * z.im) := Real.exp_pos _
  have heq : Real.exp (-(Real.pi * z.im)) = Real.exp (-Real.pi * z.im) := by
    congr 1; ring
  rw [heq]
  calc ‖LamS z‖
      = ‖4 * Complex.log (thetaC01 z) - 4 * Complex.log (thetaC00 z)‖ := by rw [LamS]
    _ ≤ ‖4 * Complex.log (thetaC01 z)‖ + ‖4 * Complex.log (thetaC00 z)‖ := norm_sub_le _ _
    _ = 4 * ‖Complex.log (thetaC01 z)‖ + 4 * ‖Complex.log (thetaC00 z)‖ := by
        simp
    _ ≤ 4 * ((24 / 7) * Real.exp (-Real.pi * z.im))
          + 4 * ((24 / 7) * Real.exp (-Real.pi * z.im)) := by linarith
    _ = (192 / 7) * Real.exp (-Real.pi * z.im) := by ring
    _ ≤ 28 * Real.exp (-Real.pi * z.im) := by nlinarith [hpos]

end Work.Residues
