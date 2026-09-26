import Mathlib
import Submission.Work.Asymptotics.KhatE1Defs
import Submission.Work.Residues.ThetaAux
import Submission.Work.Residues.ThetaDecay
import Submission.Work.Residues.LamSExpBound

/-!
# The principal branch of `log λ_S` on the funnel

CKMRV (Cohn--Kumar--Miller--Radchenko--Viazovska, Ann. of Math. 196 (2022)) use, in
Section 2.1.5, the *normalised* logarithm `𝓛_S` of `λ_S = 1 - λ = θ₀₁⁴/θ₀₀⁴`.  The data of
`Work.Kernels.LogLambdaData` fixes `𝓛_S` only through the transformation laws (2.9); on the
funnel it agrees with the explicit branch

  `Λ_S(z) = 4 log θ₀₁(z) - 4 log θ₀₀(z)`

of `Submission/Work/Kernels/LogLambda/LambdaLaws.lean`.  Here we record the fact that on the
funnel this branch is the *principal* logarithm of `λ_S`, i.e.

  `𝓛_S τ = Complex.log (W τ / U τ)`,   `τ ∈ 𝓕 = 𝒟 ∩ {im ≥ 2}`.

The proof only needs the exponential decay of `Λ_S` along the funnel: with
`ε = e^{-π im z} ≤ e^{-2π} ≤ 1/25` and `‖log θ₀₀ z‖, ‖log θ₀₁ z‖ ≤ (24/7) ε`
(`Work.Residues.norm_log_thetaC00_le_exp`, `norm_log_thetaC01_le_exp`) one gets
`‖Λ_S z‖ ≤ (192/7) ε < π`, so `(Λ_S z).im ∈ (-π, π]` and `Complex.log_exp` applies to
`Complex.exp (Λ_S z) = λ_S(z)` (`Work.Kernels.LogLambda.exp_LamS_W`).
-/

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane

noncomputable section

/-- `e^{-πy} ≤ 1/25` for `y ≥ 2`. -/
private lemma exp_neg_pi_mul_le_inv_25 {y : ℝ} (hy : 2 ≤ y) :
    Real.exp (-Real.pi * y) ≤ 1 / 25 := by
  have h6 : (6 : ℝ) ≤ Real.pi * y := by nlinarith [Real.pi_gt_three, hy]
  have hle : Real.exp (-Real.pi * y) ≤ Real.exp (-6) := Real.exp_le_exp.mpr (by linarith)
  have h25 : (25 : ℝ) ≤ Real.exp 6 := by
    have h := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 6 by norm_num)
    nlinarith
  rw [Real.exp_neg] at hle
  calc Real.exp (-Real.pi * y) ≤ (Real.exp 6)⁻¹ := hle
    _ ≤ (25 : ℝ)⁻¹ := by
        rw [inv_le_inv₀ (Real.exp_pos 6) (by norm_num)]
        exact h25
    _ = 1 / 25 := by norm_num

/-- `‖Λ_S z‖ ≤ (192/7) e^{-π im z}` for `im z ≥ 1`. -/
private lemma norm_LamS_le_exp {z : ℂ} (hz : 1 ≤ z.im) :
    ‖Work.Kernels.LogLambda.LamS z‖ ≤ (192 / 7) * Real.exp (-Real.pi * z.im) := by
  have h1 := Work.Residues.norm_log_thetaC01_le_exp z hz
  have h2 := Work.Residues.norm_log_thetaC00_le_exp z hz
  rw [Work.Kernels.LogLambda.LamS]
  calc ‖4 * Complex.log (Work.Kernels.LogLambda.thetaC01 z)
        - 4 * Complex.log (Work.Kernels.LogLambda.thetaC00 z)‖
      ≤ ‖4 * Complex.log (Work.Kernels.LogLambda.thetaC01 z)‖
        + ‖4 * Complex.log (Work.Kernels.LogLambda.thetaC00 z)‖ := norm_sub_le _ _
    _ = 4 * ‖Complex.log (Work.Kernels.LogLambda.thetaC01 z)‖
        + 4 * ‖Complex.log (Work.Kernels.LogLambda.thetaC00 z)‖ := by simp
    _ ≤ 4 * ((24 / 7) * Real.exp (-Real.pi * z.im))
        + 4 * ((24 / 7) * Real.exp (-Real.pi * z.im)) := by linarith
    _ = (192 / 7) * Real.exp (-Real.pi * z.im) := by ring

/-- On `{im z ≥ 2}` the imaginary part of `Λ_S z` lies in the fundamental strip `(-π, π]` of
the principal logarithm. -/
private lemma LamS_im_mem {z : ℂ} (hz : 2 ≤ z.im) :
    -(Real.pi) < (Work.Kernels.LogLambda.LamS z).im ∧
      (Work.Kernels.LogLambda.LamS z).im ≤ Real.pi := by
  have hz1 : (1 : ℝ) ≤ z.im := by linarith
  have hε := exp_neg_pi_mul_le_inv_25 hz
  have hLS := norm_LamS_le_exp hz1
  have hε0 : (0 : ℝ) ≤ Real.exp (-Real.pi * z.im) := (Real.exp_pos _).le
  have hlt : ‖Work.Kernels.LogLambda.LamS z‖ < Real.pi := by
    have hnum : (192 : ℝ) / 7 * (1 / 25) < 3 := by norm_num
    nlinarith [Real.pi_gt_three]
  have him := Complex.abs_im_le_norm (Work.Kernels.LogLambda.LamS z)
  obtain ⟨h1, h2⟩ := abs_lt.mp (lt_of_le_of_lt him hlt)
  exact ⟨h1, le_of_lt h2⟩

theorem E1LS_eq_log (ℓ : Work.Kernels.LogLambdaData) :
    ∀ τ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
      ℓ.L_S τ = Complex.log (Work.Kernels.WFun τ / Work.Kernels.UFun τ) := by
  intro τ hτ
  have h12 : (1 / 2 : ℝ) < τ.im := by linarith [hτ.2]
  have hz2 : (2 : ℝ) ≤ ((τ : ℂ)).im := by rw [UpperHalfPlane.coe_im]; exact hτ.2
  rw [Work.Residues.LogLambdaData_LS_eq_LamS ℓ τ h12]
  have hlam : Work.Kernels.WFun τ / Work.Kernels.UFun τ
      = Work.Kernels.LogLambda.lamSC (τ : ℂ) := rfl
  rw [hlam]
  have hexp : Complex.exp (Work.Kernels.LogLambda.LamS (τ : ℂ))
      = Work.Kernels.LogLambda.lamSC (τ : ℂ) :=
    Work.Kernels.LogLambda.exp_LamS_W _ (by linarith)
  have hstrip := LamS_im_mem hz2
  rw [← hexp, Complex.log_exp hstrip.1 hstrip.2]

end

end Work.Asymptotics.KhatE1
