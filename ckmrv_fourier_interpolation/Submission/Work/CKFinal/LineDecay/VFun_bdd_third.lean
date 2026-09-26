import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.KernelFacts.KPlus_T2
import Submission.Work.Kernels.KernelFacts.psi2_T2
import Submission.Work.Residues.ThetaDecay
import Submission.Work.Modular.ThetaFuncs
import Submission.Work.Modular.theta2_at_cusp

/-!
# `V = θ₁₀⁴` is bounded on the half-plane `{Im z ≥ 1/3}`

The theta quartic `VFun z = θ₁₀(z)⁴ = θ₂(z)⁴` (`Work.Kernels.VFun`) is bounded on the
half-plane `Im z ≥ 1/3` — the region on which the `z`-atoms of the CKMRV kernel bounds are
estimated.

The proof is the direct estimate of the defining theta series
`θ₂(τ) = ∑_{n ∈ ℤ} exp (π i τ (n + 1/2)²)`.  For `y = Im τ ≥ 1/3` the `n`-th summand has
modulus `exp (-π y (n + 1/2)²)`, and since

`(π/3) (n + 1/2)² ≥ π n² / 6 - π / 12`  (equivalently `n²/2 - 1/4 ≤ (n + 1/2)²`),

each summand is bounded by `exp (π/12) · exp (-π n²/6)`, a `τ`-independent summable function
(the theta series `∑_n exp (-π n² / 6)`, summable by
`summable_pow_mul_jacobiTheta₂_term_bound`).  Summing the moduli gives

`‖θ₂ τ‖ ≤ exp (π/12) · ∑_n exp (-π n²/6)`,

and hence `‖V τ‖ ≤ (exp (π/12) · ∑_n exp (-π n²/6))⁴` for every `τ` with `Im τ ≥ 1/3`.

No periodicity or compactness input is needed: the estimate is uniform on the whole
half-plane, and the constant is a convergent theta series rather than an explicit number.
-/

namespace Work.CKFinal.LineDecay

open UpperHalfPlane

noncomputable section

/-- The dominating theta series `∑_n exp (-π n² / 6)` converges. -/
private lemma summable_exp_neg_sq_sixth :
    Summable (fun n : ℤ => Real.exp (-(Real.pi * (n : ℝ) ^ 2 / 6))) := by
  have h := summable_pow_mul_jacobiTheta₂_term_bound (0 : ℝ) (T := 1 / 6) (by norm_num) 0
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h

/-- The dominating theta series `∑_n exp (-π n² / 6)` is positive (its `n = 0` term is `1`). -/
private lemma tsum_exp_neg_sq_sixth_pos :
    0 < (∑' n : ℤ, Real.exp (-(Real.pi * (n : ℝ) ^ 2 / 6))) := by
  have hsum := summable_exp_neg_sq_sixth
  have h0 : Real.exp (-(Real.pi * ((0 : ℤ) : ℝ) ^ 2 / 6)) = 1 := by simp
  have hle := hsum.le_tsum (0 : ℤ) (fun j _ => Real.exp_nonneg _)
  rw [h0] at hle
  linarith

/-- Pointwise domination of the summands of `θ₂` on `{Im ≥ 1/3}`: for every `n : ℤ` and every
`y ≥ 1/3`,

`exp (-π y (n + 1/2)²) ≤ exp (π/12) · exp (-π n² / 6)`.

Indeed the two exponents differ by `(π/6) (n + 1)² ≥ 0` after multiplying by `12`. -/
private lemma theta2_term_le_majorant {y : ℝ} (hy : 1 / 3 ≤ y) (n : ℤ) :
    Real.exp (-Real.pi * y * ((n : ℝ) + 1 / 2) ^ 2) ≤
      Real.exp (Real.pi / 12) * Real.exp (-(Real.pi * (n : ℝ) ^ 2 / 6)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : -Real.pi * y * ((n : ℝ) + 1 / 2) ^ 2 ≤ -(Real.pi / 3) * ((n : ℝ) + 1 / 2) ^ 2 := by
    have hyπ : Real.pi / 3 ≤ Real.pi * y := by nlinarith [Real.pi_pos, hy]
    have hle : (Real.pi / 3) * ((n : ℝ) + 1 / 2) ^ 2 ≤ (Real.pi * y) * ((n : ℝ) + 1 / 2) ^ 2 :=
      mul_le_mul_of_nonneg_right hyπ (sq_nonneg _)
    linarith
  have h2 : -(Real.pi / 3) * ((n : ℝ) + 1 / 2) ^ 2 ≤ Real.pi / 12 - Real.pi * (n : ℝ) ^ 2 / 6 := by
    have hkey : Real.pi / 12 - Real.pi * (n : ℝ) ^ 2 / 6 - (-(Real.pi / 3) * ((n : ℝ) + 1 / 2) ^ 2)
        = (Real.pi / 6) * ((n : ℝ) + 1) ^ 2 := by ring
    have hnn : 0 ≤ (Real.pi / 6) * ((n : ℝ) + 1) ^ 2 := by positivity
    linarith
  linarith

theorem VFun_bdd_third :
    ∃ C : ℝ, 0 < C ∧ ∀ z : UpperHalfPlane, (1 : ℝ) / 3 ≤ z.im → ‖Work.Kernels.VFun z‖ ≤ C := by
  set C₀ : ℝ := ∑' n : ℤ, Real.exp (-(Real.pi * (n : ℝ) ^ 2 / 6)) with hC₀
  have hC₀pos : 0 < C₀ := by rw [hC₀]; exact tsum_exp_neg_sq_sixth_pos
  refine ⟨(Real.exp (Real.pi / 12) * C₀) ^ 4, by positivity, fun z hz => ?_⟩
  have hmaj : Summable (fun n : ℤ =>
      Real.exp (Real.pi / 12) * Real.exp (-(Real.pi * (n : ℝ) ^ 2 / 6))) :=
    summable_exp_neg_sq_sixth.mul_left _
  -- Every summand of the defining series of `θ₂` is dominated by the majorant.
  have hterm : ∀ n : ℤ,
      ‖Complex.exp ((Real.pi : ℂ) * Complex.I * (z : ℂ) * ((n : ℂ) + 1 / 2) ^ 2)‖ ≤
        Real.exp (Real.pi / 12) * Real.exp (-(Real.pi * (n : ℝ) ^ 2 / 6)) := by
    intro n
    rw [Work.Modular.theta2_term_norm z n]
    exact theta2_term_le_majorant (by rw [UpperHalfPlane.coe_im]; exact hz) n
  have hsnorm : Summable (fun n : ℤ =>
      ‖Complex.exp ((Real.pi : ℂ) * Complex.I * (z : ℂ) * ((n : ℂ) + 1 / 2) ^ 2)‖) :=
    hmaj.of_nonneg_of_le (fun n => norm_nonneg _) hterm
  -- The series estimate for `θ₂`.
  have hθ2 : ‖Work.Modular.theta2 z‖ ≤ Real.exp (Real.pi / 12) * C₀ := by
    rw [Work.Modular.theta2_eq_tsum]
    calc ‖∑' n : ℤ, Complex.exp ((Real.pi : ℂ) * Complex.I * (z : ℂ) * ((n : ℂ) + 1 / 2) ^ 2)‖
        ≤ ∑' n : ℤ, ‖Complex.exp ((Real.pi : ℂ) * Complex.I * (z : ℂ) * ((n : ℂ) + 1 / 2) ^ 2)‖ :=
          norm_tsum_le_tsum_norm hsnorm
      _ ≤ ∑' n : ℤ, Real.exp (Real.pi / 12) * Real.exp (-(Real.pi * (n : ℝ) ^ 2 / 6)) :=
          Summable.tsum_le_tsum hterm hsnorm hmaj
      _ = Real.exp (Real.pi / 12) * C₀ := by rw [hC₀, tsum_mul_left]
  -- `V = θ₁₀⁴ = θ₂⁴`.
  have hV : Work.Kernels.VFun z = Work.Modular.theta2 z ^ 4 := rfl
  rw [hV, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hθ2 4


end

end Work.CKFinal.LineDecay
