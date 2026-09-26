import Mathlib
import Submission.Work.Kernels.Classical
import Submission.Work.Kernels.Kernels

namespace Work.Residues

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups Manifold Modular ModularForm

noncomputable section

/-- The cusp parameter `E τ = e^{πiτ}`, whose norm is `e^{-π Im τ}`. -/
def Ept (τ : ℍ) : ℂ := Complex.exp (Real.pi * Complex.I * (τ : ℂ))

@[simp] lemma Ept_apply (τ : ℍ) : Ept τ = Complex.exp (Real.pi * Complex.I * (τ : ℂ)) := rfl

lemma norm_Ept (τ : ℍ) : ‖Ept τ‖ = Real.exp (-(Real.pi * τ.im)) := by
  rw [Ept, Complex.norm_exp]
  congr 1
  rw [show (Real.pi : ℂ) * Complex.I * (τ : ℂ)
      = ((Real.pi : ℝ) : ℂ) * (Complex.I * (τ : ℂ)) by ring]
  rw [Complex.re_ofReal_mul, Complex.I_mul_re]
  rw [UpperHalfPlane.coe_im]
  ring

lemma norm_Ept_coe (τ : ℍ) : ‖Ept τ‖ = Real.exp (-(Real.pi * (τ : ℂ).im)) := by
  rw [norm_Ept, UpperHalfPlane.coe_im]

lemma exp_neg_pi_im_nat_mul (τ : ℍ) (k : ℕ) :
    Real.exp (-(Real.pi * (k : ℝ) * τ.im)) = ‖Ept τ‖ ^ k := by
  rw [norm_Ept, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma Ept_ne_zero (τ : ℍ) : Ept τ ≠ 0 := Complex.exp_ne_zero _

lemma norm_Ept_lt_one (τ : ℍ) : ‖Ept τ‖ < 1 := by
  rw [norm_Ept, Real.exp_lt_one_iff]
  nlinarith [Real.pi_pos, τ.im_pos]

lemma norm_Ept_le_exp_neg_pi (τ : ℍ) (hτ : 1 ≤ τ.im) : ‖Ept τ‖ ≤ Real.exp (-Real.pi) := by
  rw [norm_Ept]
  exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, hτ])

lemma exp_neg_two_pi_lt_one : Real.exp (-(2 * Real.pi)) < 1 := by
  rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]

lemma exp_neg_two_pi_pos : 0 < Real.exp (-(2 * Real.pi)) := Real.exp_pos _

lemma norm_Ept_sq_le (τ : ℍ) (hτ : 1 ≤ τ.im) : ‖Ept τ‖ ^ 2 ≤ Real.exp (-(2 * Real.pi)) := by
  have h := norm_Ept_le_exp_neg_pi τ hτ
  have h0 : 0 ≤ ‖Ept τ‖ := norm_nonneg _
  have he : 0 < Real.exp (-Real.pi) := Real.exp_pos _
  calc ‖Ept τ‖ ^ 2 ≤ (Real.exp (-Real.pi)) ^ 2 := by nlinarith
    _ = Real.exp (-(2 * Real.pi)) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring

/-- `E(τ+1) = -E(τ)`. -/
lemma Ept_T (τ : ℍ) : Ept (ModularGroup.T • τ) = - Ept τ := by
  have hlin : (Real.pi : ℂ) * Complex.I * (((ModularGroup.T • τ : ℍ)) : ℂ)
      = Real.pi * Complex.I * (τ : ℂ) + Real.pi * Complex.I := by
    rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.coe_vadd]
    push_cast
    ring
  rw [Ept, Ept, hlin, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

/-- The norm of `exp (π i m² τ)` is `exp (-π m² Im τ)`. -/
lemma norm_cexp_pi_I_sq_mul (τ : ℂ) (m : ℕ) :
    ‖Complex.exp (Real.pi * Complex.I * (m : ℂ) ^ 2 * τ)‖
      = Real.exp (-(Real.pi * (m : ℝ) ^ 2 * τ.im)) := by
  rw [Complex.norm_exp]
  congr 1
  have h : Real.pi * Complex.I * (m : ℂ) ^ 2 * τ
      = ((Real.pi * (m : ℝ) ^ 2 : ℝ) : ℂ) * (Complex.I * τ) := by push_cast; ring
  rw [h, Complex.re_ofReal_mul, Complex.I_mul_re]
  ring

/-- The norm of `exp (π i (n+1)² τ)` is `exp (-π (n+1)² Im τ)`. -/
lemma norm_cexp_pi_I_sq_mul' (τ : ℂ) (n : ℕ) :
    ‖Complex.exp (Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * τ)‖
      = Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * τ.im)) := by
  rw [Complex.norm_exp]
  congr 1
  have h : Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * τ
      = ((Real.pi * ((n : ℝ) + 1) ^ 2 : ℝ) : ℂ) * (Complex.I * τ) := by push_cast; ring
  rw [h, Complex.re_ofReal_mul, Complex.I_mul_re]
  ring

/-- The expansion `θ₀₀ = 1 + 2E + O(‖E‖⁴)` at the cusp. -/
theorem theta00Fun_expansion :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, 1 ≤ τ.im →
      ‖Work.Kernels.theta00Fun τ - 1 - 2 * Ept τ‖ ≤ C * ‖Ept τ‖ ^ 4 := by
  refine ⟨2 / (1 - Real.exp (-(2 * Real.pi))), ?_, ?_⟩
  · have h := exp_neg_two_pi_lt_one
    positivity
  · intro τ hτ
    set r : ℝ := ‖Ept τ‖ with hr
    have hr0 : 0 ≤ r := norm_nonneg _
    have hr1 : r < 1 := norm_Ept_lt_one τ
    have hr2lt : r ^ 2 < 1 := by nlinarith
    have hy : 0 < (τ : ℂ).im := by simpa using τ.im_pos
    have hsum : HasSum
        (fun n : ℕ => Complex.exp (Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * (τ : ℂ)))
        ((Work.Kernels.theta00Fun τ - 1) / 2) := by
      simpa [Work.Kernels.theta00Fun] using hasSum_nat_jacobiTheta hy
    have htheta : Work.Kernels.theta00Fun τ
        = 1 + 2 * (∑' n : ℕ, Complex.exp (Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * (τ : ℂ))) := by
      have h := jacobiTheta_eq_tsum_nat hy
      rw [show Work.Kernels.theta00Fun τ = jacobiTheta (τ : ℂ) from rfl, h]
    set F : ℕ → ℂ := fun n => Complex.exp (Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * (τ : ℂ))
      with hFdef
    have hSsum : Summable F := hsum.summable
    have hsplit : (∑' n : ℕ, F n) = F 0 + ∑' n : ℕ, F (n + 1) := hSsum.tsum_eq_zero_add
    have hF0 : F 0 = Ept τ := by simp [hFdef, Ept]
    -- each tail term is `‖F (n+1)‖ = r ^ ((n+2)^2)`
    have hnorm_eq : ∀ m : ℕ, ‖F m‖ = r ^ ((m + 1) ^ 2) := by
      intro m
      have h1 : ‖F m‖ = Real.exp (-(Real.pi * ((m : ℝ) + 1) ^ 2 * τ.im)) := by
        simp only [hFdef]
        rw [norm_cexp_pi_I_sq_mul' (τ : ℂ) m, UpperHalfPlane.coe_im]
      rw [h1, show ((m : ℝ) + 1) ^ 2 = (((m + 1) ^ 2 : ℕ) : ℝ) by push_cast; ring,
        exp_neg_pi_im_nat_mul, ← hr]
    have htailterm : ∀ n : ℕ, ‖F (n + 1)‖ ≤ r ^ (2 * n + 4) := by
      intro n
      rw [hnorm_eq (n + 1)]
      have h2 : 2 * (n + 2) ≤ (n + 2) ^ 2 := by nlinarith
      show r ^ ((n + 1 + 1) ^ 2) ≤ r ^ (2 * n + 4)
      calc r ^ ((n + 1 + 1) ^ 2) = r ^ ((n + 2) ^ 2) := by ring_nf
        _ ≤ r ^ (2 * (n + 2)) := pow_le_pow_of_le_one hr0 (le_of_lt hr1) h2
        _ = r ^ (2 * n + 4) := by
              rw [show 2 * (n + 2) = 2 * n + 4 by ring]
    have hg : HasSum (fun n : ℕ => r ^ (2 * n + 4)) (r ^ 4 / (1 - r ^ 2)) := by
      have h := (hasSum_geometric_of_lt_one (show (0:ℝ) ≤ r^2 by positivity) hr2lt).mul_left (r^4)
      have h' : HasSum (fun n : ℕ => r ^ 4 * (r ^ 2) ^ n) (r ^ 4 * (1 - r ^ 2)⁻¹) := h
      refine h'.congr_fun (fun n => ?_)
      rw [← pow_mul, ← pow_add,
        show 4 + 2 * n = 2 * n + 4 by ring]
    have hsumtail : Summable (fun n : ℕ => ‖F (n + 1)‖) :=
      Summable.of_nonneg_of_le (fun n => norm_nonneg _) htailterm hg.summable
    have htail : ‖∑' n : ℕ, F (n + 1)‖ ≤ r ^ 4 / (1 - Real.exp (-(2 * Real.pi))) := by
      refine le_trans (norm_tsum_le_tsum_norm hsumtail) ?_
      have h1 : (∑' n : ℕ, ‖F (n + 1)‖) ≤ ∑' n : ℕ, r ^ (2 * n + 4) :=
        Summable.tsum_le_tsum htailterm hsumtail hg.summable
      rw [hg.tsum_eq] at h1
      refine le_trans h1 ?_
      have hden : 0 < 1 - Real.exp (-(2 * Real.pi)) := by linarith [exp_neg_two_pi_lt_one]
      have hden2 : 0 < 1 - r ^ 2 := by linarith
      have hre : r ^ 2 ≤ Real.exp (-(2 * Real.pi)) := by rw [hr]; exact norm_Ept_sq_le τ hτ
      rw [div_eq_mul_inv, div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact inv_anti₀ hden (by linarith)
    have hmain : Work.Kernels.theta00Fun τ - 1 - 2 * Ept τ = 2 * ∑' n : ℕ, F (n + 1) := by
      rw [htheta, hsplit, hF0]
      ring
    rw [hmain, norm_mul, Complex.norm_ofNat, hr]
    calc 2 * ‖∑' n : ℕ, F (n + 1)‖
        ≤ 2 * (r ^ 4 / (1 - Real.exp (-(2 * Real.pi)))) := by linarith [htail]
      _ = 2 / (1 - Real.exp (-(2 * Real.pi))) * r ^ 4 := by ring

end

end Work.Residues
