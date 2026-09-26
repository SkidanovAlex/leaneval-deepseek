import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Residues.ThetaEpt
import Submission.Work.Asymptotics.cusp_invDelta
import Submission.Work.Asymptotics.E4cube_cusp_second

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

/-!
# The second-order cusp expansion of `j·q`

With `q(τ) = qParamFun τ = e^{2πiτ}` and `j = E₄³/Δ` the modular `j`-invariant, one has
`j(τ)·q(τ) = 1 + 744 q(τ) + O(‖q(τ)‖²)` as `Im τ → ∞`.  The proof combines the cusp
expansions `E4cube_cusp_second` (`E₄³ = 1 + 720 q + O(q²)`) and `cusp_invDelta`
(`Δ⁻¹ = q⁻¹ + 24 + O(q)`).
-/

/-- Norm of a six-term sum. -/
private lemma norm_chain6 (a b c d e f : ℂ) :
    ‖a + b + c + d + e + f‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ := by
  have h1 := norm_add_le (a + b + c + d + e) f
  have h2 := norm_add_le (a + b + c + d) e
  have h3 := norm_add_le (a + b + c) d
  have h4 := norm_add_le (a + b) c
  have h5 := norm_add_le a b
  linarith

/-- **The second-order cusp expansion of `j·q`.** -/
theorem jq_second_order :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, 2 ≤ τ.im →
      ‖Work.Kernels.jInvariantFun τ * Work.Kernels.qParamFun τ - 1
        - 744 * Work.Kernels.qParamFun τ‖ ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by
  obtain ⟨A, hA, hAc⟩ := Work.Asymptotics.E4cube_cusp_second
  obtain ⟨Cs, hCs, hsc⟩ := Work.Asymptotics.cusp_invDelta
  refine ⟨A + Cs + 720 * Cs + 17280 + 24 * A + A * Cs + 1, by positivity, fun τ hτ => ?_⟩
  have h1 : 1 ≤ τ.im := by linarith
  set q : ℂ := Work.Kernels.qParamFun τ with hqdef
  set E : ℂ := Work.Residues.Ept τ with hEdef
  have hqE : q = E ^ 2 := by
    rw [hqdef, hEdef, Work.Kernels.qParamFun, Work.Residues.Ept, sq, ← Complex.exp_add]
    congr 1; ring
  have hEnz : E ≠ 0 := by rw [hEdef]; exact Work.Residues.Ept_ne_zero τ
  have hqnz : q ≠ 0 := by rw [hqE]; exact pow_ne_zero 2 hEnz
  have hinv : (E)⁻¹ ^ 2 = q⁻¹ := by rw [hqE, inv_pow]
  have hqnorm : ‖q‖ = ‖E‖ ^ 2 := by rw [hqE, norm_pow]
  have hq1 : ‖q‖ ≤ 1 := by
    rw [hqnorm]
    have h : ‖E‖ < 1 := by rw [hEdef]; exact Work.Residues.norm_Ept_lt_one τ
    nlinarith [norm_nonneg E]
  have hq0 : (0 : ℝ) ≤ ‖q‖ := norm_nonneg q
  -- the two inputs, rewritten in terms of `q`
  have hA' : ‖Work.Kernels.E4Fun τ ^ 3 - 1 - 720 * q‖ ≤ A * ‖q‖ ^ 2 := by
    rw [hqdef]; exact hAc τ h1
  have hs' : ‖(Work.Kernels.DeltaFun τ)⁻¹ - (q⁻¹ + 24)‖ ≤ Cs * ‖q‖ := by
    have h := hsc τ h1
    have hEq : (Work.Residues.Ept τ)⁻¹ ^ 2 = q⁻¹ := by rw [← hEdef]; exact hinv
    have hN : ‖Work.Residues.Ept τ‖ ^ 2 = ‖q‖ := by rw [hqnorm, hEdef]
    rw [hEq, hN] at h
    exact h
  set s : ℂ := (Work.Kernels.DeltaFun τ)⁻¹ - (q⁻¹ + 24) with hsdef
  have hs'' : ‖s‖ ≤ Cs * ‖q‖ := hs'
  set B : ℂ := Work.Kernels.E4Fun τ ^ 3 - 1 - 720 * q with hBdef
  have hB : ‖B‖ ≤ A * ‖q‖ ^ 2 := hA'
  have hsq : q * (Work.Kernels.DeltaFun τ)⁻¹ = 1 + 24 * q + s * q := by
    have h : (Work.Kernels.DeltaFun τ)⁻¹ = q⁻¹ + 24 + s := by rw [hsdef]; ring
    rw [h, mul_add, mul_add, mul_comm q q⁻¹, inv_mul_cancel₀ hqnz]
    ring
  have hj : Work.Kernels.jInvariantFun τ * q = (1 + 720 * q + B) * (1 + 24 * q + s * q) := by
    have hj1 : Work.Kernels.jInvariantFun τ = Work.Kernels.E4Fun τ ^ 3 * (Work.Kernels.DeltaFun τ)⁻¹ := by
      rw [Work.Kernels.jInvariantFun, div_eq_mul_inv]
    rw [hj1]
    calc Work.Kernels.E4Fun τ ^ 3 * (Work.Kernels.DeltaFun τ)⁻¹ * q
        = Work.Kernels.E4Fun τ ^ 3 * (q * (Work.Kernels.DeltaFun τ)⁻¹) := by ring
      _ = Work.Kernels.E4Fun τ ^ 3 * (1 + 24 * q + s * q) := by rw [hsq]
      _ = (1 + 720 * q + B) * (1 + 24 * q + s * q) := by rw [hBdef]; ring
  have hdecomp : Work.Kernels.jInvariantFun τ * q - 1 - 744 * q
      = s * q + 17280 * q ^ 2 + 720 * q * (s * q) + B + 24 * B * q + B * (s * q) := by
    rw [hj]
    ring
  have hsqb : ‖s * q‖ ≤ Cs * ‖q‖ ^ 2 := by
    rw [norm_mul]
    calc ‖s‖ * ‖q‖ ≤ (Cs * ‖q‖) * ‖q‖ := mul_le_mul_of_nonneg_right hs'' hq0
      _ = Cs * ‖q‖ ^ 2 := by ring
  have hq2b : ‖(17280 : ℂ) * q ^ 2‖ = 17280 * ‖q‖ ^ 2 := by
    rw [norm_mul, norm_pow, Complex.norm_ofNat]
  have hprod : ‖(720 : ℂ) * q * (s * q)‖ ≤ 720 * Cs * ‖q‖ ^ 2 := by
    rw [norm_mul, norm_mul, Complex.norm_ofNat]
    have h2 : ‖q‖ * ‖q‖ ^ 2 ≤ ‖q‖ ^ 2 := by
      nlinarith [hq0, hq1, sq_nonneg ‖q‖]
    calc 720 * ‖q‖ * ‖s * q‖ ≤ 720 * ‖q‖ * (Cs * ‖q‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hsqb (by positivity)
      _ = 720 * Cs * (‖q‖ * ‖q‖ ^ 2) := by ring
      _ ≤ 720 * Cs * ‖q‖ ^ 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
  have h24B : ‖(24 : ℂ) * B * q‖ ≤ 24 * A * ‖q‖ ^ 2 := by
    rw [norm_mul, norm_mul, Complex.norm_ofNat]
    have h2 : ‖B‖ * ‖q‖ ≤ (A * ‖q‖ ^ 2) * ‖q‖ := mul_le_mul_of_nonneg_right hB hq0
    have h3 : A * ‖q‖ ^ 2 * ‖q‖ ≤ A * ‖q‖ ^ 2 := by
      have : ‖q‖ ^ 2 * ‖q‖ ≤ ‖q‖ ^ 2 := by nlinarith [hq0, hq1, sq_nonneg ‖q‖]
      calc A * ‖q‖ ^ 2 * ‖q‖ = A * (‖q‖ ^ 2 * ‖q‖) := by ring
        _ ≤ A * ‖q‖ ^ 2 := mul_le_mul_of_nonneg_left this hA.le
    calc 24 * ‖B‖ * ‖q‖ = 24 * (‖B‖ * ‖q‖) := by ring
      _ ≤ 24 * (A * ‖q‖ ^ 2 * ‖q‖) := mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ ≤ 24 * (A * ‖q‖ ^ 2) := mul_le_mul_of_nonneg_left h3 (by norm_num)
      _ = 24 * A * ‖q‖ ^ 2 := by ring
  have hBsq : ‖B * (s * q)‖ ≤ A * Cs * ‖q‖ ^ 2 := by
    rw [norm_mul]
    have h2 : ‖B‖ * ‖s * q‖ ≤ (A * ‖q‖ ^ 2) * (Cs * ‖q‖ ^ 2) :=
      mul_le_mul hB hsqb (norm_nonneg _) (mul_nonneg hA.le (sq_nonneg _))
    refine le_trans h2 ?_
    have h3 : ‖q‖ ^ 2 * ‖q‖ ^ 2 ≤ ‖q‖ ^ 2 := by
      have h4 : ‖q‖ ^ 2 ≤ 1 := by nlinarith [hq0, hq1]
      nlinarith [h4, sq_nonneg (‖q‖ ^ 2)]
    calc A * ‖q‖ ^ 2 * (Cs * ‖q‖ ^ 2) = A * Cs * (‖q‖ ^ 2 * ‖q‖ ^ 2) := by ring
      _ ≤ A * Cs * ‖q‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_left h3 ?_
          exact mul_nonneg hA.le hCs.le
  rw [hdecomp]
  refine le_trans (norm_chain6 _ _ _ _ _ _) ?_
  linarith [hsqb, hq2b, hprod, hB, h24B, hBsq, sq_nonneg ‖q‖]

end

end Work.Asymptotics.KhatE1Core
