import Mathlib
import Submission.Work.BMF.halasz_plancherel_defs
import Submission.Work.BMF.cauchy_fourier_aux
import Submission.Work.BMF.dirSum_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `L²` computation for the truncated Dirichlet series

This file evaluates

`(1/2π) ∫_τ ‖dirSum f α N τ‖² / ‖(1+α) + i τ‖² dτ`

in closed form, namely as `(1/(2+2α)) * UN f α N`.  The evaluation uses the classical
Cauchy/Lorentzian Fourier transform pair (`Work.BMF.cauchy_fourier_integral`).
-/

open Complex MeasureTheory Real Finset

set_option maxHeartbeats 1000000

namespace Work.BMF

theorem integral_dirSum_sq (f : ℕ → ℂ) (α : ℝ) (hα : 0 < α) (N : ℕ) :
    (1 / (2 * Real.pi)) *
        (∫ τ : ℝ, ‖dirSum f α N τ‖ ^ 2 / ‖((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I‖ ^ 2)
      = (1 / (2 + 2 * α)) * UN f α N := by
  have hβ : 0 < 1 + α := by linarith
  have hden : ∀ τ : ℝ,
      ‖((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I‖ ^ 2 = (1+α)^2 + τ^2 := by
    intro τ
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp
    ring
  have hpt : ∀ τ : ℝ,
      ‖dirSum f α N τ‖ ^ 2 / ‖((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I‖ ^ 2
      = ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
          (cz f α m * starRingEnd ℂ (cz f α n)
            * Complex.exp (((-(Real.log m - Real.log n) * τ : ℝ) : ℂ) * Complex.I)).re
          * (((1+α)^2 + τ^2)⁻¹) := by
    intro τ
    rw [hden τ, dirSum_normSq, div_eq_mul_inv, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_mul]
  have hIntK : Integrable (fun τ : ℝ => (((1+α)^2 + τ^2)⁻¹ : ℝ)) := by
    have h := (integrable_inv_one_add_mul_sq (b := 1/(1+α)) (by positivity)).const_mul (1/(1+α)^2)
    refine h.congr (Filter.Eventually.of_forall (fun τ => ?_))
    field_simp
  have hInt_term : ∀ m n : ℕ, Integrable (fun τ : ℝ =>
      (cz f α m * starRingEnd ℂ (cz f α n)
        * Complex.exp (((-(Real.log m - Real.log n) * τ : ℝ) : ℂ) * Complex.I)).re
      * (((1+α)^2 + τ^2)⁻¹)) := by
    intro m n
    refine Integrable.mono' (hIntK.const_mul ‖cz f α m * starRingEnd ℂ (cz f α n)‖) ?_ ?_
    · fun_prop
    · filter_upwards with τ
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ ((1+α)^2+τ^2)⁻¹)]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      calc |(cz f α m * starRingEnd ℂ (cz f α n)
            * Complex.exp (((-(Real.log m - Real.log n) * τ : ℝ) : ℂ) * Complex.I)).re|
          ≤ ‖cz f α m * starRingEnd ℂ (cz f α n)
            * Complex.exp (((-(Real.log m - Real.log n) * τ : ℝ) : ℂ) * Complex.I)‖ :=
            Complex.abs_re_le_norm _
        _ = ‖cz f α m * starRingEnd ℂ (cz f α n)‖
              * ‖Complex.exp (((-(Real.log m - Real.log n) * τ : ℝ) : ℂ) * Complex.I)‖ :=
            norm_mul _ _
        _ = ‖cz f α m * starRingEnd ℂ (cz f α n)‖ := by
            rw [Complex.norm_exp]
            have hz : (((-(Real.log m - Real.log n) * τ : ℝ) : ℂ) * Complex.I).re = 0 := by
              rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
              ring
            rw [hz]
            simp
  have hInt : (∫ τ : ℝ, ‖dirSum f α N τ‖ ^ 2 / ‖((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I‖ ^ 2)
      = ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
          (cz f α m * starRingEnd ℂ (cz f α n)).re
            * ((Real.pi/(1+α)) * Real.exp (-((1+α) * |Real.log m - Real.log n|))) := by
    simp_rw [hpt]
    rw [integral_finsetSum (Icc 1 N)
      (fun m _ => integrable_finsetSum _ (fun n _ => hInt_term m n))]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [integral_finsetSum (Icc 1 N) (fun n _ => hInt_term m n)]
    refine Finset.sum_congr rfl fun n _ => ?_
    exact integral_exp_mul_cauchy (1+α) (Real.log m - Real.log n) hβ _
  rw [hInt]
  have hfold : (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        (cz f α m * starRingEnd ℂ (cz f α n)).re
          * (Real.pi/(1+α) * Real.exp (-((1+α) * |Real.log m - Real.log n|))))
      = (Real.pi/(1+α)) * (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        (cz f α m * starRingEnd ℂ (cz f α n)).re
          * Real.exp (-((1+α) * |Real.log m - Real.log n|))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [hfold]
  have hsum : (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        (cz f α m * starRingEnd ℂ (cz f α n)).re
          * Real.exp (-((1+α) * |Real.log m - Real.log n|)))
      = ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        ((f m * (Real.log m : ℂ)) * starRingEnd ℂ (f n * (Real.log n : ℂ))).re
          * (((max m n : ℕ) : ℝ) ^ (-(2 + 2 * α))) := by
    refine Finset.sum_congr rfl fun m hm => ?_
    refine Finset.sum_congr rfl fun n hn => ?_
    exact summand_eq f α (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hn).1
  rw [hsum, UN, ← mul_assoc,
      show (1/(2*Real.pi)) * (Real.pi/(1+α)) = 1/(2+2*α) by
        have h1 : (1:ℝ) + α ≠ 0 := by linarith
        field_simp]

end Work.BMF
