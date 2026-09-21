import Mathlib
import Submission.Work.OddVolterra.Kernel.Diag
import Submission.Work.OddVolterra.Kernel.G2Deriv
import Submission.Work.OddVolterra.Existence.Theta_integrand_intervalIntegrable
import Submission.Work.OddVolterra.Existence.deriv_G2_apply_eq_integral
import Submission.Work.OddVolterra.Existence.continuousOn_integral_deriv_G2_apply

namespace Work.OddVolterra.Existence

open MeasureTheory Set Filter intervalIntegral
open scoped Topology ContDiff Interval

/-- The Abel weight integrates to `π` on `(0,1)`: `∫₀¹ (√(τ(1-τ)))⁻¹ dτ = π`.

This is the value of `∫_{-1}^{1} (√(1-x²))⁻¹ dx = π` (`integral_eval_T_real_measureT_zero`)
after the affine substitution `x = 2τ - 1`. -/
theorem abel_weight_integral :
    ∫ τ in (0:ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ = Real.pi := by
  have hbase : ∫ x in (-1:ℝ)..1, (Real.sqrt (1 - x ^ 2))⁻¹ = Real.pi := by
    have h1 : ∫ x, (Polynomial.eval x (Polynomial.Chebyshev.T ℝ 0))
        ∂Polynomial.Chebyshev.measureT = Real.pi :=
      Polynomial.Chebyshev.integral_eval_T_real_measureT_zero
    have h2 : ∫ x, (1:ℝ) ∂Polynomial.Chebyshev.measureT = Real.pi := by simpa using h1
    rw [Polynomial.Chebyshev.integral_measureT] at h2
    simpa using h2
  have hcomp := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0:ℝ)) (b := 1) (f := fun τ : ℝ => 2 * τ - 1) (f' := fun _ => (2:ℝ))
    (g := fun x : ℝ => (Real.sqrt (1 - x ^ 2))⁻¹)
    (by fun_prop)
    (fun x _ => by simpa using (hasDerivAt_id x).const_mul 2 |>.sub_const 1)
    (fun x _ => by norm_num)
  rw [show (2:ℝ) * 0 - 1 = (-1:ℝ) by norm_num,
      show (2:ℝ) * 1 - 1 = (1:ℝ) by norm_num, hbase] at hcomp
  rw [← hcomp]
  refine intervalIntegral.integral_congr (fun τ hτ => ?_)
  rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1), Set.mem_Icc] at hτ
  simp only [Function.comp_apply]
  have h1 : 1 - (2 * τ - 1) ^ 2 = 4 * (τ * (1 - τ)) := by ring
  have hnn : 0 ≤ τ * (1 - τ) := by nlinarith [hτ.1, hτ.2]
  rw [h1, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4), show Real.sqrt (4:ℝ) = 2 by norm_num]
  field_simp

theorem continuousOn_deriv_G2_apply (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) {Z : ℝ → Work.OddVolterra.St}
    (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z (Set.Ioi (0:ℝ)))
    {s : ℝ} (hs : s ∈ Set.Ioo (0:ℝ) 1) (i : Fin 2)
    {δ Cm : ℝ} (hδ : 0 < δ) (hCm : 0 < Cm)
    (hpos : ∀ σ ∈ Set.Icc s 1, ∀ a ∈ Set.Icc (s - δ) σ,
      0 < Work.OddVolterra.krad h σ (-(Z σ 0)) a ∧
        0 < Work.OddVolterra.krad h σ (Z σ 1) a)
    (hbdK : ∀ σ ∈ Set.Icc s 1, ∀ a ∈ Set.Ico (s - δ) σ,
      ‖Work.OddVolterra.Kvec n h a σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)‖ ≤ Cm)
    (hbdD : ∀ σ ∈ Set.Icc s 1, ∀ a ∈ Set.Ico (s - δ) σ,
      ‖deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) a‖ ≤ Cm) :
    ContinuousOn (fun σ : ℝ =>
        deriv (fun u : ℝ => (Work.OddVolterra.G2 n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) i) s)
      (Set.Ioo s 1) ∧
    (∀ σ ∈ Set.Ioo s 1,
      deriv (fun u : ℝ => (Work.OddVolterra.G2 n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) i) s =
        ∫ τ in (0:ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ *
          ((1 - τ) * ((deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) (s + τ * (σ - s))) i))) ∧
    (∀ σ ∈ Set.Ioo s 1,
      ‖deriv (fun u : ℝ => (Work.OddVolterra.G2 n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) i) s‖
        ≤ Cm * Real.pi) := by
  have hderiv : ∀ σ ∈ Set.Ioo s 1,
      deriv (fun u : ℝ => (Work.OddVolterra.G2 n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) i) s =
        ∫ τ in (0:ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ *
          ((1 - τ) * ((deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) (s + τ * (σ - s))) i)) :=
    fun σ hσ => deriv_G2_apply_eq_integral n hn hh hZ hs i hδ hCm hpos hbdK hbdD hσ
  refine ⟨?_, hderiv, ?_⟩
  · refine (continuousOn_integral_deriv_G2_apply n hn hh hZ hs i hδ hCm hpos hbdK hbdD).congr ?_
    intro σ hσ
    exact hderiv σ hσ
  · intro σ hσ
    rw [hderiv σ hσ]
    have hσI : σ ∈ Set.Icc s 1 := ⟨le_of_lt hσ.1, le_of_lt hσ.2⟩
    have hbdd : ∀ᵐ τ ∂(volume : Measure ℝ), τ ∈ Set.Ioc (0:ℝ) 1 →
        ‖(Real.sqrt (τ * (1 - τ)))⁻¹ *
        ((1 - τ) * ((deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) (s + τ * (σ - s))) i))‖
        ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * Cm := by
      filter_upwards with τ hτ
      rw [Set.mem_Ioc] at hτ
      by_cases h1 : τ = 1
      · subst h1
        norm_num
      · have hτlt : τ < 1 := lt_of_le_of_ne hτ.2 h1
        have hτ0 : 0 < τ := hτ.1
        have hspos : 0 < σ - s := sub_pos.mpr hσ.1
        have ha_mem : s + τ * (σ - s) ∈ Set.Ico (s - δ) σ := by
          refine ⟨?_, ?_⟩
          · nlinarith [hδ, hτ0, hspos, mul_pos hτ0 hspos]
          · nlinarith [hτlt, hspos]
        have hD := hbdD σ hσI _ ha_mem
        have hCm0 : 0 ≤ Cm := le_trans (norm_nonneg _) hD
        have hwpos : 0 ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
        have h1t : 0 ≤ 1 - τ := by linarith
        have hcomp : ‖((deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) (s + τ * (σ - s))) i)‖ ≤ Cm :=
          le_trans (norm_le_pi_norm _ _) hD
        rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg hwpos, abs_of_nonneg h1t]
        refine mul_le_mul_of_nonneg_left ?_ hwpos
        calc (1 - τ) * ‖((deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) (s + τ * (σ - s))) i)‖
            ≤ (1 - τ) * Cm := mul_le_mul_of_nonneg_left hcomp h1t
          _ ≤ 1 * Cm := mul_le_mul_of_nonneg_right (by linarith) hCm0
          _ = Cm := one_mul Cm
    calc ‖∫ τ in (0:ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ *
        ((1 - τ) * ((deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) (s + τ * (σ - s))) i))‖
        ≤ ∫ τ in (0:ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ * Cm :=
          intervalIntegral.norm_integral_le_of_norm_le (by norm_num) hbdd
            (Commons.Geometry.Ulam.intervalIntegrable_abel_weight.mul_const Cm)
      _ = Cm * Real.pi := by
          rw [intervalIntegral.integral_mul_const, abel_weight_integral]; ring

end Work.OddVolterra.Existence
