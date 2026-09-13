import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace Commons.Analysis.Calculus.Taylor

open MeasureTheory intervalIntegral
open scoped Topology

theorem abs_taylor_remainder_three_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ} {B θ : ℝ} (hB : 0 ≤ B)
    (hF : ∀ y : E, ‖y‖ ≤ θ → ContDiffAt ℝ 3 F y)
    (h3 : ∀ y : E, ‖y‖ ≤ θ → ‖iteratedFDeriv ℝ 3 F y‖ ≤ B)
    {x : E} (hx : ‖x‖ ≤ θ) :
    |F x - F 0 - (fderiv ℝ F 0) x - (1 / 2 : ℝ) * (fderiv ℝ (fderiv ℝ F) 0) x x| ≤ B * θ ^ 3 := by
  have hθ0 : 0 ≤ θ := le_trans (norm_nonneg x) hx
  -- `F` is `C³` along the segment from `0` to `x`.
  have htc : ∀ t ∈ Set.Icc (0:ℝ) 1, ContDiffAt ℝ 3 F ((0:E) + t • x) := by
    intro t ht
    have hnorm : ‖(0:E) + t • x‖ ≤ θ := by
      rw [zero_add, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      calc t * ‖x‖ ≤ 1 * θ := mul_le_mul ht.2 hx (norm_nonneg x) (by norm_num)
        _ = θ := by ring
    exact hF _ hnorm
  -- Taylor's formula with integral remainder, expanded to order `2` at `0`.
  have hTaylor := map_add_eq_sum_add_integral_iteratedFDeriv (f := F) (x := (0:E)) (y := x)
    (n := 2) htc
  simp only [zero_add] at hTaylor
  -- The finite Taylor sum is `F 0 + DF(0)·x + 1/2 D²F(0)(x,x)`.
  have h0 : ((0:ℕ).factorial : ℝ)⁻¹ • (iteratedFDeriv ℝ 0 F 0 (fun _ : Fin 0 => x)) = F 0 := by
    simp
  have h1 : ((1:ℕ).factorial : ℝ)⁻¹ • (iteratedFDeriv ℝ 1 F 0 (fun _ : Fin 1 => x))
      = (fderiv ℝ F 0) x := by simp
  have h2 : ((2:ℕ).factorial : ℝ)⁻¹ • (iteratedFDeriv ℝ 2 F 0 (fun _ : Fin 2 => x))
      = (1/2:ℝ) * (fderiv ℝ (fderiv ℝ F) 0) x x := by
    rw [iteratedFDeriv_two_apply]
    norm_num [Nat.factorial]
  have hsum : (∑ k ∈ Finset.range 3, (k.factorial : ℝ)⁻¹ •
        (iteratedFDeriv ℝ k F 0 (fun _ : Fin k => x)))
      = F 0 + (fderiv ℝ F 0) x + (1/2:ℝ) * (fderiv ℝ (fderiv ℝ F) 0) x x := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, h0, h1, h2]
  rw [hsum] at hTaylor
  -- Name the remainder integral.
  set I : ℝ := ∫ (t:ℝ) in (0:ℝ)..1,
      (1-t)^2 • (iteratedFDeriv ℝ 3 F (t • x)) (fun _ : Fin 3 => x) with hIdef
  have hIeq : ((2:ℕ).factorial : ℝ)⁻¹ •
        (∫ (t:ℝ) in (0:ℝ)..1, (1-t)^2 • (iteratedFDeriv ℝ 3 F (t • x)) (fun _ : Fin 3 => x))
      = (1/2:ℝ) * I := by
    rw [hIdef]
    have hfac : ((2:ℕ).factorial : ℝ)⁻¹ = 1/2 := by norm_num [Nat.factorial]
    rw [hfac, smul_eq_mul]
  have hkey : F x - F 0 - (fderiv ℝ F 0) x - (1/2:ℝ) * (fderiv ℝ (fderiv ℝ F) 0) x x
      = (1/2:ℝ) * I := by
    rw [hTaylor, hIeq]
    ring
  rw [hkey]
  -- Bound the integral.
  have hIbound : |I| ≤ B * ‖x‖ ^ 3 := by
    rw [hIdef]
    have hbound : ∀ t ∈ Set.uIoc (0:ℝ) 1,
        ‖(1-t)^2 • (iteratedFDeriv ℝ 3 F (t • x)) (fun _ : Fin 3 => x)‖ ≤ B * ‖x‖^3 := by
      intro t ht
      rw [Set.uIoc_of_le zero_le_one, Set.mem_Ioc] at ht
      obtain ⟨ht0, ht1⟩ := ht
      have hnorm : ‖t • x‖ ≤ θ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
        calc t * ‖x‖ ≤ 1 * θ := mul_le_mul ht1 hx (norm_nonneg x) (by norm_num)
          _ = θ := by ring
      have hMB : ‖(iteratedFDeriv ℝ 3 F (t • x)) (fun _ : Fin 3 => x)‖ ≤ B * ‖x‖^3 := by
        calc ‖(iteratedFDeriv ℝ 3 F (t • x)) (fun _ : Fin 3 => x)‖
            ≤ ‖iteratedFDeriv ℝ 3 F (t • x)‖ * ∏ i : Fin 3, ‖(fun _ : Fin 3 => x) i‖ :=
              ContinuousMultilinearMap.le_opNorm _ _
          _ = ‖iteratedFDeriv ℝ 3 F (t • x)‖ * ‖x‖^3 := by
              simp [Finset.prod_const]
          _ ≤ B * ‖x‖^3 := mul_le_mul_of_nonneg_right (h3 _ hnorm) (by positivity)
      have h1t : ‖(1-t)^2‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [ht0, ht1]
      rw [norm_smul]
      calc ‖(1-t)^2‖ * ‖(iteratedFDeriv ℝ 3 F (t • x)) (fun _ : Fin 3 => x)‖
          ≤ 1 * (B * ‖x‖^3) := mul_le_mul h1t hMB (norm_nonneg _) (by norm_num)
        _ = B * ‖x‖^3 := by ring
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1) hbound
    rw [Real.norm_eq_abs] at h
    simpa using h
  -- Final triangle-type estimate.
  have hx3 : ‖x‖^3 ≤ θ^3 := pow_le_pow_left₀ (norm_nonneg x) hx 3
  have hBθ : 0 ≤ B * θ^3 := mul_nonneg hB (pow_nonneg hθ0 3)
  calc |(1/2:ℝ) * I| = (1/2) * |I| := by rw [abs_mul]; norm_num
    _ ≤ (1/2) * (B * ‖x‖^3) := mul_le_mul_of_nonneg_left hIbound (by norm_num)
    _ ≤ B * θ^3 := by nlinarith [mul_le_mul_of_nonneg_left hx3 hB]

end Commons.Analysis.Calculus.Taylor
