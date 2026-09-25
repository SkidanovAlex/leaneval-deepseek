import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Submission.Commons.Analysis.Fourier.grid_cell_average_eq_triangular

namespace Commons.Analysis.Fourier

open MeasureTheory

/-- The `{0,1}`-valued indicator of a measurable set is interval integrable. -/
private lemma intervalIntegrable_indicator_one (S : Set ℝ) (hS : MeasurableSet S) (a b : ℝ) :
    IntervalIntegrable (S.indicator (fun _ : ℝ => (1 : ℝ))) volume a b := by
  classical
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded ?_ ?_ (M := 1) ?_
  · rw [Real.volume_uIoc]; exact ENNReal.ofReal_ne_top
  · exact (measurable_const.indicator hS).aestronglyMeasurable
  · filter_upwards with v
    simp only [Set.indicator_apply]
    split_ifs <;> simp

theorem grid_shift_kernel_eq_triangular (K k : ℤ) (hKk : K ≤ k) (x y : ℝ) :
    (1 / (2:ℝ)^(-K)) * ∫ θ in (0:ℝ)..((2:ℝ)^(-K)),
      (if ⌊(y - θ) * (2:ℝ)^k⌋ = ⌊(x - θ) * (2:ℝ)^k⌋ then (1:ℝ) else 0)
    = max 0 (1 - (2:ℝ)^k * |x - y|) := by
  classical
  set T : ℝ := (2:ℝ)^(-k) with hTdef
  set N : ℝ := (2:ℝ)^k with hNdef
  set M : ℝ := (2:ℝ)^(-K) with hMdef
  have hT : 0 < T := by rw [hTdef]; exact zpow_pos (by norm_num) (-k)
  have hN : 0 < N := by rw [hNdef]; exact zpow_pos (by norm_num) k
  have hM : 0 < M := by rw [hMdef]; exact zpow_pos (by norm_num) (-K)
  have hTne : T ≠ 0 := ne_of_gt hT
  have hMne : M ≠ 0 := ne_of_gt hM
  have hTN : T * N = 1 := by
    rw [hTdef, hNdef, ← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
    rw [show (-k) + k = 0 by ring, zpow_zero]
  set S : Set ℝ := {v : ℝ | ⌊(y - x - v) * N⌋ = ⌊((0:ℝ) - v) * N⌋} with hSdef
  set f : ℝ → ℝ := fun v => if ⌊(y - x - v) * N⌋ = ⌊((0:ℝ) - v) * N⌋ then (1:ℝ) else 0 with hfdef
  have hSmeas : MeasurableSet S := by
    rw [hSdef]
    exact measurableSet_eq_fun (Measurable.floor (by fun_prop)) (Measurable.floor (by fun_prop))
  have hfS : f = S.indicator (fun _ : ℝ => (1:ℝ)) := by
    funext v
    simp only [hfdef, hSdef, Set.indicator_apply, Set.mem_ofPred_eq]
  have hint : ∀ t₁ t₂ : ℝ, IntervalIntegrable f volume t₁ t₂ := by
    intro t₁ t₂
    rw [hfS]
    exact intervalIntegrable_indicator_one S hSmeas t₁ t₂
  have hper : Function.Periodic f T := by
    intro v
    simp only [hfdef]
    have ha : (y - x - (v + T)) * N = (y - x - v) * N - 1 := by
      calc (y - x - (v + T)) * N = (y - x - v) * N - T * N := by ring
        _ = (y - x - v) * N - 1 := by rw [hTN]
    have hb : ((0:ℝ) - (v + T)) * N = ((0:ℝ) - v) * N - 1 := by
      calc ((0:ℝ) - (v + T)) * N = ((0:ℝ) - v) * N - T * N := by ring
        _ = ((0:ℝ) - v) * N - 1 := by rw [hTN]
    rw [ha, hb, Int.floor_sub_one, Int.floor_sub_one]
    by_cases h : (⌊(y - x - v) * N⌋ = ⌊((0:ℝ) - v) * N⌋)
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]
  have hgf : ∀ θ : ℝ,
      (if ⌊(y - θ) * N⌋ = ⌊(x - θ) * N⌋ then (1:ℝ) else 0) = f (θ - x) := by
    intro θ
    simp only [hfdef]
    rw [show y - x - (θ - x) = y - θ by ring,
        show ((0:ℝ) - (θ - x)) = x - θ by ring]
  set m : ℕ := (k - K).toNat with hmdef
  set n : ℤ := (2:ℤ)^m with hndef
  have hmcast : (m : ℤ) = k - K := by
    rw [hmdef]; exact Int.toNat_of_nonneg (by omega)
  have hnR : (n : ℝ) = (2:ℝ)^(k - K) := by
    rw [hndef, Int.cast_pow]
    push_cast
    rw [← zpow_natCast, hmcast]
  have hnT : (n : ℝ) * T = M := by
    rw [hnR, hTdef, hMdef, ← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
    rw [show (k - K) + (-k) = -K by ring]
  have hshift : ∫ θ in (0:ℝ)..M,
        (if ⌊(y - θ) * N⌋ = ⌊(x - θ) * N⌋ then (1:ℝ) else 0)
      = ∫ v in (-x)..(M - x), f v := by
    simp only [hgf]
    rw [show (∫ θ in (0:ℝ)..M, f (θ - x)) = ∫ θ in (0:ℝ)..M, f (θ + (-x)) by
          simp only [sub_eq_add_neg]]
    rw [intervalIntegral.integral_comp_add_right f (-x)]
    simp only [zero_add, sub_eq_add_neg]
  have hmain : ∫ θ in (0:ℝ)..M,
        (if ⌊(y - θ) * N⌋ = ⌊(x - θ) * N⌋ then (1:ℝ) else 0)
      = (n : ℝ) * (∫ v in (0:ℝ)..T, f v) := by
    rw [hshift]
    have hz := hper.intervalIntegral_add_zsmul_eq n (-x) hint
    have hx : (-x) + n • T = M - x := by
      rw [zsmul_eq_mul, hnT]; ring
    rw [← hx, hz, hper.intervalIntegral_add_eq (-x) 0, zsmul_eq_mul, zero_add]
  have hgc : (1 / T) * (∫ v in (0:ℝ)..T, f v) = max 0 (1 - N * |y - x|) := by
    rw [hTdef, hNdef]
    simpa only [hfdef] using grid_cell_average_eq_triangular k (y - x)
  have hIntT : ∫ v in (0:ℝ)..T, f v = T * max 0 (1 - N * |y - x|) := by
    rw [← hgc, ← mul_assoc, mul_one_div, div_self hTne, one_mul]
  rw [hmain, hIntT]
  rw [show (n : ℝ) * (T * max 0 (1 - N * |y - x|)) = M * max 0 (1 - N * |y - x|) by
        rw [← mul_assoc, hnT]]
  rw [abs_sub_comm y x, one_div, ← mul_assoc, inv_mul_cancel₀ hMne, one_mul]

end Commons.Analysis.Fourier