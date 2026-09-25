import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace Commons.Analysis.Fourier

/-- `⌊x⌋ = -1` iff `-1 ≤ x < 0`. -/
private lemma grid_cell_floor_eq_neg_one (x : ℝ) : ⌊x⌋ = -1 ↔ -1 ≤ x ∧ x < 0 := by
  rw [Int.floor_eq_iff]; norm_num

/-- The Lebesgue measure (as a real number) of a half-open interval. -/
private lemma grid_cell_volume_real_Ioc (a b : ℝ) :
    (MeasureTheory.volume (Set.Ioc a b)).toReal = max 0 (b - a) := by
  rw [Real.volume_Ioc]
  rcases le_or_gt (b - a) 0 with h | h
  · rw [ENNReal.ofReal_of_nonpos h, ENNReal.toReal_zero, max_eq_left h]
  · rw [ENNReal.toReal_ofReal h.le, max_eq_right h.le]

/-- Core computation: the average over the grid cell `(0, 1/N]` of the indicator that
`u` and `0` land in the same cell of the `1/N`-grid equals the triangular profile
`max 0 (L - |u|)` with `L = 1/N`. -/
private lemma grid_cell_integral (N L u : ℝ) (hN : 0 < N) (hL : 0 < L) (hLN : L * N = 1) :
    ∫ θ in (0:ℝ)..L,
        (if ⌊(u - θ) * N⌋ = ⌊((0:ℝ) - θ) * N⌋ then (1:ℝ) else 0)
      = max 0 (L - |u|) := by
  rw [intervalIntegral.integral_of_le hL.le]
  have hpt : ∀ θ ∈ Set.Ioc (0:ℝ) L,
      (if ⌊(u - θ) * N⌋ = ⌊((0:ℝ) - θ) * N⌋ then (1:ℝ) else 0)
        = (Set.Ioc u (u + L)).indicator (fun _ => (1:ℝ)) θ := by
    intro θ hθ
    rw [Set.mem_Ioc] at hθ
    obtain ⟨hθ0, hθL⟩ := hθ
    have hA : ⌊((0:ℝ) - θ) * N⌋ = -1 := by
      rw [grid_cell_floor_eq_neg_one]
      have h1 : (0:ℝ) < θ * N := mul_pos hθ0 hN
      have h2 : θ * N ≤ 1 := by
        have := mul_le_mul_of_nonneg_right hθL hN.le
        rwa [hLN] at this
      constructor <;> nlinarith [h1, h2]
    have hlt : (u - θ) * N < 0 ↔ u < θ := by
      have h := mul_lt_mul_iff_left₀ (a := N) (b := u - θ) (c := 0) hN
      rw [zero_mul] at h
      rw [h]; constructor <;> intro hh <;> linarith
    have hle : -1 ≤ (u - θ) * N ↔ θ ≤ u + L := by
      have e : (-L) * N = -1 := by rw [neg_mul, hLN]
      rw [← e, mul_le_mul_iff_left₀ (a := N) (b := -L) (c := u - θ) hN]
      constructor <;> intro hh <;> linarith
    have hB : ⌊(u - θ) * N⌋ = -1 ↔ θ ∈ Set.Ioc u (u + L) := by
      rw [grid_cell_floor_eq_neg_one, Set.mem_Ioc, hle, hlt]
      exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    rw [hA, Set.indicator_apply]
    simp only [hB]
  have heq : ∫ θ in Set.Ioc (0:ℝ) L,
        (if ⌊(u - θ) * N⌋ = ⌊((0:ℝ) - θ) * N⌋ then (1:ℝ) else 0)
      = ∫ θ in Set.Ioc (0:ℝ) L, (Set.Ioc u (u + L)).indicator (fun _ => (1:ℝ)) θ :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hpt
  rw [heq, MeasureTheory.setIntegral_indicator measurableSet_Ioc,
    MeasureTheory.setIntegral_const]
  rw [smul_eq_mul, mul_one]
  simp only [MeasureTheory.Measure.real_def]
  rw [Set.Ioc_inter_Ioc, grid_cell_volume_real_Ioc]
  have hminmax : min L (u + L) - max 0 u = L - |u| := by
    rcases le_or_gt 0 u with h | h
    · rw [abs_of_nonneg h, max_eq_right h, min_eq_left (by linarith)]
    · rw [abs_of_neg h, max_eq_left h.le, min_eq_right (by linarith)]
      ring
  rw [hminmax]

theorem grid_cell_average_eq_triangular (k : ℤ) (u : ℝ) :
    (1 / (2:ℝ) ^ (-k)) * ∫ θ in (0:ℝ)..(2:ℝ) ^ (-k),
        (if ⌊(u - θ) * 2 ^ k⌋ = ⌊((0:ℝ) - θ) * 2 ^ k⌋ then (1:ℝ) else 0)
      = max 0 (1 - 2 ^ k * |u|) := by
  have hN : (0:ℝ) < (2:ℝ) ^ k := zpow_pos (by norm_num) k
  have hL : (0:ℝ) < (2:ℝ) ^ (-k) := zpow_pos (by norm_num) (-k)
  have hLN : (2:ℝ) ^ (-k) * (2:ℝ) ^ k = 1 := by
    rw [zpow_neg]
    exact inv_mul_cancel₀ (zpow_ne_zero k (by norm_num))
  have hInt : ∫ θ in (0:ℝ)..(2:ℝ) ^ (-k),
        (if ⌊(u - θ) * 2 ^ k⌋ = ⌊((0:ℝ) - θ) * 2 ^ k⌋ then (1:ℝ) else 0)
      = max 0 ((2:ℝ) ^ (-k) - |u|) :=
    grid_cell_integral ((2:ℝ) ^ k) ((2:ℝ) ^ (-k)) u hN hL hLN
  rw [hInt]
  have hpow : (1:ℝ) / (2:ℝ) ^ (-k) = (2:ℝ) ^ k := by
    rw [one_div, zpow_neg, inv_inv]
  rw [hpow]
  have hmul : (2:ℝ) ^ k * (2:ℝ) ^ (-k) = 1 := by rw [mul_comm]; exact hLN
  rw [mul_max_of_nonneg (a := (2:ℝ) ^ k) 0 ((2:ℝ) ^ (-k) - |u|) hN.le, mul_zero]
  rw [show (2:ℝ) ^ k * ((2:ℝ) ^ (-k) - |u|) = 1 - (2:ℝ) ^ k * |u| by
    rw [mul_sub, hmul]]

end Commons.Analysis.Fourier