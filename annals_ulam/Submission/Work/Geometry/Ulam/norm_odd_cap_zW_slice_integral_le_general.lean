import Mathlib

namespace Commons.Geometry.Ulam

open MeasureTheory Set Filter
open scoped Topology Interval ContDiff RealInnerProductSpace BigOperators

set_option autoImplicit false

lemma norm_odd_cap_zW_slice_integral_le_general {n : ℕ} {f h : ℝ → ℝ} {M A B : ℝ} (hAB : A < B)
    (hf_le_M : ∀ t ∈ Set.Icc A B, f t ≤ M)
    (hf_nonneg : ∀ t ∈ Set.Icc A B, 0 ≤ f t)
    (hM_nonneg : 0 ≤ M) :
    ∀ r : ℝ, ∀ᵐ t ∂volume, t ∈ Ι A B →
      ‖(∫ z in (-f t)..(max (-f t) (min (f t) (r * t + h r))),
          z * ((f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2)))‖ ≤
        M * (2 * M) * ((M ^ 2) ^ (n - 1) * M) := by
  intro r
  filter_upwards [] with t ht
  have htIoc : t ∈ Set.Ioc A B := by
    simpa [Set.uIoc_of_le (hAB.le)] using ht
  have htcc : t ∈ Set.Icc A B := Set.Ioc_subset_Icc_self htIoc
  have hft_nonneg : 0 ≤ f t := hf_nonneg t htcc
  have hft_le : f t ≤ M := hf_le_M t htcc
  let a : ℝ := -f t
  let b : ℝ := f t
  let U : ℝ := max a (min b (r * t + h r))
  let g : ℝ → ℝ := fun z => z * ((f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2))
  have ha_le_b : a ≤ b := by dsimp [a, b]; linarith
  have hU_mem : U ∈ Set.Icc a b := by
    dsimp [U]
    rw [Set.mem_Icc]
    constructor
    · exact le_max_left _ _
    · exact max_le ha_le_b (min_le_left _ _)
  have hUa : a ≤ U := hU_mem.1
  have hUb : U ≤ b := hU_mem.2
  have hg_bound : ∀ z ∈ Ι a U, ‖g z‖ ≤ M * ((M ^ 2) ^ (n - 1) * M) := by
    intro z hz
    have hzIoc : z ∈ Set.Ioc a U := by
      simpa [Set.uIoc_of_le hUa] using hz
    have hz_lower : -M ≤ z := by
      have ha_lower : -M ≤ a := by dsimp [a]; linarith
      exact le_trans ha_lower (le_of_lt hzIoc.1)
    have hz_upper : z ≤ M := by
      have hb_upper : b ≤ M := by dsimp [b]; exact hft_le
      exact le_trans (le_trans hzIoc.2 hUb) hb_upper
    have hz_abs : |z| ≤ M := abs_le.mpr ⟨hz_lower, hz_upper⟩
    have hG_nonneg : 0 ≤ f t ^ 2 - z ^ 2 := by
      have hz_le_f : z ≤ f t := le_trans hzIoc.2 hUb
      have hz_ge_negf : -f t ≤ z := le_of_lt hzIoc.1
      have h1 : 0 ≤ f t - z := sub_nonneg.mpr hz_le_f
      have h2 : 0 ≤ f t + z := by linarith
      nlinarith [mul_nonneg h1 h2]
    have hG_le : f t ^ 2 - z ^ 2 ≤ M ^ 2 := by
      have hftsq : f t ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hft_nonneg hft_le 2
      nlinarith [sq_nonneg z]
    have hpow : |(f t ^ 2 - z ^ 2) ^ (n - 1)| ≤ (M ^ 2) ^ (n - 1) := by
      rw [abs_pow, abs_of_nonneg hG_nonneg]
      exact pow_le_pow_left₀ hG_nonneg hG_le (n - 1)
    have hsqrt : |Real.sqrt (f t ^ 2 - z ^ 2)| ≤ M := by
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      exact (Real.sqrt_le_left hM_nonneg).2 hG_le
    have hW_le : |((f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2))| ≤
        (M ^ 2) ^ (n - 1) * M := by
      simpa [abs_mul] using mul_le_mul hpow hsqrt (abs_nonneg _) (by positivity)
    dsimp [g]
    simpa [abs_mul] using mul_le_mul hz_abs hW_le (abs_nonneg _) (by positivity)
  have hlen : |U - a| ≤ 2 * M := by
    rw [abs_of_nonneg (sub_nonneg.mpr hUa)]
    calc U - a ≤ b - a := sub_le_sub hUb le_rfl
      _ = 2 * f t := by dsimp [a, b]; ring
      _ ≤ 2 * M := mul_le_mul_of_nonneg_left hft_le (by norm_num)
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := U)
      (C := M * ((M ^ 2) ^ (n - 1) * M)) (f := g) hg_bound
  calc
    ‖∫ z in (-f t)..(max (-f t) (min (f t) (r * t + h r))),
        z * ((f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2))‖
        = ‖∫ z in a..U, g z‖ := by simp [a, b, U, g]
    _ ≤ (M * ((M ^ 2) ^ (n - 1) * M)) * |U - a| := hnorm
    _ ≤ (M * ((M ^ 2) ^ (n - 1) * M)) * (2 * M) := by
        exact mul_le_mul_of_nonneg_left hlen (by positivity)
    _ = M * (2 * M) * ((M ^ 2) ^ (n - 1) * M) := by ring


end Commons.Geometry.Ulam
