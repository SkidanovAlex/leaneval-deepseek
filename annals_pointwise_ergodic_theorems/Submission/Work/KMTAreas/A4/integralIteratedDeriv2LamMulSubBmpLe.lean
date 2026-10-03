import Mathlib
import Submission.Work.KMTAreas.A4.offPieceMid

namespace Work.KMTAreas.A4

open MeasureTheory
open scoped ENNReal

theorem integralIteratedDeriv2LamMulSubBmpLe (N : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ (k jj : ℤ), k ≤ 0 → 0 ≤ jj → 0 ≤ k + jj → ∫⁻ x : ℝ, ‖iteratedDeriv 2 (Work.KMTAreas.A4.lam k) x * (1 - Work.KMTAreas.A4.bmp jj x)‖ₑ ≤ ENNReal.ofReal (C * (2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))) := by
  obtain ⟨C', hC'pos, hC'⟩ := offLamTail 2 N
  refine ⟨C', hC'pos, ?_⟩
  intro k jj hk hjj hkj
  set R : ℝ := (2 : ℝ) ^ (jj - 1) with hR
  set S : Set ℝ := {x : ℝ | R ≤ |x|} with hS
  have hRpos : 0 < R := by rw [hR]; exact zpow_pos (by norm_num) (jj - 1)
  have hSmeas : MeasurableSet S := by
    rw [hS]
    exact measurableSet_le measurable_const continuous_abs.measurable
  have hkR : (2 : ℝ) ^ k * R = (2 : ℝ) ^ (k + jj - 1) := by
    rw [hR, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    ring
  -- pointwise domination by the tail indicator
  have hpoint : ∀ x : ℝ,
      ‖iteratedDeriv 2 (lam k) x * (1 - (bmp jj) x)‖ₑ
        ≤ S.indicator (fun x : ℝ => ‖iteratedDeriv 2 (lam k) x‖ₑ) x := by
    intro x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, enorm_mul]
      have hb : ‖(1 : ℂ) - (bmp jj) x‖ₑ ≤ 1 := by
        rw [enorm_complex_eq_ofReal_norm, ENNReal.ofReal_le_one]
        exact norm_one_sub_bmp_le jj x
      calc ‖iteratedDeriv 2 (lam k) x‖ₑ * ‖(1 : ℂ) - (bmp jj) x‖ₑ
          ≤ ‖iteratedDeriv 2 (lam k) x‖ₑ * 1 := mul_le_mul_of_nonneg_left hb (by positivity)
        _ = ‖iteratedDeriv 2 (lam k) x‖ₑ := mul_one _
    · rw [Set.indicator_of_notMem hx]
      have hlt : |x| < (2 : ℝ) ^ (jj - 1) := by
        rw [hS] at hx
        rw [hR] at hx
        exact lt_of_not_ge hx
      have hb1 : (bmp jj) x = 1 := bmp_one_of_le jj (le_of_lt hlt)
      rw [hb1, sub_self, mul_zero, enorm_zero]
  have hle : ∫⁻ x : ℝ, ‖iteratedDeriv 2 (lam k) x * (1 - (bmp jj) x)‖ₑ
      ≤ ∫⁻ x : ℝ in S, ‖iteratedDeriv 2 (lam k) x‖ₑ := by
    calc ∫⁻ x : ℝ, ‖iteratedDeriv 2 (lam k) x * (1 - (bmp jj) x)‖ₑ
        ≤ ∫⁻ x : ℝ, S.indicator (fun x : ℝ => ‖iteratedDeriv 2 (lam k) x‖ₑ) x :=
          lintegral_mono hpoint
      _ = ∫⁻ x : ℝ in S, ‖iteratedDeriv 2 (lam k) x‖ₑ :=
          lintegral_indicator hSmeas _
  have hfun : (fun x : ℝ => ‖iteratedDeriv 2 (lam k) x‖ₑ)
      = fun x : ℝ => ‖iteratedDeriv 2
          ((Work.KMTAreas.A7.etaMult_K k : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖ₑ := by
    funext x
    rw [lam_eq_etaMult_K]
  have htail : ∫⁻ x : ℝ in S, ‖iteratedDeriv 2 (lam k) x‖ₑ
      ≤ ENNReal.ofReal (C' * (((2 : ℝ) ^ k) ^ 2)
          * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))) := by
    have h := hC' k R hRpos.le
    rw [hfun]
    simpa [hS, hkR] using h
  refine hle.trans (htail.trans ?_)
  apply ENNReal.ofReal_le_ofReal
  have h2k : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
  have h2k1 : (2 : ℝ) ^ k ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hk
  have hM : (0 : ℝ) ≤ (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)) :=
    Real.rpow_nonneg (le_trans zero_le_one (le_max_right _ 1)) _
  have hsq : ((2 : ℝ) ^ k) ^ 2 ≤ (2 : ℝ) ^ k := by
    rw [sq]
    simpa using mul_le_mul_of_nonneg_right h2k1 h2k.le
  have h1 : C' * ((2 : ℝ) ^ k) ^ 2 * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))
      ≤ C' * (2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)) := by
    have h2 : C' * ((2 : ℝ) ^ k) ^ 2 ≤ C' * (2 : ℝ) ^ k :=
      mul_le_mul_of_nonneg_left hsq hC'pos.le
    exact mul_le_mul_of_nonneg_right h2 hM
  exact h1

end Work.KMTAreas.A4
