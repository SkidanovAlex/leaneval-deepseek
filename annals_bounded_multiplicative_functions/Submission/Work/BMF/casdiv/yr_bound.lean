import Mathlib
import Submission.Work.BMF.halasz_defs
import Submission.Work.BMF.casdiv.yr_series
import Submission.Work.BMF.halasz_intM
import Submission.Work.BMF.casdiv.wdb_support

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.casdiv

open scoped BigOperators
open MeasureTheory intervalIntegral

theorem yr_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) → (∀ n, ‖f n‖ ≤ 1) →
      ∀ x y T : ℝ, 11 ≤ x → 3 ≤ y → y ≤ x → 2 ≤ T →
        (∫ t in (Real.sqrt y)..y, ‖Mf f t‖ / t ^ 2) ≤
          C * (Real.exp (Wsup f x (1 / Real.log y) (T + 1)) +
               Real.exp (Zrcp y) / Real.sqrt T +
               1 / Real.log y) := by
  obtain ⟨CM, hCMpos, hM⟩ := Work.BMF.halasz_intM
  obtain ⟨CK, hCKpos, hK⟩ := yr_Kf_L1
  refine ⟨max (4 * CK) (2 * CM), lt_max_of_lt_left (by linarith), ?_⟩
  intro f hf1 hmul hb x y T hx hy hyx hT
  have hy1 : (1 : ℝ) ≤ y := by linarith
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have hylog : 0 < Real.log y := Real.log_pos (by linarith)
  have hsq1 : (1 : ℝ) ≤ Real.sqrt y := Real.one_le_sqrt.mpr hy1
  have hsq0 : 0 < Real.sqrt y := Real.sqrt_pos.mpr (by linarith)
  have hsqq : Real.sqrt y ≤ y := by
    have h : y ≤ y ^ 2 := by nlinarith
    calc Real.sqrt y ≤ Real.sqrt (y ^ 2) := Real.sqrt_le_sqrt h
      _ = y := Real.sqrt_sq hy0
  have hcy : Real.log (Real.sqrt y) = Real.log y / 2 := Real.log_sqrt hy0
  have hc : 0 < Real.log (Real.sqrt y) := by rw [hcy]; linarith
  -- integrability facts
  have hL1 : IntervalIntegrable (fun t : ℝ => ‖Mf f t‖ / t ^ 2) volume (Real.sqrt y) y :=
    Work.BMF.intervalIntegrable_norm_Mf_div_sq f hsq1 hsqq
  have hL2 : IntervalIntegrable (fun t : ℝ => ‖Mf f t‖ * Real.log t / t ^ 2)
      volume (Real.sqrt y) y :=
    Work.BMF.intervalIntegrable_norm_Mf_log_div_sq f hsq1 hsqq
  have hL2Y : IntervalIntegrable (fun t : ℝ => ‖Mf f t‖ * Real.log t / t ^ 2) volume 1 y :=
    Work.BMF.intervalIntegrable_norm_Mf_log_div_sq f le_rfl hy1
  -- STEP 1: log-weighting on `[√y, y]`
  have hstep1 : (∫ t in (Real.sqrt y)..y, ‖Mf f t‖ / t ^ 2)
      ≤ (1 / Real.log (Real.sqrt y)) *
        (∫ t in (Real.sqrt y)..y, ‖Mf f t‖ * Real.log t / t ^ 2) := by
    have hpt : ∀ t ∈ Set.Icc (Real.sqrt y) y,
        ‖Mf f t‖ / t ^ 2
          ≤ (1 / Real.log (Real.sqrt y)) * (‖Mf f t‖ * Real.log t / t ^ 2) := by
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le hsq0 ht.1
      have hlogt : Real.log (Real.sqrt y) ≤ Real.log t := Real.log_le_log hsq0 ht.1
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < t ^ 2)]
      have heq : (1 / Real.log (Real.sqrt y)) * (‖Mf f t‖ * Real.log t / t ^ 2) * t ^ 2
          = (‖Mf f t‖ * Real.log t) / Real.log (Real.sqrt y) := by
        field_simp
      rw [heq, le_div_iff₀ hc]
      exact mul_le_mul_of_nonneg_left hlogt (norm_nonneg _)
    have hmono := intervalIntegral.integral_mono_on hsqq hL1
      (hL2.const_mul (1 / Real.log (Real.sqrt y))) hpt
    rwa [intervalIntegral.integral_const_mul] at hmono
  -- STEP 2: pass to the full range `[1, y]`
  have hstep2 : (∫ t in (Real.sqrt y)..y, ‖Mf f t‖ * Real.log t / t ^ 2)
      ≤ ∫ t in (1 : ℝ)..y, ‖Mf f t‖ * Real.log t / t ^ 2 := by
    refine intervalIntegral.integral_mono_interval hsq1 hsqq le_rfl ?_ hL2Y
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => by
      rw [Set.mem_Ioc] at ht
      exact div_nonneg (mul_nonneg (norm_nonneg _) (Real.log_nonneg (le_of_lt ht.1)))
        (by positivity))
  have hstep12 : (∫ t in (Real.sqrt y)..y, ‖Mf f t‖ / t ^ 2)
      ≤ (1 / Real.log (Real.sqrt y)) *
        (∫ t in (1 : ℝ)..y, ‖Mf f t‖ * Real.log t / t ^ 2) :=
    le_trans hstep1 (mul_le_mul_of_nonneg_left hstep2 (by positivity))
  -- STEP 3: the Halász `intM` inequality at scale `y`
  have hM' := hM f hb y hy1
  -- STEP 4: the `Kf` bound of `b_bound`
  have hK' := hK f hf1 hmul hb x y T hx hy hyx hT
  -- combine
  have hInv : (1 : ℝ) / Real.log (Real.sqrt y) = 2 / Real.log y := by
    rw [hcy]; ring
  have hstep12' : (∫ t in (Real.sqrt y)..y, ‖Mf f t‖ / t ^ 2)
      ≤ (2 / Real.log y) * (∫ t in (1 : ℝ)..y, ‖Mf f t‖ * Real.log t / t ^ 2) := by
    refine le_trans hstep12 (le_of_eq ?_)
    rw [hInv]
  have hA_le : (∫ t in (Real.sqrt y)..y, ‖Mf f t‖ / t ^ 2)
      ≤ 4 * CK * Real.exp (Wsup f x (1 / Real.log y) (T + 1))
        + 4 * CK * (Real.exp (Zrcp y) / Real.sqrt T)
        + 2 * CM * (1 / Real.log y) := by
    have h1 : (2 / Real.log y) * (∫ t in (1 : ℝ)..y, ‖Mf f t‖ * Real.log t / t ^ 2)
        ≤ (2 / Real.log y) *
            (2 * (∫ t in (1 : ℝ)..y, ‖Kf f t‖ / t ^ 2) + CM) :=
      mul_le_mul_of_nonneg_left hM' (by positivity)
    have h2 : 2 * (∫ t in (1 : ℝ)..y, ‖Kf f t‖ / t ^ 2) + CM
        ≤ 2 * (CK * (Real.log y * Real.exp (Wsup f x (1 / Real.log y) (T + 1))
              + Real.exp (Zrcp y) * Real.log y / Real.sqrt T)) + CM := by
      linarith [hK']
    have h3 : (2 / Real.log y) *
          (2 * (CK * (Real.log y * Real.exp (Wsup f x (1 / Real.log y) (T + 1))
              + Real.exp (Zrcp y) * Real.log y / Real.sqrt T)) + CM)
        = 4 * CK * Real.exp (Wsup f x (1 / Real.log y) (T + 1))
          + 4 * CK * (Real.exp (Zrcp y) / Real.sqrt T)
          + 2 * CM * (1 / Real.log y) := by
      field_simp
      ring
    calc (∫ t in (Real.sqrt y)..y, ‖Mf f t‖ / t ^ 2)
        ≤ (2 / Real.log y) * (∫ t in (1 : ℝ)..y, ‖Mf f t‖ * Real.log t / t ^ 2) :=
          hstep12'
      _ ≤ (2 / Real.log y) * (2 * (∫ t in (1 : ℝ)..y, ‖Kf f t‖ / t ^ 2) + CM) := h1
      _ ≤ (2 / Real.log y) *
            (2 * (CK * (Real.log y * Real.exp (Wsup f x (1 / Real.log y) (T + 1))
              + Real.exp (Zrcp y) * Real.log y / Real.sqrt T)) + CM) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 4 * CK * Real.exp (Wsup f x (1 / Real.log y) (T + 1))
          + 4 * CK * (Real.exp (Zrcp y) / Real.sqrt T)
          + 2 * CM * (1 / Real.log y) := h3
  -- final assembly
  refine le_trans hA_le ?_
  have hW0 : 0 ≤ Real.exp (Wsup f x (1 / Real.log y) (T + 1)) := Real.exp_nonneg _
  have hE0 : 0 ≤ Real.exp (Zrcp y) / Real.sqrt T :=
    div_nonneg (Real.exp_nonneg _) (Real.sqrt_nonneg _)
  have hL0 : 0 ≤ 1 / Real.log y := by positivity
  have hm1 : 4 * CK ≤ max (4 * CK) (2 * CM) := le_max_left _ _
  have hm2 : 2 * CM ≤ max (4 * CK) (2 * CM) := le_max_right _ _
  have e1 := mul_le_mul_of_nonneg_right hm1 hW0
  have e2 := mul_le_mul_of_nonneg_right hm1 hE0
  have e3 := mul_le_mul_of_nonneg_right hm2 hL0
  nlinarith [e1, e2, e3]

end Work.BMF.casdiv
