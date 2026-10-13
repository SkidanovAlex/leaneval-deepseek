import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Submission.Work.FTS.PhiStar.Radial.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.PhiStar.Honesty.CSTools

/-- Cauchy–Schwarz near zero.

For `r ≥ -2`, writing `c t * t ^ r = (c t / t ^ 2) * t ^ (r + 2)` and applying Cauchy–Schwarz to
the functions `t ↦ c t / t ^ 2` and `t ↦ t ^ (r + 2)` on `(0,1]` gives

`(∫_0^1 c t · t^r)² ≤ (∫_0^1 c²/t⁴) · (∫_0^1 t^{2r+4}) ≤ ∫_0^1 c²/t⁴`

because `2r + 4 ≥ 0` makes `t^{2r+4} ≤ 1` there.  (When `c · (·)^r` fails to be integrable, the
interval integral is `0` by definition and the inequality holds trivially.) -/
theorem sq_near_zero {c : ℝ → ℝ} {r : ℝ} (hr : -2 ≤ r)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1)) :
    (∫ t in (0 : ℝ)..1, c t * t ^ r) ^ 2 ≤ ∫ t in (0 : ℝ)..1, (c t) ^ 2 / t ^ 4 := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  -- `Ioc 0 1` and `Ioo 0 1` differ by the null set `{1}`.
  have hae : Set.Ioc (0:ℝ) 1 =ᵐ[volume] Set.Ioo (0:ℝ) 1 := by
    rw [MeasureTheory.ae_eq_set]
    constructor
    · have h : Set.Ioc (0:ℝ) 1 \ Set.Ioo (0:ℝ) 1 = {1} := by
        ext x
        simp only [Set.mem_sdiff, Set.mem_Ioc, Set.mem_Ioo, Set.mem_singleton_iff]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          exact le_antisymm h2 (le_of_not_gt (fun hlt => h3 ⟨h1, hlt⟩))
        · rintro rfl
          exact ⟨⟨zero_lt_one, le_rfl⟩, by norm_num⟩
      rw [h]; simp
    · have h : Set.Ioo (0:ℝ) 1 \ Set.Ioc (0:ℝ) 1 = ∅ := by
        ext x
        simp only [Set.mem_sdiff, Set.mem_Ioo, Set.mem_Ioc, Set.mem_empty_iff_false]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          exact absurd ⟨h1, le_of_lt h2⟩ h3
        · intro h; exact h.elim
      rw [h]; simp
  have hgi : IntegrableOn (fun t : ℝ => (c t)^2 / t^4) (Set.Ioc 0 1) := hnear.congr_set_ae hae
  by_cases hfint : IntegrableOn (fun t : ℝ => c t * t^r) (Set.Ioc (0:ℝ) 1)
  · -- Case 1: `c · (·)^r` is integrable; apply Cauchy–Schwarz.
    have hfm : AEStronglyMeasurable (fun t : ℝ => c t * t^r) (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
      hfint.aestronglyMeasurable
    have hgm : AEStronglyMeasurable (fun t : ℝ => t ^ (-(r+2))) (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
      ContinuousOn.aestronglyMeasurable
        ((continuousOn_id : ContinuousOn (fun x : ℝ => x) (Set.Ioc (0:ℝ) 1)).rpow_const
          (fun x hx => Or.inl (ne_of_gt hx.1))) measurableSet_Ioc
    -- `t ↦ c t / t^2` is a.e. strongly measurable since it agrees with `t ↦ (c t · t^r) · t^{-r-2}`.
    have hFmeas : AEStronglyMeasurable (fun t : ℝ => c t / t^2) (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
      refine (hfm.mul hgm).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      simp only [Pi.mul_apply]
      have ht0 : (0:ℝ) < t := ht.1
      have h1 : t ^ (-(2:ℝ)) = (t^2)⁻¹ := by
        rw [Real.rpow_neg (le_of_lt ht0) 2]; congr 1; rw [Real.rpow_ofNat]
      rw [mul_assoc, ← Real.rpow_add ht0]
      have h3 : r + -(r+2) = -(2:ℝ) := by ring
      rw [h3, h1, div_eq_mul_inv]
    have hF2 : Integrable (fun t : ℝ => (c t / t^2)^2) (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
      hgi.congr (Filter.Eventually.of_forall (fun t => by
        simp only []
        rw [div_pow, show ((t:ℝ)^2)^2 = t^4 by ring]))
    have hFmem : MemLp (fun t : ℝ => c t / t^2) (ENNReal.ofReal (2:ℝ))
        (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
      rw [show ENNReal.ofReal (2:ℝ) = (2 : ENNReal) by norm_num]
      exact (memLp_two_iff_integrable_sq hFmeas).2 hF2
    have hGmeas : AEStronglyMeasurable (fun t : ℝ => t ^ (r+2)) (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
      ContinuousOn.aestronglyMeasurable
        ((continuousOn_id : ContinuousOn (fun x : ℝ => x) (Set.Ioc (0:ℝ) 1)).rpow_const
          (fun x hx => Or.inl (ne_of_gt hx.1))) measurableSet_Ioc
    have hG2 : Integrable (fun t : ℝ => (t^(r+2))^2) (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
      have hint : Integrable (fun t : ℝ => t^((r+2)*2)) (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
        (intervalIntegral.intervalIntegrable_rpow'
          (a := (0:ℝ)) (b := 1) (r := (r+2)*2) (by linarith)).1
      refine hint.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [Real.rpow_mul (le_of_lt ht.1) (r+2) 2, Real.rpow_ofNat]
    have hGmem : MemLp (fun t : ℝ => t^(r+2)) (ENNReal.ofReal (2:ℝ))
        (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
      rw [show ENNReal.ofReal (2:ℝ) = (2 : ENNReal) by norm_num]
      exact (memLp_two_iff_integrable_sq hGmeas).2 hG2
    have hholder := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
      (μ := volume.restrict (Set.Ioc (0:ℝ) 1))
      (f := fun t : ℝ => c t / t^2) (g := fun t : ℝ => t^(r+2))
      (p := 2) (q := 2) (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩) hFmem hGmem
    have hFsq : (∫ t in Set.Ioc (0:ℝ) 1, ‖c t / t^2‖ ^ (2:ℝ))
        = ∫ t in Set.Ioc (0:ℝ) 1, (c t / t^2)^2 := by
      refine integral_congr_ae ?_
      refine Filter.Eventually.of_forall (fun t => ?_)
      simp only []
      rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]
    have hGsq : (∫ t in Set.Ioc (0:ℝ) 1, ‖t^(r+2)‖ ^ (2:ℝ))
        = ∫ t in Set.Ioc (0:ℝ) 1, (t^(r+2))^2 := by
      refine integral_congr_ae ?_
      refine Filter.Eventually.of_forall (fun t => ?_)
      simp only []
      rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]
    have hroot : ∫ t in Set.Ioc (0:ℝ) 1, ‖c t / t^2‖ * ‖t^(r+2)‖
        ≤ (∫ t in Set.Ioc (0:ℝ) 1, (c t / t^2)^2)^((1:ℝ)/2)
          * (∫ t in Set.Ioc (0:ℝ) 1, (t^(r+2))^2)^((1:ℝ)/2) := by
      rw [hFsq, hGsq] at hholder
      exact hholder
    have h1 : |∫ t in Set.Ioc (0:ℝ) 1, (c t / t^2) * t^(r+2)|
        ≤ ∫ t in Set.Ioc (0:ℝ) 1, ‖c t / t^2‖ * ‖t^(r+2)‖ := by
      have heq : (∫ t in Set.Ioc (0:ℝ) 1, |(c t / t^2) * t^(r+2)|)
          = ∫ t in Set.Ioc (0:ℝ) 1, ‖c t / t^2‖ * ‖t^(r+2)‖ := by
        refine integral_congr_ae ?_
        refine Filter.Eventually.of_forall (fun t => ?_)
        simp only []
        simp only [Real.norm_eq_abs, abs_mul]
      exact (MeasureTheory.abs_integral_le_integral_abs (μ := volume.restrict (Set.Ioc (0:ℝ) 1))
        (f := fun t : ℝ => (c t / t^2) * t^(r+2))).trans heq.le
    have hsqF : 0 ≤ ∫ t in Set.Ioc (0:ℝ) 1, (c t / t^2)^2 :=
      setIntegral_nonneg measurableSet_Ioc (fun t ht => by positivity)
    have hsqG : 0 ≤ ∫ t in Set.Ioc (0:ℝ) 1, (t^(r+2))^2 :=
      setIntegral_nonneg measurableSet_Ioc (fun t ht => by positivity)
    have hGle : ∫ t in Set.Ioc (0:ℝ) 1, (t^(r+2))^2 ≤ 1 := by
      have hbd : ∀ t ∈ Set.Ioc (0:ℝ) 1, (t^(r+2))^2 ≤ (1:ℝ) := by
        intro t ht
        have h1 : t ^ (r+2) ≤ 1 := Real.rpow_le_one (le_of_lt ht.1) ht.2 (by linarith)
        calc (t^(r+2))^2 ≤ (1:ℝ)^2 := pow_le_pow_left₀ (Real.rpow_nonneg (le_of_lt ht.1) _) h1 2
          _ = 1 := by norm_num
      calc ∫ t in Set.Ioc (0:ℝ) 1, (t^(r+2))^2
          ≤ ∫ t in Set.Ioc (0:ℝ) 1, (1:ℝ) :=
            setIntegral_mono_on hG2 (MeasureTheory.integrableOn_const (C := (1:ℝ))
              (s := Set.Ioc (0:ℝ) 1) (by rw [Real.volume_Ioc]; simp) (by simp)) measurableSet_Ioc hbd
        _ = 1 := by
            rw [MeasureTheory.setIntegral_const]
            simp [MeasureTheory.measureReal_def, Real.volume_Ioc]
    have hCsqrt : (∫ t in Set.Ioc (0:ℝ) 1, (t^(r+2))^2)^((1:ℝ)/2) ≤ 1 := by
      have h1 : (∫ t in Set.Ioc (0:ℝ) 1, (t^(r+2))^2)^((1:ℝ)/2) ≤ (1:ℝ)^((1:ℝ)/2) :=
        Real.rpow_le_rpow hsqG hGle (by norm_num)
      rwa [Real.one_rpow] at h1
    have hBsq : ((∫ t in Set.Ioc (0:ℝ) 1, (c t / t^2)^2)^((1:ℝ)/2))^2
        = ∫ t in Set.Ioc (0:ℝ) 1, (c t / t^2)^2 := by
      rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hsqF]
    have hfin : ∫ t in Set.Ioc (0:ℝ) 1, (c t / t^2)^2 = ∫ t in Set.Ioc (0:ℝ) 1, (c t)^2/t^4 := by
      refine integral_congr_ae ?_
      refine Filter.Eventually.of_forall (fun t => ?_)
      simp only []
      rw [div_pow, show ((t:ℝ)^2)^2 = t^4 by ring]
    have hA : (∫ t in Set.Ioc (0:ℝ) 1, c t * t^r)
        = ∫ t in Set.Ioc (0:ℝ) 1, (c t / t^2) * t^(r+2) :=
      (setIntegral_congr_fun measurableSet_Ioc (fun t ht => by
        have ht0 : (0:ℝ) < t := ht.1
        have h2 : t^(r+2)/t^2 = t^r := by
          rw [show (t:ℝ)^2 = t^(2:ℝ) by rw [Real.rpow_ofNat]]
          rw [← Real.rpow_sub ht0 (r+2) 2]
          congr 1
          ring
        rw [show c t / t^2 * t^(r+2) = c t * (t^(r+2)/t^2) by ring, h2])).symm
    calc (∫ t in Set.Ioc (0:ℝ) 1, c t * t^r)^2
        = (∫ t in Set.Ioc (0:ℝ) 1, (c t / t^2) * t^(r+2))^2 := by rw [hA]
      _ ≤ (∫ t in Set.Ioc (0:ℝ) 1, ‖c t/t^2‖ * ‖t^(r+2)‖)^2 :=
            sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2
      _ ≤ ((∫ t in Set.Ioc (0:ℝ) 1, (c t/t^2)^2)^((1:ℝ)/2)
            * (∫ t in Set.Ioc (0:ℝ) 1, (t^(r+2))^2)^((1:ℝ)/2))^2 := by
            apply pow_le_pow_left₀ (le_trans (abs_nonneg _) h1)
            exact hroot
      _ ≤ ((∫ t in Set.Ioc (0:ℝ) 1, (c t/t^2)^2)^((1:ℝ)/2))^2 := by
            apply pow_le_pow_left₀ (mul_nonneg (Real.rpow_nonneg hsqF _) (Real.rpow_nonneg hsqG _))
            exact mul_le_of_le_one_right (Real.rpow_nonneg hsqF _) hCsqrt
      _ = ∫ t in Set.Ioc (0:ℝ) 1, (c t/t^2)^2 := hBsq
      _ = ∫ t in Set.Ioc (0:ℝ) 1, (c t)^2/t^4 := hfin
  · -- Case 2: `c · (·)^r` is not integrable, so its interval integral is `0`; the right-hand side
    -- is the integral of a nonnegative function.
    rw [MeasureTheory.integral_undef hfint]
    norm_num
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ioc
      (fun t ht => div_nonneg (sq_nonneg _) (by positivity))

end Work.FTS.PhiStar.Honesty.CSTools
