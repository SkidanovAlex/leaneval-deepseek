import Mathlib
import Submission.Work.BMF.halasz_defs
import Submission.Work.BMF.halasz_plancherel
import Submission.Work.BMF.mrlas.norm_Kf_le
import Submission.Work.BMF.mrlas.interval_integral_cs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mrlas

open MeasureTheory intervalIntegral Finset

/-! ## Elementary support lemmas -/

/-- `Kf f t = Σ_{n ≤ ⌊t⌋₊} f n log n` vanishes for `t ≤ 1`: the index set `Icc 1 ⌊t⌋₊` is either
empty or `{1}`, and `log 1 = 0`. -/
lemma Kf_eq_zero_of_le_one (f : ℕ → ℂ) {t : ℝ} (ht : t ≤ 1) : Work.BMF.Kf f t = 0 := by
  have hfloor : ⌊t⌋₊ ≤ 1 := by
    have h := Nat.floor_mono ht
    rwa [Nat.floor_one] at h
  rw [Work.BMF.Kf]
  apply Finset.sum_eq_zero
  intro n hn
  rw [Finset.mem_Icc] at hn
  have hn1 : n = 1 := by omega
  rw [hn1]
  simp

/-- `t ↦ Kf f t` is measurable (it is a finite sum indexed by `⌊t⌋₊`). -/
lemma measurable_Kf (f : ℕ → ℂ) : Measurable (fun t : ℝ => Work.BMF.Kf f t) := by
  have hA : Measurable (fun n : ℕ => ∑ m ∈ Finset.Icc 1 n, f m * (Real.log m : ℂ)) :=
    measurable_of_countable _
  have hcomp : Measurable
      (fun t : ℝ => (fun n : ℕ => ∑ m ∈ Finset.Icc 1 n, f m * (Real.log m : ℂ)) ⌊t⌋₊) :=
    hA.comp (Nat.measurable_floor (R := ℝ))
  simpa only [Work.BMF.Kf] using hcomp

/-! ## Integrability of the `L²` density on `(0,∞)` -/

/-- For `‖f n‖ ≤ 1` and `α > 0`, the density `t ↦ ‖Kf f t‖²/t^{3+2α}` is integrable on `(0,∞)`.
The proof bounds it by the integrable majorant `(log t)² t^{-(1+2α)}` on `(1,∞)`, which is itself
dominated by `(4/α²) t^{-(1+α)}` using `Real.log_le_rpow_div`. -/
lemma integrableOn_Kf_sq_div_rpow (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) {α : ℝ} (hα : 0 < α) :
    IntegrableOn (fun t : ℝ => ‖Work.BMF.Kf f t‖ ^ 2 / t ^ (3 + 2 * α)) (Set.Ioi 0) := by
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => ‖Work.BMF.Kf f t‖ ^ 2 / t ^ (3 + 2 * α))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (((continuous_norm.measurable.comp (measurable_Kf f)).pow_const 2).div
      (measurable_id.pow_const (3 + 2 * α))).aestronglyMeasurable
  have hmaj_int : Integrable
      ((Set.Ioi (1 : ℝ)).indicator (fun t : ℝ => 4 / α ^ 2 * t ^ (-(1 + α)))) volume :=
    (integrable_indicator_iff measurableSet_Ioi).mpr
      (Integrable.const_mul
        (integrableOn_Ioi_rpow_of_lt (show -(1 + α) < -1 by linarith) (by norm_num : (0:ℝ) < 1))
        (4 / α ^ 2))
  have hmaj : Integrable
      ((Set.Ioi (1 : ℝ)).indicator (fun t : ℝ => 4 / α ^ 2 * t ^ (-(1 + α))))
      (volume.restrict (Set.Ioi (0 : ℝ))) := hmaj_int.integrableOn
  refine hmaj.mono' hmeas ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  by_cases h1t : 1 < t
  · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr h1t)]
    have hFnn : 0 ≤ ‖Work.BMF.Kf f t‖ ^ 2 / t ^ (3 + 2 * α) :=
      div_nonneg (sq_nonneg _) (Real.rpow_nonneg ht0.le _)
    rw [Real.norm_of_nonneg hFnn]
    have hKf : ‖Work.BMF.Kf f t‖ ≤ t * Real.log t := norm_Kf_le f hf h1t.le
    have hlogt : 0 ≤ Real.log t := Real.log_nonneg h1t.le
    have hden : 0 < t ^ (3 + 2 * α) := Real.rpow_pos_of_pos ht0 _
    have hstep1 : ‖Work.BMF.Kf f t‖ ^ 2 / t ^ (3 + 2 * α)
        ≤ (t * Real.log t) ^ 2 / t ^ (3 + 2 * α) :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hKf 2) hden.le
    have hlog2 : Real.log t ^ 2 ≤ 4 * t ^ α / α ^ 2 := by
      have hε : (0 : ℝ) < α / 2 := by linarith
      have hlogle : Real.log t ≤ 2 * t ^ (α / 2) / α := by
        have h := Real.log_le_rpow_div ht0.le hε
        have heq : t ^ (α / 2) / (α / 2) = 2 * t ^ (α / 2) / α := by
          field_simp
        linarith [h, heq.le, heq.ge]
      have h2 := pow_le_pow_left₀ hlogt hlogle 2
      have heq2 : (2 * t ^ (α / 2) / α) ^ 2 = 4 * t ^ α / α ^ 2 := by
        rw [div_pow, mul_pow]
        have hsq : (t ^ (α / 2)) ^ 2 = t ^ α := by
          rw [← Real.rpow_natCast (t ^ (α / 2)) 2, ← Real.rpow_mul ht0.le]
          congr 1
          ring
        rw [hsq]
        norm_num
      linarith [h2, heq2.le, heq2.ge]
    have hrew : (t * Real.log t) ^ 2 / t ^ (3 + 2 * α) = Real.log t ^ 2 * t ^ (-(1 + 2 * α)) := by
      have h3 : t ^ (2 : ℝ) / t ^ (3 + 2 * α) = t ^ (-(1 + 2 * α)) := by
        rw [← Real.rpow_sub ht0, show (2:ℝ) - (3 + 2 * α) = -(1 + 2 * α) by ring]
      have h1 : (t * Real.log t) ^ 2 / t ^ (3 + 2 * α)
          = Real.log t ^ 2 * (t ^ (2 : ℝ) / t ^ (3 + 2 * α)) := by
        rw [mul_pow, ← Real.rpow_natCast t 2]
        ring_nf
      rw [h1, h3]
    have hstep2 : (t * Real.log t) ^ 2 / t ^ (3 + 2 * α)
        ≤ (4 * t ^ α / α ^ 2) * t ^ (-(1 + 2 * α)) := by
      rw [hrew]
      exact mul_le_mul_of_nonneg_right hlog2 (Real.rpow_nonneg ht0.le _)
    have hstep3 : (4 * t ^ α / α ^ 2) * t ^ (-(1 + 2 * α)) = 4 / α ^ 2 * t ^ (-(1 + α)) := by
      have hA : (4 * t ^ α / α ^ 2) * t ^ (-(1 + 2 * α))
          = (4 / α ^ 2) * (t ^ α * t ^ (-(1 + 2 * α))) := by ring
      rw [hA, ← Real.rpow_add ht0 α (-(1 + 2 * α)), show α + -(1 + 2 * α) = -(1 + α) by ring]
    exact le_trans hstep1 (le_trans hstep2 (le_of_eq hstep3))
  · rw [Set.indicator_of_notMem (by simpa using h1t)]
    rw [Kf_eq_zero_of_le_one f (le_of_not_gt h1t)]
    simp

/-! ## The Plancherel comparison -/

/-- The truncated `L²` integral of `Kf` is bounded by the full Plancherel integral:
`∫_1^z ‖Kf f t‖²/t^{3+2α} ≤ (1/2π) ∫_ℝ ‖Kser f (1+α+iτ)‖²/‖1+α+iτ‖² dτ`.
The integrand vanishes on `(0,1)`, so the integral over `(1,z)` is bounded by the integral over
`(0,∞)`, to which `Work.BMF.halasz_plancherel` applies (the integrability input is
`integrableOn_Kf_sq_div_rpow`). -/
lemma kf_sq_integral_le_plancherel (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) {α z : ℝ}
    (hα : 0 < α) (hz : 1 ≤ z) :
    (∫ t in (1 : ℝ)..z, ‖Work.BMF.Kf f t‖ ^ 2 / t ^ (3 + 2 * α)) ≤
      (1 / (2 * Real.pi)) * ∫ τ : ℝ, ‖Work.BMF.Kser f
          (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 /
          ‖((((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I))‖ ^ 2 := by
  have hInt : IntegrableOn (fun t : ℝ => ‖Work.BMF.Kf f t‖ ^ 2 / t ^ (3 + 2 * α))
      (Set.Ioi 0) := integrableOn_Kf_sq_div_rpow f hf hα
  have hnn : ∀ t : ℝ, 0 ≤ ‖Work.BMF.Kf f t‖ ^ 2 / t ^ (3 + 2 * α) := by
    intro t
    by_cases h : 1 ≤ t
    · exact div_nonneg (sq_nonneg _) (Real.rpow_nonneg (by linarith) _)
    · push_neg at h
      rw [Kf_eq_zero_of_le_one f h.le]; simp
  have key : (∫ t in (1 : ℝ)..z, ‖Work.BMF.Kf f t‖ ^ 2 / t ^ (3 + 2 * α))
      ≤ ∫ t in Set.Ioi (0 : ℝ), ‖Work.BMF.Kf f t‖ ^ 2 / t ^ (3 + 2 * α) := by
    rw [intervalIntegral.integral_of_le hz]
    refine setIntegral_mono_set hInt (Filter.Eventually.of_forall hnn) ?_
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    exact lt_trans zero_lt_one ht.1
  calc (∫ t in (1 : ℝ)..z, ‖Work.BMF.Kf f t‖ ^ 2 / t ^ (3 + 2 * α))
      ≤ ∫ t in Set.Ioi (0 : ℝ), ‖Work.BMF.Kf f t‖ ^ 2 / t ^ (3 + 2 * α) := key
    _ = (1 / (2 * Real.pi)) * ∫ τ : ℝ, ‖Work.BMF.Kser f
          (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 /
          ‖((((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I))‖ ^ 2 :=
        halasz_plancherel f hf α hα

/-! ## Cauchy–Schwarz -/

/-- **Cauchy–Schwarz step.**  For `α > 0` and `1 ≤ z`,
`∫_1^z ‖Kf f t‖/t² ≤ (∫_1^z ‖Kf f t‖²/t^{3+2α})^{1/2} (∫_1^z t^{2α-1})^{1/2}`.
This is Cauchy–Schwarz (`interval_integral_mul_le_sqrt`) applied to
`‖Kf f t‖/t² = (‖Kf f t‖/t^{3/2+α}) · t^{α-1/2}`. -/
lemma kf_cauchy_schwarz (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) {α z : ℝ}
    (hα : 0 < α) (hz : 1 ≤ z) :
    (∫ t in (1 : ℝ)..z, ‖Work.BMF.Kf f t‖ / t ^ 2) ≤
      Real.sqrt (∫ t in (1 : ℝ)..z, ‖Work.BMF.Kf f t‖ ^ 2 / t ^ (3 + 2 * α)) *
        Real.sqrt (∫ t in (1 : ℝ)..z, t ^ (2 * α - 1)) := by
  have hKfm : Measurable (fun t : ℝ => Work.BMF.Kf f t) := measurable_Kf f
  set F : ℝ → ℝ := fun t => ‖Work.BMF.Kf f t‖ / t ^ ((3 : ℝ) / 2 + α) with hFdef
  set G : ℝ → ℝ := fun t => t ^ (α - 1 / 2) with hGdef
  have hFm : Measurable F := by
    rw [hFdef]
    exact (continuous_norm.measurable.comp hKfm).div (measurable_id.pow_const ((3 : ℝ) / 2 + α))
  have hGm : Measurable G := by
    rw [hGdef]; exact measurable_id.pow_const (α - 1 / 2)
  have hz0 : 0 < z := lt_of_lt_of_le one_pos hz
  have hzlogz : 0 ≤ z * Real.log z := mul_nonneg hz0.le (Real.log_nonneg hz)
  have hFG_eq : ∀ t ∈ Set.Icc (1 : ℝ) z, F t * G t = ‖Work.BMF.Kf f t‖ / t ^ 2 := by
    intro t ht
    have ht0 : 0 < t := (by linarith [ht.1] : (0 : ℝ) < t)
    have h3 : t ^ (α - 1 / 2) * t ^ 2 = t ^ ((3 : ℝ) / 2 + α) := by
      rw [← Real.rpow_natCast t 2, ← Real.rpow_add ht0]
      congr 1; ring
    rw [hFdef, hGdef]
    show ‖Work.BMF.Kf f t‖ / t ^ ((3 : ℝ) / 2 + α) * t ^ (α - 1 / 2) = ‖Work.BMF.Kf f t‖ / t ^ 2
    rw [div_mul_eq_mul_div, div_eq_div_iff (by positivity) (by positivity), mul_assoc, h3]
  have hF2_eq : ∀ t ∈ Set.Icc (1 : ℝ) z, F t ^ 2 = ‖Work.BMF.Kf f t‖ ^ 2 / t ^ (3 + 2 * α) := by
    intro t ht
    have ht0 : 0 < t := (by linarith [ht.1] : (0 : ℝ) < t)
    have ha : (t ^ ((3 : ℝ) / 2 + α)) ^ 2 = t ^ (3 + 2 * α) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
      congr 1; ring
    rw [hFdef]
    show (‖Work.BMF.Kf f t‖ / t ^ ((3 : ℝ) / 2 + α)) ^ 2
        = ‖Work.BMF.Kf f t‖ ^ 2 / t ^ (3 + 2 * α)
    rw [div_pow, ha]
  have hG2_eq : ∀ t ∈ Set.Icc (1 : ℝ) z, G t ^ 2 = t ^ (2 * α - 1) := by
    intro t ht
    have ht0 : 0 < t := (by linarith [ht.1] : (0 : ℝ) < t)
    rw [hGdef]
    show (t ^ (α - 1 / 2)) ^ 2 = t ^ (2 * α - 1)
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
    congr 1; ring
  have hFb : ∀ t ∈ Set.Ioc (1 : ℝ) z, ‖F t ^ 2‖ ≤ max 1 ((z * Real.log z) ^ 2) := by
    intro t ht
    have ht0 : 0 < t := (by linarith [ht.1] : (0 : ℝ) < t)
    have hKf : ‖Work.BMF.Kf f t‖ ≤ t * Real.log t := norm_Kf_le f hf ht.1.le
    have hlogt : 0 ≤ Real.log t := Real.log_nonneg ht.1.le
    have hml : t * Real.log t ≤ z * Real.log z :=
      mul_le_mul ht.2 (Real.log_le_log ht0 ht.2) hlogt hz0.le
    have hden : 1 ≤ t ^ ((3 : ℝ) / 2 + α) := Real.one_le_rpow ht.1.le (by linarith)
    have hden0 : 0 < t ^ ((3 : ℝ) / 2 + α) := lt_of_lt_of_le one_pos hden
    have hFnn : 0 ≤ F t := by
      rw [hFdef]; exact div_nonneg (norm_nonneg _) hden0.le
    have hFle : F t ≤ z * Real.log z := by
      rw [hFdef]
      show ‖Work.BMF.Kf f t‖ / t ^ ((3 : ℝ) / 2 + α) ≤ z * Real.log z
      calc ‖Work.BMF.Kf f t‖ / t ^ ((3 : ℝ) / 2 + α)
          ≤ (z * Real.log z) / t ^ ((3 : ℝ) / 2 + α) :=
            div_le_div_of_nonneg_right (le_trans hKf hml) hden0.le
        _ ≤ (z * Real.log z) / 1 := div_le_div_of_nonneg_left hzlogz one_pos hden
        _ = z * Real.log z := div_one _
    rw [Real.norm_of_nonneg (sq_nonneg (F t))]
    calc F t ^ 2 ≤ (z * Real.log z) ^ 2 := pow_le_pow_left₀ hFnn hFle 2
      _ ≤ max 1 ((z * Real.log z) ^ 2) := le_max_right _ _
  have hGb : ∀ t ∈ Set.Ioc (1 : ℝ) z, ‖G t ^ 2‖ ≤ max 1 (z ^ (2 * α - 1)) := by
    intro t ht
    have ht1 : 1 ≤ t := ht.1.le
    rw [Real.norm_of_nonneg (sq_nonneg (G t)), hG2_eq t ⟨ht.1.le, ht.2⟩]
    by_cases h : 0 ≤ 2 * α - 1
    · calc t ^ (2 * α - 1) ≤ z ^ (2 * α - 1) := Real.rpow_le_rpow (by linarith) ht.2 h
        _ ≤ max 1 (z ^ (2 * α - 1)) := le_max_right _ _
    · push_neg at h
      calc t ^ (2 * α - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht1 h.le
        _ ≤ max 1 (z ^ (2 * α - 1)) := le_max_left _ _
  have hFGb : ∀ t ∈ Set.Ioc (1 : ℝ) z, ‖F t * G t‖ ≤ max 1 (z * Real.log z) := by
    intro t ht
    have ht0 : 0 < t := (by linarith [ht.1] : (0 : ℝ) < t)
    have hKf : ‖Work.BMF.Kf f t‖ ≤ t * Real.log t := norm_Kf_le f hf ht.1.le
    have hlogt : 0 ≤ Real.log t := Real.log_nonneg ht.1.le
    have hml : t * Real.log t ≤ z * Real.log z :=
      mul_le_mul ht.2 (Real.log_le_log ht0 ht.2) hlogt hz0.le
    have ht2 : (1 : ℝ) ≤ t ^ 2 := by nlinarith [ht.1, ht0]
    rw [hFG_eq t ⟨ht.1.le, ht.2⟩, Real.norm_of_nonneg (div_nonneg (norm_nonneg _) (by positivity))]
    calc ‖Work.BMF.Kf f t‖ / t ^ 2 ≤ ‖Work.BMF.Kf f t‖ / 1 :=
          div_le_div_of_nonneg_left (norm_nonneg _) one_pos ht2
      _ = ‖Work.BMF.Kf f t‖ := div_one _
      _ ≤ z * Real.log z := le_trans hKf hml
      _ ≤ max 1 (z * Real.log z) := le_max_right _ _
  have hF2int : IntervalIntegrable (fun t : ℝ => F t ^ 2) volume 1 z := by
    refine IntervalIntegrable.mono_fun (f := fun _ : ℝ => max 1 ((z * Real.log z) ^ 2))
      intervalIntegrable_const (hFm.pow_const 2).aestronglyMeasurable ?_
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    rw [Set.uIoc_of_le hz] at ht
    have hC : (0 : ℝ) ≤ max 1 ((z * Real.log z) ^ 2) := le_trans zero_le_one (le_max_left _ _)
    rw [Real.norm_of_nonneg hC]
    exact hFb t ht
  have hG2int : IntervalIntegrable (fun t : ℝ => G t ^ 2) volume 1 z := by
    refine IntervalIntegrable.mono_fun (f := fun _ : ℝ => max 1 (z ^ (2 * α - 1)))
      intervalIntegrable_const (hGm.pow_const 2).aestronglyMeasurable ?_
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    rw [Set.uIoc_of_le hz] at ht
    have hC : (0 : ℝ) ≤ max 1 (z ^ (2 * α - 1)) := le_trans zero_le_one (le_max_left _ _)
    rw [Real.norm_of_nonneg hC]
    exact hGb t ht
  have hFGint : IntervalIntegrable (fun t : ℝ => F t * G t) volume 1 z := by
    refine IntervalIntegrable.mono_fun (f := fun _ : ℝ => max 1 (z * Real.log z))
      intervalIntegrable_const (hFm.mul hGm).aestronglyMeasurable ?_
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    rw [Set.uIoc_of_le hz] at ht
    have hC : (0 : ℝ) ≤ max 1 (z * Real.log z) := le_trans zero_le_one (le_max_left _ _)
    rw [Real.norm_of_nonneg hC]
    exact hFGb t ht
  have hFnn' : ∀ t ∈ Set.Icc (1 : ℝ) z, 0 ≤ F t := by
    intro t ht
    have ht0 : 0 < t := (by linarith [ht.1] : (0 : ℝ) < t)
    rw [hFdef]; exact div_nonneg (norm_nonneg _) (Real.rpow_nonneg ht0.le _)
  have hGnn' : ∀ t ∈ Set.Icc (1 : ℝ) z, 0 ≤ G t := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans zero_le_one ht.1
    rw [hGdef]; exact Real.rpow_nonneg ht0 _
  have hcs := interval_integral_mul_le_sqrt hz hF2int hG2int hFGint hFnn' hGnn'
  have e1 : (∫ t in (1 : ℝ)..z, F t * G t) = ∫ t in (1 : ℝ)..z, ‖Work.BMF.Kf f t‖ / t ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hz] at ht
    exact hFG_eq t ht
  have e2 : (∫ t in (1 : ℝ)..z, F t ^ 2)
      = ∫ t in (1 : ℝ)..z, ‖Work.BMF.Kf f t‖ ^ 2 / t ^ (3 + 2 * α) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hz] at ht
    exact hF2_eq t ht
  have e3 : (∫ t in (1 : ℝ)..z, G t ^ 2) = ∫ t in (1 : ℝ)..z, t ^ (2 * α - 1) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hz] at ht
    exact hG2_eq t ht
  rw [e1, e2, e3] at hcs
  exact hcs

/-! ## The elementary `rpow` integral -/

/-- With `α = 1/log z` and `z ≥ 3`: `∫_1^z t^{2α-1} dt ≤ e² log z`. -/
lemma int_rpow_sub_one_le (z : ℝ) (hz : 3 ≤ z) :
    (∫ t in (1 : ℝ)..z, t ^ (2 * (1 / Real.log z) - 1)) ≤ Real.exp 2 * Real.log z := by
  set α : ℝ := 1 / Real.log z with hαdef
  have hz1 : (1 : ℝ) ≤ z := by linarith
  have hz0 : 0 < z := by linarith
  have hlog : 0 < Real.log z := Real.log_pos (by linarith)
  have hα : 0 < α := by rw [hαdef]; positivity
  have hpow : z ^ (2 * α) = Real.exp 2 := by
    rw [Real.rpow_def_of_pos hz0]
    congr 1
    rw [hαdef]
    field_simp
  have hpt : ∀ t ∈ Set.Icc (1 : ℝ) z, t ^ (2 * α - 1) ≤ Real.exp 2 * t ^ (-1 : ℝ) := by
    intro t ht
    have ht0 : 0 < t := (by linarith [ht.1] : (0 : ℝ) < t)
    have h2a : 0 ≤ 2 * α := by linarith
    have h1 : t ^ (2 * α) ≤ z ^ (2 * α) := Real.rpow_le_rpow ht0.le ht.2 h2a
    have h1' : t ^ (2 * α) ≤ Real.exp 2 := le_trans h1 (le_of_eq hpow)
    have h2 : t ^ (2 * α - 1) = t ^ (2 * α) * t ^ (-1 : ℝ) := by
      have h := Real.rpow_add ht0 (2 * α) (-1 : ℝ)
      rw [show 2 * α + (-1 : ℝ) = 2 * α - 1 by ring] at h
      exact h
    rw [h2]
    exact mul_le_mul_of_nonneg_right h1' (Real.rpow_nonneg ht0.le _)
  have hint1 : IntervalIntegrable (fun t : ℝ => t ^ (2 * α - 1)) volume 1 z := by
    refine IntervalIntegrable.mono_fun (f := fun _ : ℝ => max 1 (z ^ (2 * α - 1)))
      intervalIntegrable_const ?_ ?_
    · exact (measurable_id.pow_const (2 * α - 1)).aestronglyMeasurable
    · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
      refine Filter.Eventually.of_forall (fun t ht => ?_)
      rw [Set.uIoc_of_le hz1] at ht
      have ht1 : 1 ≤ t := ht.1.le
      have hC : (0 : ℝ) ≤ max 1 (z ^ (2 * α - 1)) := le_trans zero_le_one (le_max_left _ _)
      rw [Real.norm_of_nonneg hC, Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : (0:ℝ) ≤ t) _)]
      by_cases h : 0 ≤ 2 * α - 1
      · calc t ^ (2 * α - 1) ≤ z ^ (2 * α - 1) := Real.rpow_le_rpow (by linarith) ht.2 h
          _ ≤ max 1 (z ^ (2 * α - 1)) := le_max_right _ _
      · push_neg at h
        calc t ^ (2 * α - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht1 h.le
          _ ≤ max 1 (z ^ (2 * α - 1)) := le_max_left _ _
  have hint2 : IntervalIntegrable (fun t : ℝ => Real.exp 2 * t ^ (-1 : ℝ)) volume 1 z := by
    refine IntervalIntegrable.mono_fun (f := fun _ : ℝ => max (Real.exp 2) 1)
      intervalIntegrable_const ?_ ?_
    · exact ((measurable_const.mul (measurable_id.pow_const (-1 : ℝ)))).aestronglyMeasurable
    · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
      refine Filter.Eventually.of_forall (fun t ht => ?_)
      rw [Set.uIoc_of_le hz1] at ht
      have ht1 : 1 ≤ t := ht.1.le
      have hC : (0 : ℝ) ≤ max (Real.exp 2) 1 := le_trans zero_le_one (le_max_right _ _)
      have hnn : 0 ≤ Real.exp 2 * t ^ (-1 : ℝ) :=
        mul_nonneg (Real.exp_pos 2).le (Real.rpow_nonneg (by linarith : (0:ℝ) ≤ t) _)
      rw [Real.norm_of_nonneg hC, Real.norm_of_nonneg hnn]
      calc Real.exp 2 * t ^ (-1 : ℝ) ≤ Real.exp 2 * 1 :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_one_of_one_le_of_nonpos ht1 (by norm_num)) (Real.exp_pos 2).le
        _ = Real.exp 2 := mul_one _
        _ ≤ max (Real.exp 2) 1 := le_max_left _ _
  have hmono := intervalIntegral.integral_mono_on hz1 hint1 hint2 hpt
  have hInt : (∫ t in (1 : ℝ)..z, Real.exp 2 * t ^ (-1 : ℝ)) = Real.exp 2 * Real.log z := by
    rw [intervalIntegral.integral_const_mul]
    have h1 : (∫ t in (1 : ℝ)..z, t ^ (-1 : ℝ)) = ∫ t in (1 : ℝ)..z, t⁻¹ := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact Real.rpow_neg_one t
    rw [h1, integral_inv_of_pos (by norm_num : (0 : ℝ) < 1) hz0]
    simp
  rw [hαdef] at hpt hmono
  rw [hInt] at hmono
  exact hmono

/-! ## The main estimate -/

/-- **Cauchy–Schwarz + Plancherel.**  For a `1`-bounded `f` and `3 ≤ z`, with `α = 1/log z ≤ 1`
and `J = ∫_ℝ ‖Kser f (1+α+iτ)‖²/‖1+α+iτ‖² dτ`,

`∫_1^z ‖Kf f t‖/t² dt ≤ C √(J log z)`.

Indeed `∫_1^z ‖Kf‖/t² ≤ (∫_1^z ‖Kf‖²/t^{3+2α})^{1/2} (∫_1^z t^{2α-1})^{1/2}` by Cauchy–Schwarz,
`∫_1^z t^{2α-1} ≤ z^{2α}/(2α) = e² log z / 2` since `α = 1/log z`, and
`∫_1^z ‖Kf f t‖²/t^{3+2α} ≤ ∫_{Ioi 0} ‖Kf f t‖²/t^{3+2α} = J/(2π)` by
`Work.BMF.halasz_plancherel` (the integrand vanishes for `t < 1`). -/
theorem casdiv_kf_planch : ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) →
      ∀ z : ℝ, 3 ≤ z →
        (∫ t in (1 : ℝ)..z, ‖Work.BMF.Kf f t‖ / t ^ 2) ≤
          C * Real.sqrt ((∫ τ : ℝ, ‖Work.BMF.Kser f
              (((1 + 1 / Real.log z : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 /
              ‖((((1 + 1 / Real.log z : ℝ) : ℂ) + (τ : ℂ) * Complex.I))‖ ^ 2)
            * Real.log z) := by
  refine ⟨4, by norm_num, ?_⟩
  intro f hf z hz
  have hz1 : (1 : ℝ) ≤ z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hα : 0 < 1 / Real.log z := by positivity
  set J : ℝ := ∫ τ : ℝ, ‖Work.BMF.Kser f
      (((1 + 1 / Real.log z : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 /
      ‖((((1 + 1 / Real.log z : ℝ) : ℂ) + (τ : ℂ) * Complex.I))‖ ^ 2 with hJdef
  have hCS := kf_cauchy_schwarz f hf hα hz1
  have hAle := kf_sq_integral_le_plancherel f hf hα hz1
  have hBle := int_rpow_sub_one_le z hz
  have hJ0 : 0 ≤ J := by
    rw [hJdef]
    exact MeasureTheory.integral_nonneg_of_ae
      (Filter.Eventually.of_forall (fun τ => by positivity))
  have hA0 : 0 ≤ ∫ t in (1 : ℝ)..z, ‖Work.BMF.Kf f t‖ ^ 2 / t ^ (3 + 2 * (1 / Real.log z)) :=
    intervalIntegral.integral_nonneg hz1 (fun t ht => by
      have ht0 : (0 : ℝ) < t := (by linarith [ht.1] : (0 : ℝ) < t)
      exact div_nonneg (sq_nonneg _) (Real.rpow_nonneg ht0.le _))
  have hB0 : 0 ≤ ∫ t in (1 : ℝ)..z, t ^ (2 * (1 / Real.log z) - 1) :=
    intervalIntegral.integral_nonneg hz1 (fun t ht =>
      Real.rpow_nonneg (by linarith [ht.1] : (0 : ℝ) ≤ t) _)
  have h1 : Real.sqrt (∫ t in (1 : ℝ)..z, ‖Work.BMF.Kf f t‖ ^ 2 / t ^ (3 + 2 * (1 / Real.log z)))
        * Real.sqrt (∫ t in (1 : ℝ)..z, t ^ (2 * (1 / Real.log z) - 1))
      ≤ Real.sqrt ((1 / (2 * Real.pi)) * J) * Real.sqrt (Real.exp 2 * Real.log z) :=
    mul_le_mul (Real.sqrt_le_sqrt hAle) (Real.sqrt_le_sqrt hBle) (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)
  have h2 : Real.sqrt ((1 / (2 * Real.pi)) * J) * Real.sqrt (Real.exp 2 * Real.log z)
      ≤ 4 * Real.sqrt (J * Real.log z) := by
    have hc0 : 0 ≤ (1 / (2 * Real.pi)) * J := mul_nonneg (by positivity) hJ0
    have hkey : Real.exp 2 / (2 * Real.pi) ≤ 16 := by
      rw [div_le_iff₀ (by positivity)]
      have h3 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
      have he2 : Real.exp 2 < 9 := by
        have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
          rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
        rw [h2]
        nlinarith [Real.exp_pos 1, h3,
          mul_pos (by linarith : (0 : ℝ) < 3 - Real.exp 1)
            (by linarith [Real.exp_pos 1] : (0 : ℝ) < 3 + Real.exp 1)]
      nlinarith [Real.pi_gt_three]
    rw [← Real.sqrt_mul hc0]
    have hmono : (1 / (2 * Real.pi)) * J * (Real.exp 2 * Real.log z) ≤ 16 * (J * Real.log z) := by
      have heq : (1 / (2 * Real.pi)) * J * (Real.exp 2 * Real.log z)
          = (Real.exp 2 / (2 * Real.pi)) * (J * Real.log z) := by
        rw [div_eq_mul_inv, one_mul]
        ring
      rw [heq]
      exact mul_le_mul_of_nonneg_right hkey (mul_nonneg hJ0 hlogz.le)
    calc Real.sqrt ((1 / (2 * Real.pi)) * J * (Real.exp 2 * Real.log z))
        ≤ Real.sqrt (16 * (J * Real.log z)) := Real.sqrt_le_sqrt hmono
      _ = 4 * Real.sqrt (J * Real.log z) := by
          rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4 ^ 2),
            Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 4)]
  have hmain : (∫ t in (1 : ℝ)..z, ‖Work.BMF.Kf f t‖ / t ^ 2) ≤ 4 * Real.sqrt (J * Real.log z) :=
    le_trans (le_trans hCS h1) h2
  exact hmain

end Work.BMF.mrlas
