import Mathlib
import Submission.Work.GM.S3.Base
import Submission.Work.GM.S3.Defs
import Submission.Work.GM.S3.prop71_defs
import Submission.Work.GM.S3.prop101_defs
import Submission.Work.GM.S3.prop72_core
import Submission.Work.GM.S3.window_defs
import Submission.Work.GM.S3.RtildeSq_continuous
import Submission.Work.GM.S3.window_pair_bound

namespace Work.GM.S3

open Complex Finset MeasureTheory
open scoped BigOperators
open Submission.GM (Rfun)

theorem window_integral_le_Rtilde {W : Finset ℝ} {N : ℕ} {B η : ℝ} {ψ₁ ψ₂ : ℝ → ℝ} {C₀ : ℝ}
    (hC₀ : 1 ≤ C₀) (h₁ : Work.GM.S3.IsBumpAtZero ψ₁ C₀) (h₂ : Work.GM.S3.IsBumpAtOne ψ₂ C₀)
    (hψ₁ge : ∀ x, |x| ≤ 1 → 1 ≤ ψ₁ x)
    (hψ₂ge : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 2, 1 ≤ ψ₂ x)
    (hη : 0 < η) (hB : 0 < (N : ℝ) * B)
    {m₁ m₂ m₃ : ℤ}
    (hspace : B * (Submission.LargeValues.M N) ^ η ≤ |((m₂ : ℤ) : ℝ)| / 2)
    (hgood : ∀ v ∈ Work.GM.S3.pbox, |Work.GM.S3.phas (m₁, m₂, m₃) v| ≤
        (Submission.LargeValues.M N) ^ η / (N : ℝ) → v.2 / v.1 ∈ Set.Icc (1 / 2 : ℝ) 2) :
    (∫ v in Work.GM.S3.pbox, (if |Work.GM.S3.phas (m₁, m₂, m₃) v| ≤
        (Submission.LargeValues.M N) ^ η / (N : ℝ) then ‖Work.GM.S3.Rprod W v‖ else 0))
      ≤ Real.sqrt 2 * (∫ v in (1 / 2 : ℝ)..2, ‖Submission.GM.Rfun W v‖ *
            Work.GM.S3.Rtilde W N B ψ₁ ψ₂ (Work.GM.S3.arg1 m₁ (-m₂) m₃ v) *
            Work.GM.S3.Rtilde W N B ψ₁ ψ₂ (Work.GM.S3.arg2 m₁ (-m₂) m₃ v)) / ((N : ℝ) * B) := by
  classical
  -- ## 0. positivity of the parameters
  have hNne : (N : ℝ) ≠ 0 := by
    intro h; rw [h, zero_mul] at hB; exact lt_irrefl 0 hB
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_le_of_ne (Nat.cast_nonneg N) (Ne.symm hNne)
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (by simpa using hNne)
  have hBpos : 0 < B := by
    have h := div_pos hB hNpos
    rwa [mul_div_cancel_left₀ B hNne] at h
  have hMpos : 0 < Submission.LargeValues.M N := Submission.LargeValues.M_pos hN1
  have hMηpos : 0 < (Submission.LargeValues.M N) ^ η := Real.rpow_pos_of_pos hMpos η
  have hm2pos : 0 < |((m₂ : ℤ) : ℝ)| := by
    have h1 : 0 < |((m₂ : ℤ) : ℝ)| / 2 := lt_of_lt_of_le (mul_pos hBpos hMηpos) hspace
    linarith
  have hm2ne : ((m₂ : ℤ) : ℝ) ≠ 0 := abs_pos.mp hm2pos
  set c : ℝ := (Submission.LargeValues.M N) ^ η / (N : ℝ) with hcdef
  set δ : ℝ := (Submission.LargeValues.M N) ^ η / ((N : ℝ) * |((m₂ : ℤ) : ℝ)|) with hδdef
  have hδ0 : 0 ≤ δ := by rw [hδdef]; positivity
  have hδle : δ ≤ 1 / (2 * ((N : ℝ) * B)) := by
    rw [hδdef, div_le_div_iff₀ (by positivity) (by positivity)]
    have h2 : 2 * (B * (Submission.LargeValues.M N) ^ η) ≤ |((m₂ : ℤ) : ℝ)| := by linarith
    have h3 : 2 * (B * (Submission.LargeValues.M N) ^ η) * (N : ℝ)
        ≤ |((m₂ : ℤ) : ℝ)| * (N : ℝ) := mul_le_mul_of_nonneg_right h2 (le_of_lt hNpos)
    linarith [h3]
  have hcdelta : |((m₂ : ℤ) : ℝ)| * δ = c := by
    rw [hδdef, hcdef]; field_simp
  -- ## 1. `hgood` in the form consumed by the window estimate
  have hgood' : ∀ x : ℝ, x ∈ Set.Icc (1 / 2 : ℝ) 2 → ∀ u : ℝ,
      x * u ∈ Set.Icc (1 / 2 : ℝ) 2 → |x * u - wcen m₁ m₂ m₃ x| ≤ δ →
      u ∈ Set.Icc (1 / 2 : ℝ) 2 := by
    intro x hx u hxu hw
    have hxne : x ≠ 0 := by linarith [hx.1]
    have hval := hgood (x, x * u) (by rw [pbox]; exact ⟨hx, hxu⟩) ?_
    · rwa [mul_div_cancel_left₀ u hxne] at hval
    · rw [phas_eq_wcen m₁ m₂ m₃ hm2ne, abs_mul, ← hcdelta]
      exact mul_le_mul_of_nonneg_left hw (abs_nonneg _)
  -- ## 2. the integrand and its integrability
  set F : ℝ × ℝ → ℝ := fun v => if |phas (m₁, m₂, m₃) v| ≤ c then ‖Rprod W v‖ else 0 with hFdef
  have hFmeas : Measurable F := by
    rw [hFdef]
    refine Measurable.ite ?_ ?_ measurable_const
    · have hcont : Continuous fun v : ℝ × ℝ => |phas (m₁, m₂, m₃) v| := by
        unfold phas; fun_prop
      exact (isClosed_le hcont continuous_const).measurableSet
    · exact (Rprod_measurable W).norm
  have hInt : IntegrableOn F (Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (1 / 2 : ℝ) 2) volume := by
    refine MeasureTheory.IntegrableOn.of_bound ?_ ?_ (C := (W.card : ℝ) ^ 3) ?_
    · exact (isCompact_Icc.prod isCompact_Icc).measure_lt_top
    · exact hFmeas.aestronglyMeasurable.mono_measure Measure.restrict_le_self
    · refine Filter.Eventually.of_forall fun v => ?_
      simp only [hFdef]
      by_cases h : |phas (m₁, m₂, m₃) v| ≤ c
      · rw [if_pos h, Real.norm_of_nonneg (norm_nonneg _)]; exact norm_Rprod_le W v
      · rw [if_neg h]; simp
  have hFub : (∫ v in pbox, F v) = ∫ x in Set.Icc (1 / 2 : ℝ) 2,
      ∫ y in Set.Icc (1 / 2 : ℝ) 2, F (x, y) := by
    rw [pbox]
    exact MeasureTheory.setIntegral_prod F hInt
  -- ## 3. pointwise rewriting of the inner integrand
  have hkey : ∀ x y : ℝ, x ∈ Set.Icc (1 / 2 : ℝ) 2 → y ∈ Set.Icc (1 / 2 : ℝ) 2 →
      F (x, y) = ‖Rfun W x‖ *
        (wwin m₁ m₂ m₃ δ x).indicator (fun y => ‖Rfun W (y / x)‖ * ‖Rfun W y‖) y := by
    intro x y hx hy
    have hyne : y ≠ 0 := by linarith [hy.1]
    have hyw : (y ∈ wwin m₁ m₂ m₃ δ x) ↔ |y - wcen m₁ m₂ m₃ x| ≤ δ := by
      rw [wwin]
      simp only [Set.mem_inter_iff, Set.mem_Icc]
      constructor
      · rintro ⟨-, h2, h3⟩
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      · intro h
        exact ⟨hy, by linarith [(abs_le.mp h).1], by linarith [(abs_le.mp h).2]⟩
    have hcond : (|phas (m₁, m₂, m₃) (x, y)| ≤ c) ↔ |y - wcen m₁ m₂ m₃ x| ≤ δ := by
      rw [phas_eq_wcen m₁ m₂ m₃ hm2ne, abs_mul]
      constructor
      · intro h
        rw [← hcdelta] at h
        exact (mul_le_mul_iff_of_pos_left hm2pos).mp h
      · intro h
        rw [← hcdelta]
        exact mul_le_mul_of_nonneg_left h (abs_nonneg _)
    have hRp : ‖Rprod W (x, y)‖ = ‖Rfun W x‖ * ‖Rfun W (y / x)‖ * ‖Rfun W y‖ := by
      simp only [Rprod, norm_mul, Rfun_norm_one_div W (v := y) hyne]
    simp only [hFdef]
    by_cases h : |phas (m₁, m₂, m₃) (x, y)| ≤ c
    · rw [if_pos h, hRp, Set.indicator_of_mem (hyw.mpr (hcond.mp h))]
      ring
    · rw [if_neg h, Set.indicator_of_notMem (fun hh => h (hcond.mpr (hyw.mp hh)))]
      ring
  -- ## 4. the per-`x` bound
  have hinner : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 2, (∫ y in Set.Icc (1 / 2 : ℝ) 2, F (x, y)) ≤
      ‖Rfun W x‖ * (Real.sqrt 2 * Rtilde W N B ψ₁ ψ₂ (arg1 m₁ (-m₂) m₃ x) *
        Rtilde W N B ψ₁ ψ₂ (arg2 m₁ (-m₂) m₃ x) / ((N : ℝ) * B)) := by
    intro x hx
    have heq : (∫ y in Set.Icc (1 / 2 : ℝ) 2, F (x, y))
        = ∫ y in Set.Icc (1 / 2 : ℝ) 2, ‖Rfun W x‖ *
            (wwin m₁ m₂ m₃ δ x).indicator (fun y => ‖Rfun W (y / x)‖ * ‖Rfun W y‖) y := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      intro y hy
      exact hkey x y hx hy
    have hrew : (∫ y in Set.Icc (1 / 2 : ℝ) 2, F (x, y))
        = ‖Rfun W x‖ * ∫ y in wwin m₁ m₂ m₃ δ x, ‖Rfun W (y / x)‖ * ‖Rfun W y‖ := by
      rw [heq, setIntegral_const_mul' ‖Rfun W x‖
        ((wwin m₁ m₂ m₃ δ x).indicator (fun y => ‖Rfun W (y / x)‖ * ‖Rfun W y‖))]
      congr 1
      exact setIntegral_indicator_of_subset (measurableSet_wwin m₁ m₂ m₃ δ x)
        (wwin_subset_Icc m₁ m₂ m₃ δ x) _
    rw [hrew]
    exact mul_le_mul_of_nonneg_left
      (window_pair_bound hC₀ h₁ h₂ hψ₁ge hψ₂ge hB hδ0 hδle hx (hgood' x hx)) (norm_nonneg _)
  -- ## 5. the outer comparison
  have hmono : (∫ x in Set.Icc (1 / 2 : ℝ) 2, ∫ y in Set.Icc (1 / 2 : ℝ) 2, F (x, y))
      ≤ ∫ x in Set.Icc (1 / 2 : ℝ) 2, ‖Rfun W x‖ *
          (Real.sqrt 2 * Rtilde W N B ψ₁ ψ₂ (arg1 m₁ (-m₂) m₃ x) *
            Rtilde W N B ψ₁ ψ₂ (arg2 m₁ (-m₂) m₃ x) / ((N : ℝ) * B)) := by
    apply MeasureTheory.setIntegral_mono_of_nonneg
    · intro x hx
      exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun y hy => by simp only [hFdef]; split_ifs <;> positivity)
    · exact hinner
    · obtain ⟨K, hK0, hK⟩ := Rtilde_le_const (W := W) (N := N) (B := B) (C₀ := C₀) h₁ h₂
        (le_of_lt hB)
      have hRc : Continuous fun u : ℝ => Rtilde W N B ψ₁ ψ₂ u :=
        Real.continuous_sqrt.comp (RtildeSq_continuous W N B C₀ ψ₁ ψ₂ h₁ h₂)
      have ha1 : Measurable fun x : ℝ => arg1 m₁ (-m₂) m₃ x := by unfold arg1; fun_prop
      have ha2 : Measurable fun x : ℝ => arg2 m₁ (-m₂) m₃ x := by unfold arg2; fun_prop
      have hm1 : Measurable fun x : ℝ => Rtilde W N B ψ₁ ψ₂ (arg1 m₁ (-m₂) m₃ x) :=
        hRc.measurable.comp ha1
      have hm2 : Measurable fun x : ℝ => Rtilde W N B ψ₁ ψ₂ (arg2 m₁ (-m₂) m₃ x) :=
        hRc.measurable.comp ha2
      have hgm : Measurable fun x : ℝ => ‖Rfun W x‖ *
          (Real.sqrt 2 * Rtilde W N B ψ₁ ψ₂ (arg1 m₁ (-m₂) m₃ x) *
            Rtilde W N B ψ₁ ψ₂ (arg2 m₁ (-m₂) m₃ x) / ((N : ℝ) * B)) :=
        (Rfun_measurable W).norm.mul
          (((measurable_const.mul hm1).mul hm2).div measurable_const)
      refine MeasureTheory.IntegrableOn.of_bound (isCompact_Icc.measure_lt_top) ?_
        (C := (W.card : ℝ) * (Real.sqrt 2 * K * K / ((N : ℝ) * B))) ?_
      · exact hgm.aestronglyMeasurable.mono_measure Measure.restrict_le_self
      · refine Filter.Eventually.of_forall fun x => ?_
        have hA0 : 0 ≤ Rtilde W N B ψ₁ ψ₂ (arg1 m₁ (-m₂) m₃ x) := Rtilde_nonneg W N B ψ₁ ψ₂ _
        have hB0 : 0 ≤ Rtilde W N B ψ₁ ψ₂ (arg2 m₁ (-m₂) m₃ x) := Rtilde_nonneg W N B ψ₁ ψ₂ _
        have hA1 : Rtilde W N B ψ₁ ψ₂ (arg1 m₁ (-m₂) m₃ x) ≤ K := hK _
        have hB1 : Rtilde W N B ψ₁ ψ₂ (arg2 m₁ (-m₂) m₃ x) ≤ K := hK _
        have hgnn : 0 ≤ ‖Rfun W x‖ * (Real.sqrt 2 * Rtilde W N B ψ₁ ψ₂ (arg1 m₁ (-m₂) m₃ x) *
            Rtilde W N B ψ₁ ψ₂ (arg2 m₁ (-m₂) m₃ x) / ((N : ℝ) * B)) := by positivity
        rw [Real.norm_of_nonneg hgnn]
        have hb : Real.sqrt 2 * Rtilde W N B ψ₁ ψ₂ (arg1 m₁ (-m₂) m₃ x) *
              Rtilde W N B ψ₁ ψ₂ (arg2 m₁ (-m₂) m₃ x) / ((N : ℝ) * B)
            ≤ Real.sqrt 2 * K * K / ((N : ℝ) * B) := by
          gcongr
        exact mul_le_mul (Rfun_norm_le_card W x) hb (by positivity) (Nat.cast_nonneg _)
  -- ## 6. the final rewriting into the interval integral
  have hfinal : (∫ x in Set.Icc (1 / 2 : ℝ) 2, ‖Rfun W x‖ *
          (Real.sqrt 2 * Rtilde W N B ψ₁ ψ₂ (arg1 m₁ (-m₂) m₃ x) *
            Rtilde W N B ψ₁ ψ₂ (arg2 m₁ (-m₂) m₃ x) / ((N : ℝ) * B)))
      = Real.sqrt 2 * (∫ v in (1 / 2 : ℝ)..2, ‖Rfun W v‖ *
            Rtilde W N B ψ₁ ψ₂ (arg1 m₁ (-m₂) m₃ v) *
            Rtilde W N B ψ₁ ψ₂ (arg2 m₁ (-m₂) m₃ v)) / ((N : ℝ) * B) := by
    have hp : ∀ x : ℝ, ‖Rfun W x‖ * (Real.sqrt 2 * Rtilde W N B ψ₁ ψ₂ (arg1 m₁ (-m₂) m₃ x) *
            Rtilde W N B ψ₁ ψ₂ (arg2 m₁ (-m₂) m₃ x) / ((N : ℝ) * B))
        = (Real.sqrt 2 / ((N : ℝ) * B)) * (‖Rfun W x‖ *
            Rtilde W N B ψ₁ ψ₂ (arg1 m₁ (-m₂) m₃ x) *
            Rtilde W N B ψ₁ ψ₂ (arg2 m₁ (-m₂) m₃ x)) := by
      intro x; ring
    rw [show (fun x : ℝ => ‖Rfun W x‖ * (Real.sqrt 2 * Rtilde W N B ψ₁ ψ₂ (arg1 m₁ (-m₂) m₃ x) *
            Rtilde W N B ψ₁ ψ₂ (arg2 m₁ (-m₂) m₃ x) / ((N : ℝ) * B)))
        = fun x : ℝ => (Real.sqrt 2 / ((N : ℝ) * B)) * (‖Rfun W x‖ *
            Rtilde W N B ψ₁ ψ₂ (arg1 m₁ (-m₂) m₃ x) *
            Rtilde W N B ψ₁ ψ₂ (arg2 m₁ (-m₂) m₃ x)) from funext hp]
    rw [setIntegral_const_mul']
    rw [setIntegral_Icc_eq_intervalIntegral]
    ring
  calc (∫ v in pbox, (if |phas (m₁, m₂, m₃) v| ≤
          (Submission.LargeValues.M N) ^ η / (N : ℝ) then ‖Rprod W v‖ else 0))
      = ∫ v in pbox, F v := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_pbox
        intro v hv
        simp only [hFdef]
        rw [hcdef]
    _ = ∫ x in Set.Icc (1 / 2 : ℝ) 2, ∫ y in Set.Icc (1 / 2 : ℝ) 2, F (x, y) := hFub
    _ ≤ ∫ x in Set.Icc (1 / 2 : ℝ) 2, ‖Rfun W x‖ *
          (Real.sqrt 2 * Rtilde W N B ψ₁ ψ₂ (arg1 m₁ (-m₂) m₃ x) *
            Rtilde W N B ψ₁ ψ₂ (arg2 m₁ (-m₂) m₃ x) / ((N : ℝ) * B)) := hmono
    _ = Real.sqrt 2 * (∫ v in (1 / 2 : ℝ)..2, ‖Rfun W v‖ *
            Rtilde W N B ψ₁ ψ₂ (arg1 m₁ (-m₂) m₃ v) *
            Rtilde W N B ψ₁ ψ₂ (arg2 m₁ (-m₂) m₃ v)) / ((N : ℝ) * B) := hfinal

end Work.GM.S3
