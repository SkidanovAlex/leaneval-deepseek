import Mathlib
import Submission.Work.GM.S3.Base
import Submission.Work.GM.S3.Defs
import Submission.Work.GM.S3.prop71_defs
import Submission.Work.GM.S3.prop101_defs
import Submission.Work.GM.S3.prop72_core

/-!
# Notation for the per-`m` estimate of GM Prop 7.2 (`window_integral_le_Rtilde`)

The constraint `|m₁v₁ + m₂v₂ + m₃| ≤ (M N)^η/N` of GM Proposition 7.1 is equivalent to
`|v₂ - w| ≤ δ` with

* `wcen m₁ m₂ m₃ v₁ = -(m₁v₁ + m₃)/m₂` — the centre of the constraint window in `v₂`, and also
  (divided by `v₁`) the centre of the image window in `v₂/v₁`;
* `δ = (M N)^η/(N |m₂|)` — its half width.

The two `R̃`-arguments of GM 10.1 with the reflection `m₂ ↦ -m₂` are exactly `wcen/v₁` and `wcen`.
-/

namespace Work.GM.S3

open Complex Finset MeasureTheory
open scoped BigOperators
open Submission.GM (Rfun)

/-- `wcen m₁ m₂ m₃ v = -(m₁ v + m₃)/m₂`, the centre of the constraint window of GM Prop 7.1. -/
noncomputable def wcen (m₁ m₂ m₃ : ℤ) (v : ℝ) : ℝ :=
  -(((m₁ : ℝ) * v + (m₃ : ℝ)) / ((m₂ : ℤ) : ℝ))

/-- The constraint window of GM Prop 7.1 in the `v₂` variable, within `pbox`:
`[1/2,2] ∩ [wcen - δ, wcen + δ]`. -/
noncomputable def wwin (m₁ m₂ m₃ : ℤ) (δ x : ℝ) : Set ℝ :=
  Set.Icc (1 / 2 : ℝ) 2 ∩ Set.Icc (wcen m₁ m₂ m₃ x - δ) (wcen m₁ m₂ m₃ x + δ)

theorem wwin_subset_Icc (m₁ m₂ m₃ : ℤ) (δ x : ℝ) :
    wwin m₁ m₂ m₃ δ x ⊆ Set.Icc (1 / 2 : ℝ) 2 := Set.inter_subset_left

theorem measurableSet_wwin (m₁ m₂ m₃ : ℤ) (δ x : ℝ) :
    MeasurableSet (wwin m₁ m₂ m₃ δ x) := measurableSet_Icc.inter measurableSet_Icc

theorem volume_wwin_lt_top (m₁ m₂ m₃ : ℤ) (δ x : ℝ) :
    volume (wwin m₁ m₂ m₃ δ x) < ⊤ := by
  refine lt_of_le_of_lt (measure_mono (wwin_subset_Icc m₁ m₂ m₃ δ x)) ?_
  rw [Real.volume_Icc]
  exact ENNReal.ofReal_lt_top

/-- `arg1 m₁ (-m₂) m₃ v = wcen m₁ m₂ m₃ v / v` (GM 10.1 first argument, reflected). -/
theorem arg1_eq_wcen (m₁ m₂ m₃ : ℤ) (v : ℝ) :
    arg1 m₁ (-m₂) m₃ v = wcen m₁ m₂ m₃ v / v := by
  rw [arg1, wcen, Int.cast_neg]
  field_simp

/-- `arg2 m₁ (-m₂) m₃ v = wcen m₁ m₂ m₃ v` (GM 10.1 second argument, reflected). -/
theorem arg2_eq_wcen (m₁ m₂ m₃ : ℤ) (v : ℝ) :
    arg2 m₁ (-m₂) m₃ v = wcen m₁ m₂ m₃ v := by
  rw [arg2, wcen, Int.cast_neg]
  field_simp

/-- The constraint `|phas| ≤ c` is `|v₂ - wcen| ≤ c/|m₂|`. -/
theorem phas_eq_wcen (m₁ m₂ m₃ : ℤ) {v₁ v₂ : ℝ} (hm₂ : ((m₂ : ℤ) : ℝ) ≠ 0) :
    phas (m₁, m₂, m₃) (v₁, v₂) = ((m₂ : ℤ) : ℝ) * (v₂ - wcen m₁ m₂ m₃ v₁) := by
  rw [phas, wcen]
  field_simp
  ring

/-! ### Elementary algebra -/

theorem two_mul_le_sq_add (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

theorem sq_sqrt_two : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)

/-- `√P √Q ≤ a` as soon as `P Q ≤ a²` and `P, Q, a ≥ 0`. -/
theorem sqrt_mul_sqrt_le_of_mul_le_sq {P Q a : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (ha : 0 ≤ a)
    (h : P * Q ≤ a ^ 2) : Real.sqrt P * Real.sqrt Q ≤ a := by
  rw [← Real.sqrt_mul hP Q]
  exact (Real.sqrt_le_left ha).mpr h

/-! ### Cauchy–Schwarz for set integrals -/

/-- Hölder (hence Cauchy–Schwarz) in the form needed here: on a finite-measure set `s` and for
nonnegative measurable bounded `f, g`, `∫_s f g ≤ √(∫_s f²) √(∫_s g²)`. -/
theorem set_integral_mul_le_sqrt {s : Set ℝ} {f g : ℝ → ℝ} (hsf : volume s < ⊤)
    (hf0 : 0 ≤ᵐ[volume.restrict s] f) (hg0 : 0 ≤ᵐ[volume.restrict s] g)
    (hf : AEStronglyMeasurable f (volume.restrict s))
    (hg : AEStronglyMeasurable g (volume.restrict s))
    {Cf Cg : ℝ} (hfC : ∀ᵐ x ∂(volume.restrict s), ‖f x‖ ≤ Cf)
    (hgC : ∀ᵐ x ∂(volume.restrict s), ‖g x‖ ≤ Cg) :
    ∫ x in s, f x * g x ≤ Real.sqrt (∫ x in s, f x ^ 2) * Real.sqrt (∫ x in s, g x ^ 2) := by
  have hfin : IsFiniteMeasure (volume.restrict s) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  have hpq2 : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict s) (p := 2) (q := 2) hpq2
    hf0 hg0 (MemLp.of_bound hf Cf hfC) (MemLp.of_bound hg Cg hgC)
  simp only [Real.rpow_two] at hH
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact hH

/-! ### The smoothing `R̃` is bounded -/

/-- **`R̃` is bounded.** For `IsBumpAtZero ψ₁`, `IsBumpAtOne ψ₂` and `0 ≤ N B`, the smoothed
`|R|²` is bounded uniformly in the argument (`ψ₂` is supported in the fixed interval `[1/C₀, C₀]`,
where the `ψ₁`-window has length `≤ 2 C₀/(N B)`). -/
theorem Rtilde_le_const {W : Finset ℝ} {N : ℕ} {B C₀ : ℝ} {ψ₁ ψ₂ : ℝ → ℝ}
    (h₁ : IsBumpAtZero ψ₁ C₀) (h₂ : IsBumpAtOne ψ₂ C₀) (hB : 0 ≤ (N : ℝ) * B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u, Rtilde W N B ψ₁ ψ₂ u ≤ K := by
  obtain ⟨c₁, hc₁0, hc₁⟩ := h₁.2.2.2.2 0
  obtain ⟨c₂, hc₂0, hc₂⟩ := h₂.2.2.2.2 0
  simp only [iteratedDeriv_zero] at hc₁ hc₂
  have hC₀1 : 1 ≤ C₀ := by
    have hne : ψ₂ 1 ≠ 0 := by rw [h₂.2.2.2.1]; norm_num
    exact (Set.mem_Icc.mp (h₂.2.2.1 1 hne)).2
  have hCpos : 0 < C₀ := lt_of_lt_of_le one_pos hC₀1
  have h1C : 1 / C₀ ≤ C₀ := by
    have hmem : (1 : ℝ) ∈ Set.Icc (1 / C₀) C₀ := h₂.2.2.1 1 (by rw [h₂.2.2.2.1]; norm_num)
    exact le_trans hmem.1 hmem.2
  set K : ℝ := (((N : ℝ) * B) * c₁ * c₂ * (W.card : ℝ) ^ 2) * (C₀ - 1 / C₀) with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hB hc₁0) hc₂0) (sq_nonneg _))
      (sub_nonneg.mpr h1C)
  refine ⟨Real.sqrt K, Real.sqrt_nonneg _, fun u => ?_⟩
  rw [Rtilde]
  refine Real.sqrt_le_sqrt ?_
  show RtildeSq W N B ψ₁ ψ₂ u ≤ K
  rw [RtildeSq]
  have hInt : (∫ u' : ℝ, (N : ℝ) * B * ψ₁ ((N : ℝ) * B * (u - u')) * ψ₂ u' *
        ‖Rfun W u'‖ ^ 2)
      ≤ ∫ u' : ℝ, (Set.Icc (1 / C₀) C₀).indicator
          (fun _ => ((N : ℝ) * B) * c₁ * c₂ * (W.card : ℝ) ^ 2) u' := by
    refine integral_mono_of_nonneg ?_ ?_ ?_
    · exact Filter.Eventually.of_forall (fun u' =>
        mul_nonneg (mul_nonneg (mul_nonneg hB (h₁.2.1 _)) (h₂.2.1 _)) (sq_nonneg _))
    · rw [MeasureTheory.integrable_indicator_iff measurableSet_Icc]
      exact MeasureTheory.integrableOn_const
        (hs := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    · refine Filter.Eventually.of_forall (fun u' => ?_)
      by_cases hu : u' ∈ Set.Icc (1 / C₀) C₀
      · rw [Set.indicator_of_mem hu]
        have hA : ψ₁ ((N : ℝ) * B * (u - u')) ≤ c₁ := le_trans (le_abs_self _) (hc₁ _)
        have hB' : ψ₂ u' ≤ c₂ := le_trans (le_abs_self _) (hc₂ _)
        have hC : ‖Rfun W u'‖ ^ 2 ≤ (W.card : ℝ) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (Rfun_norm_le_card W u') 2
        have h1 : (N : ℝ) * B * ψ₁ ((N : ℝ) * B * (u - u')) ≤ (N : ℝ) * B * c₁ :=
          mul_le_mul_of_nonneg_left hA hB
        have h2 : ((N : ℝ) * B * ψ₁ ((N : ℝ) * B * (u - u'))) * ψ₂ u' ≤
            ((N : ℝ) * B * c₁) * c₂ :=
          mul_le_mul h1 hB' (h₂.2.1 _) (mul_nonneg hB hc₁0)
        exact mul_le_mul h2 hC (sq_nonneg _) (mul_nonneg (mul_nonneg hB hc₁0) hc₂0)
      · rw [Set.indicator_of_notMem hu]
        have hψ₂ : ψ₂ u' = 0 := by
          by_contra hne
          exact hu (h₂.2.2.1 u' hne)
        simp [hψ₂]
  calc (∫ u' : ℝ, (N : ℝ) * B * ψ₁ ((N : ℝ) * B * (u - u')) * ψ₂ u' * ‖Rfun W u'‖ ^ 2)
      ≤ _ := hInt
    _ = (C₀ - 1 / C₀) * (((N : ℝ) * B) * c₁ * c₂ * (W.card : ℝ) ^ 2) := by
          rw [MeasureTheory.integral_indicator_const _ measurableSet_Icc,
            Real.volume_real_Icc_of_le h1C, smul_eq_mul]
    _ = K := by rw [hK]; ring

theorem Rtilde_nonneg' {W : Finset ℝ} {N : ℕ} {B : ℝ} {ψ₁ ψ₂ : ℝ → ℝ} (u : ℝ) :
    0 ≤ Rtilde W N B ψ₁ ψ₂ u := Rtilde_nonneg W N B ψ₁ ψ₂ u


/-! ### Elementary manipulations of set integrals -/

theorem setIntegral_const_mul' {s : Set ℝ} (c : ℝ) (g : ℝ → ℝ) :
    ∫ y in s, c * g y = c * ∫ y in s, g y := by
  rw [MeasureTheory.integral_const_mul]

theorem setIntegral_indicator_of_subset {s t : Set ℝ} (ht : MeasurableSet t) (hsub : t ⊆ s)
    (g : ℝ → ℝ) : ∫ y in s, t.indicator g y = ∫ y in t, g y := by
  rw [MeasureTheory.setIntegral_indicator ht, Set.inter_eq_right.mpr hsub]

theorem setIntegral_Icc_eq_intervalIntegral (f : ℝ → ℝ) :
    ∫ x in Set.Icc (1 / 2 : ℝ) 2, f x = ∫ x in (1 / 2 : ℝ)..2, f x := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)]

end Work.GM.S3
