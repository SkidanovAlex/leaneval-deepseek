import Mathlib
import Submission.Work.GM.S3.window_defs

namespace Work.GM.S3

open MeasureTheory
open scoped Pointwise

/-- Elementary square-root arithmetic behind `window_pair_bound`: if `A ≤ P²/c`, `Bq ≤ Q²/c`
with `P, Q, c ≥ 0` (`c > 0`) and `0 < x ≤ 2`, then `√(x A) √Bq ≤ √2 P Q / c`. -/
private lemma sqrt_pair_le {x A Bq P Q c : ℝ} (hx0 : 0 < x) (hx2 : x ≤ 2) (hc0 : 0 < c)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hA : A ≤ P ^ 2 / c) (hBq : Bq ≤ Q ^ 2 / c) :
    Real.sqrt (x * A) * Real.sqrt Bq ≤ Real.sqrt 2 * P * Q / c := by
  have h1 : Real.sqrt (x * A) ≤ Real.sqrt (x * (P ^ 2 / c)) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hA (le_of_lt hx0))
  have h2 : Real.sqrt Bq ≤ Real.sqrt (Q ^ 2 / c) := Real.sqrt_le_sqrt hBq
  have h3 : Real.sqrt (x * (P ^ 2 / c)) * Real.sqrt (Q ^ 2 / c) ≤ Real.sqrt 2 * P * Q / c := by
    rw [Real.sqrt_mul (le_of_lt hx0) (P ^ 2 / c), Real.sqrt_div' (P ^ 2) (le_of_lt hc0),
      Real.sqrt_sq hP, Real.sqrt_div' (Q ^ 2) (le_of_lt hc0), Real.sqrt_sq hQ]
    have e : Real.sqrt x * (P / Real.sqrt c) * (Q / Real.sqrt c) = Real.sqrt x * P * Q / c := by
      field_simp
      rw [Real.sq_sqrt (le_of_lt hc0)]
      ring
    rw [e]
    rw [mul_assoc, mul_assoc]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hx2) (mul_nonneg hP hQ)) hc0.le
  calc Real.sqrt (x * A) * Real.sqrt Bq
      ≤ Real.sqrt (x * (P ^ 2 / c)) * Real.sqrt (Q ^ 2 / c) :=
        mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt 2 * P * Q / c := h3

/-- GM Prop 7.2, the per-`m` window majorisation (with the `m₂ ↦ -m₂` reflection of GM 10.1).

Let `wcen m₁ m₂ m₃ x = -(m₁x + m₃)/m₂` and `wwin m₁ m₂ m₃ δ x = [1/2,2] ∩ [wcen - δ, wcen + δ]`
(defined in `Submission.Work.GM.S3.window_defs`).  For `x ∈ [1/2,2]`, `δ ≥ 0`, `δ ≤ 1/(2(N B))`
and a `good` hypothesis saying that the pre-image of the window under `u ↦ x·u` stays in
`[1/2,2]`, the Cauchy–Schwarz/window-majorisation step of GM 7.2 holds:

`∫_{wwin} ‖R(y/x)‖‖R(y)‖ dy ≤ √2 R̃(wcen/x) R̃(wcen)/(N B)`

where `R̃ = Rtilde W N B ψ₁ ψ₂`.  Proof route: Cauchy–Schwarz in `y` (`set_integral_mul_le_sqrt`
in `window_defs`), substitute `u = y/x` in the first `L²` factor (`∫_J ‖R(y/x)‖² = x ∫_{J/x} ‖R u‖²`
via `MeasureTheory.Measure.integral_comp_div`), bound both `L²` factors by `set_normSq_le_Rtilde`
(GM 7.2's window majorisation, in `prop72_core`) applied to `wwin` (centre `wcen`, radius
`δ ≤ 1/(2NB)`) and to its scaled pre-image (centre `wcen/x`, radius `δ/x ≤ 1/(N B)`, needs `hgood`
for the `[1/2,2]`-confinement), then `√(x A) √B ≤ √2 √(AB)` using `x ≤ 2`. -/
theorem window_pair_bound {W : Finset ℝ} {N : ℕ} {B δ C₀ : ℝ} {ψ₁ ψ₂ : ℝ → ℝ}
    {m₁ m₂ m₃ : ℤ}
    (hC₀ : 1 ≤ C₀) (h₁ : Work.GM.S3.IsBumpAtZero ψ₁ C₀) (h₂ : Work.GM.S3.IsBumpAtOne ψ₂ C₀)
    (hψ₁ge : ∀ x, |x| ≤ 1 → 1 ≤ ψ₁ x)
    (hψ₂ge : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 2, 1 ≤ ψ₂ x)
    (hB : 0 < (N : ℝ) * B)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / (2 * ((N : ℝ) * B)))
    {x : ℝ} (hx : x ∈ Set.Icc (1 / 2 : ℝ) 2)
    (hgood : ∀ u : ℝ, x * u ∈ Set.Icc (1 / 2 : ℝ) 2 →
        |x * u - Work.GM.S3.wcen m₁ m₂ m₃ x| ≤ δ → u ∈ Set.Icc (1 / 2 : ℝ) 2) :
    ∫ y in Work.GM.S3.wwin m₁ m₂ m₃ δ x,
        ‖Submission.GM.Rfun W (y / x)‖ * ‖Submission.GM.Rfun W y‖
      ≤ Real.sqrt 2 * Work.GM.S3.Rtilde W N B ψ₁ ψ₂ (Work.GM.S3.arg1 m₁ (-m₂) m₃ x) *
          Work.GM.S3.Rtilde W N B ψ₁ ψ₂ (Work.GM.S3.arg2 m₁ (-m₂) m₃ x) / ((N : ℝ) * B) := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx.1
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have hc : 0 < (N : ℝ) * B := hB
  set S : Set ℝ := Work.GM.S3.wwin m₁ m₂ m₃ δ x with hSdef
  set T : Set ℝ := x⁻¹ • S with hTdef
  have hSmeas : MeasurableSet S := by
    rw [hSdef]; exact Work.GM.S3.measurableSet_wwin m₁ m₂ m₃ δ x
  have hSfin : volume S < ⊤ := by
    rw [hSdef]; exact Work.GM.S3.volume_wwin_lt_top m₁ m₂ m₃ δ x
  have hTmeas : MeasurableSet T := by rw [hTdef]; exact hSmeas.const_smul₀ x⁻¹
  have hSmem : ∀ y ∈ S, y ∈ Set.Icc (1 / 2 : ℝ) 2 ∧ |y - Work.GM.S3.wcen m₁ m₂ m₃ x| ≤ δ := by
    intro y hy
    simp only [hSdef, Work.GM.S3.wwin, Set.mem_inter_iff, Set.mem_Icc] at hy
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hy
    exact ⟨⟨h1, h2⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  have hTmem : ∀ u ∈ T, x * u ∈ Set.Icc (1 / 2 : ℝ) 2 ∧
      |x * u - Work.GM.S3.wcen m₁ m₂ m₃ x| ≤ δ := by
    intro u hu
    rw [hTdef] at hu
    rw [Set.mem_inv_smul_set_iff₀ hxne S u] at hu
    have hu2 : x * u ∈ S := by simpa [smul_eq_mul] using hu
    exact hSmem (x * u) hu2
  have hNBδ : (N : ℝ) * B * δ ≤ 1 / 2 := by
    have h4 : δ * (2 * ((N : ℝ) * B)) ≤ 1 := (le_div_iff₀ (by positivity)).mp hδ
    nlinarith [h4, hc]
  have hSbdd : ∀ y ∈ S, |(N : ℝ) * B * (Work.GM.S3.wcen m₁ m₂ m₃ x - y)| ≤ 1 := by
    intro y hy
    obtain ⟨-, hyl⟩ := hSmem y hy
    have h6 : |Work.GM.S3.wcen m₁ m₂ m₃ x - y| ≤ δ := by rw [abs_sub_comm]; exact hyl
    have h7 : (N : ℝ) * B * |Work.GM.S3.wcen m₁ m₂ m₃ x - y| ≤ (N : ℝ) * B * δ :=
      mul_le_mul_of_nonneg_left h6 hc.le
    calc |(N : ℝ) * B * (Work.GM.S3.wcen m₁ m₂ m₃ x - y)|
        = (N : ℝ) * B * |Work.GM.S3.wcen m₁ m₂ m₃ x - y| := by rw [abs_mul, abs_of_pos hc]
      _ ≤ 1 := by linarith
  have hTbdd : ∀ u ∈ T, |(N : ℝ) * B * (Work.GM.S3.wcen m₁ m₂ m₃ x / x - u)| ≤ 1 := by
    intro u hu
    obtain ⟨-, huδ⟩ := hTmem u hu
    have hdiv : |Work.GM.S3.wcen m₁ m₂ m₃ x / x - u| ≤ δ / x := by
      have heq : Work.GM.S3.wcen m₁ m₂ m₃ x / x - u
          = -(x * u - Work.GM.S3.wcen m₁ m₂ m₃ x) / x := by
        field_simp
        ring
      rw [heq, abs_div, abs_neg, abs_of_pos hxpos]
      exact (div_le_div_iff_of_pos_right hxpos).mpr huδ
    have h6 : (N : ℝ) * B * |Work.GM.S3.wcen m₁ m₂ m₃ x / x - u| ≤ (N : ℝ) * B * (δ / x) :=
      mul_le_mul_of_nonneg_left hdiv hc.le
    have h8 : (N : ℝ) * B * δ ≤ x := by linarith [hx.1]
    have h9 : (N : ℝ) * B * δ / x ≤ 1 := (div_le_one hxpos).mpr h8
    have h7 : (N : ℝ) * B * (δ / x) ≤ 1 := by simpa [mul_div_assoc] using h9
    calc |(N : ℝ) * B * (Work.GM.S3.wcen m₁ m₂ m₃ x / x - u)|
        = (N : ℝ) * B * |Work.GM.S3.wcen m₁ m₂ m₃ x / x - u| := by rw [abs_mul, abs_of_pos hc]
      _ ≤ 1 := by linarith
  have hS_int : ∫ y in S, ‖Submission.GM.Rfun W y‖ ^ 2
      ≤ Work.GM.S3.Rtilde W N B ψ₁ ψ₂ (Work.GM.S3.wcen m₁ m₂ m₃ x) ^ 2 / ((N : ℝ) * B) :=
    Work.GM.S3.set_normSq_le_Rtilde hC₀ h₁ h₂ hB hψ₁ge hψ₂ge (Work.GM.S3.wcen m₁ m₂ m₃ x)
      hSmeas hSbdd (fun u hu => (hSmem u hu).1)
  have hT_int : ∫ u in T, ‖Submission.GM.Rfun W u‖ ^ 2
      ≤ Work.GM.S3.Rtilde W N B ψ₁ ψ₂ (Work.GM.S3.wcen m₁ m₂ m₃ x / x) ^ 2
          / ((N : ℝ) * B) :=
    Work.GM.S3.set_normSq_le_Rtilde hC₀ h₁ h₂ hB hψ₁ge hψ₂ge
      (Work.GM.S3.wcen m₁ m₂ m₃ x / x) hTmeas hTbdd
      (fun u hu => hgood u (hTmem u hu).1 (hTmem u hu).2)
  have hf_meas : AEStronglyMeasurable (fun y : ℝ => ‖Submission.GM.Rfun W (y / x)‖)
      (volume.restrict S) :=
    (((Work.GM.S3.Rfun_measurable W).comp (measurable_id.div_const x)).norm).aestronglyMeasurable
  have hg_meas : AEStronglyMeasurable (fun y : ℝ => ‖Submission.GM.Rfun W y‖)
      (volume.restrict S) := (Work.GM.S3.Rfun_measurable W).norm.aestronglyMeasurable
  have hfC : ∀ᵐ y ∂(volume.restrict S),
      ‖(fun y : ℝ => ‖Submission.GM.Rfun W (y / x)‖) y‖ ≤ (W.card : ℝ) :=
    Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact Work.GM.S3.Rfun_norm_le_card W _
  have hgC : ∀ᵐ y ∂(volume.restrict S),
      ‖(fun y : ℝ => ‖Submission.GM.Rfun W y‖) y‖ ≤ (W.card : ℝ) :=
    Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact Work.GM.S3.Rfun_norm_le_card W _
  have hCS := Work.GM.S3.set_integral_mul_le_sqrt (s := S)
    (f := fun y : ℝ => ‖Submission.GM.Rfun W (y / x)‖)
    (g := fun y : ℝ => ‖Submission.GM.Rfun W y‖)
    hSfin (Filter.Eventually.of_forall fun y => norm_nonneg _)
    (Filter.Eventually.of_forall fun y => norm_nonneg _) hf_meas hg_meas hfC hgC
  have hsub : ∫ y in S, ‖Submission.GM.Rfun W (y / x)‖ ^ 2
      = x * ∫ u in T, ‖Submission.GM.Rfun W u‖ ^ 2 := by
    have hkey := MeasureTheory.Measure.setIntegral_comp_smul (μ := volume)
      (f := fun u : ℝ => ‖Submission.GM.Rfun W u‖ ^ 2) (s := S) (R := x⁻¹) (inv_ne_zero hxne)
    have hL : ∫ y in S, ‖Submission.GM.Rfun W (y / x)‖ ^ 2
        = ∫ y in S, (fun u : ℝ => ‖Submission.GM.Rfun W u‖ ^ 2) (x⁻¹ • y) := by
      refine MeasureTheory.setIntegral_congr_fun hSmeas fun y hy => ?_
      have h : x⁻¹ • y = y / x := by rw [smul_eq_mul, div_eq_mul_inv, mul_comm]
      rw [h]
    rw [hL, hkey, hTdef]
    simp [smul_eq_mul, abs_of_pos hxpos]
  have hR1nn : 0 ≤ Work.GM.S3.Rtilde W N B ψ₁ ψ₂ (Work.GM.S3.wcen m₁ m₂ m₃ x / x) :=
    Work.GM.S3.Rtilde_nonneg W N B ψ₁ ψ₂ _
  have hR2nn : 0 ≤ Work.GM.S3.Rtilde W N B ψ₁ ψ₂ (Work.GM.S3.wcen m₁ m₂ m₃ x) :=
    Work.GM.S3.Rtilde_nonneg W N B ψ₁ ψ₂ _
  have harith := sqrt_pair_le (x := x) (A := ∫ u in T, ‖Submission.GM.Rfun W u‖ ^ 2)
    (Bq := ∫ y in S, ‖Submission.GM.Rfun W y‖ ^ 2)
    (P := Work.GM.S3.Rtilde W N B ψ₁ ψ₂ (Work.GM.S3.wcen m₁ m₂ m₃ x / x))
    (Q := Work.GM.S3.Rtilde W N B ψ₁ ψ₂ (Work.GM.S3.wcen m₁ m₂ m₃ x)) (c := (N : ℝ) * B)
    hxpos hx.2 hc hR1nn hR2nn hT_int hS_int
  calc ∫ y in S, ‖Submission.GM.Rfun W (y / x)‖ * ‖Submission.GM.Rfun W y‖
      ≤ Real.sqrt (∫ y in S, ‖Submission.GM.Rfun W (y / x)‖ ^ 2) *
          Real.sqrt (∫ y in S, ‖Submission.GM.Rfun W y‖ ^ 2) := hCS
    _ = Real.sqrt (x * ∫ u in T, ‖Submission.GM.Rfun W u‖ ^ 2) *
          Real.sqrt (∫ y in S, ‖Submission.GM.Rfun W y‖ ^ 2) := by rw [hsub]
    _ ≤ Real.sqrt 2 * Work.GM.S3.Rtilde W N B ψ₁ ψ₂ (Work.GM.S3.arg1 m₁ (-m₂) m₃ x) *
          Work.GM.S3.Rtilde W N B ψ₁ ψ₂ (Work.GM.S3.arg2 m₁ (-m₂) m₃ x) / ((N : ℝ) * B) := by
        rw [Work.GM.S3.arg1_eq_wcen, Work.GM.S3.arg2_eq_wcen]
        exact harith

end Work.GM.S3
