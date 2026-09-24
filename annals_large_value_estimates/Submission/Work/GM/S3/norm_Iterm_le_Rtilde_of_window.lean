import Mathlib
import Submission.Work.GM.S3.Base
import Submission.Work.GM.S3.Defs
import Submission.Work.GM.S3.prop71_defs
import Submission.Work.GM.S3.prop101_defs
import Submission.Work.GM.S3.prop72_core
import Submission.Work.GM.S3.prop71_main
import Submission.Work.GM.S3.window_defs
import Submission.Work.GM.S3.window_pair_bound
import Submission.Work.GM.S3.window_integral_le_Rtilde
import Submission.Work.GM.S3.norm_Iterm_le_Rtilde_of_good
import Submission.Work.GM.S3.RtildeSq_continuous

namespace Work.GM.S3

open Complex Finset MeasureTheory
open scoped BigOperators Pointwise
open Submission.GM (Rfun)

/-!
# GM 7.2's per-`m` estimate with a *generalised plateau* `[c₁,c₂] ⊇ [1/2,2]`

The three lemmas below (`set_normSq_le_Rtilde_Icc`, `window_pair_bound_Icc`,
`window_integral_le_Rtilde_Icc`) are the copies of `Work.GM.S3.set_normSq_le_Rtilde`,
`Work.GM.S3.window_pair_bound` and `Work.GM.S3.window_integral_le_Rtilde` in which the plateau
`Set.Icc (1/2) 2` of `ψ₂` is replaced by an arbitrary `Set.Icc c₁ c₂` with `c₁ ≤ 1/2 ≤ 2 ≤ c₂`.
The point is that the "good window" hypothesis then only has to produce `v.2/v.1 ∈ [c₁,c₂]`,
which is weaker; the two places where the interval is used are

* the first `L²` factor, integrated over `wwin m₁ m₂ m₃ δ x ⊆ [1/2,2] ⊆ [c₁,c₂]` (uses `hc₁,hc₂`),
* the second one, integrated over `T = x⁻¹ • wwin ⊆ [c₁,c₂]` (uses `hgood`).

The final theorem `norm_Iterm_le_Rtilde_of_window` is then the proof of
`Work.GM.S3.norm_Iterm_le_Rtilde_of_good` with `window_integral_le_Rtilde_Icc` in place of
`window_integral_le_Rtilde`; the conclusion is unchanged.
-/

/-- **Majorization of a *set* of `‖R‖²` by the smoothing `R̃`**, with the plateau `[1/2,2]` of
`ψ₂` replaced by an arbitrary pair `[c₁,c₂]`: if `ψ₁ ≥ 1` on `|x| ≤ 1`, `ψ₂ ≥ 1` on `[c₁,c₂]`,
`S` is measurable, lies inside the `ψ₁`-window `|NB(x-u)| ≤ 1` of `x` and inside `[c₁,c₂]`, then
`∫_S ‖R u‖² ≤ R̃(x)²/(N B)`.

This is `Work.GM.S3.set_normSq_le_Rtilde` with `Set.Icc (1/2) 2` replaced by `Set.Icc c₁ c₂`
throughout; the interval is used in that proof only to feed `hψ₂ge`. -/
theorem set_normSq_le_Rtilde_Icc {W : Finset ℝ} {N : ℕ} {B : ℝ} {ψ₁ ψ₂ : ℝ → ℝ} {C₀ : ℝ}
    (hC₀ : 1 ≤ C₀) (hψ₁ : IsBumpAtZero ψ₁ C₀) (hψ₂ : IsBumpAtOne ψ₂ C₀)
    (hB : 0 < (N : ℝ) * B) (hψ₁ge : ∀ x, |x| ≤ 1 → 1 ≤ ψ₁ x)
    {c₁ c₂ : ℝ} (hψ₂ge : ∀ x ∈ Set.Icc c₁ c₂, 1 ≤ ψ₂ x)
    (x : ℝ) {S : Set ℝ} (hmeas : MeasurableSet S)
    (hwin : ∀ u ∈ S, |(N : ℝ) * B * (x - u)| ≤ 1)
    (hpos : ∀ u ∈ S, u ∈ Set.Icc c₁ c₂) :
    ∫ u in S, ‖Rfun W u‖ ^ 2 ≤ Rtilde W N B ψ₁ ψ₂ x ^ 2 / ((N : ℝ) * B) := by
  have hψ₁nn : ∀ x, 0 ≤ ψ₁ x := hψ₁.2.1
  have hψ₂nn : ∀ x, 0 ≤ ψ₂ x := hψ₂.2.1
  have hBnn : 0 ≤ (N : ℝ) * B := le_of_lt hB
  have hBpos : 0 ≤ B := by
    by_contra h
    push Not at h
    exact absurd (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg N) h.le) (not_le.mpr hB)
  have hsq : Rtilde W N B ψ₁ ψ₂ x ^ 2 = RtildeSq W N B ψ₁ ψ₂ x :=
    Rtilde_sq W N B ψ₁ ψ₂ x (RtildeSq_nonneg W N B ψ₁ ψ₂ x hψ₁nn hψ₂nn hBpos)
  have hint := RtildeSq_integrable (W := W) (N := N) (B := B) (C₀ := C₀) (x := x)
    hC₀ hψ₁ hψ₂ hB
  have hpt : ∀ u : ℝ, S.indicator (fun u => (N : ℝ) * B * ‖Rfun W u‖ ^ 2) u ≤
        (N : ℝ) * B * ψ₁ ((N : ℝ) * B * (x - u)) * ψ₂ u * ‖Rfun W u‖ ^ 2 := by
    intro u
    by_cases hu : u ∈ S
    · rw [Set.indicator_of_mem hu]
      have h1 : 1 ≤ ψ₁ ((N : ℝ) * B * (x - u)) := hψ₁ge _ (hwin u hu)
      have h2 : 1 ≤ ψ₂ u := hψ₂ge u (hpos u hu)
      calc (N : ℝ) * B * ‖Rfun W u‖ ^ 2
          = (N : ℝ) * B * 1 * 1 * ‖Rfun W u‖ ^ 2 := by ring
        _ ≤ (N : ℝ) * B * ψ₁ ((N : ℝ) * B * (x - u)) * ψ₂ u * ‖Rfun W u‖ ^ 2 := by gcongr
    · rw [Set.indicator_of_notMem hu]
      exact mul_nonneg (mul_nonneg (mul_nonneg hBnn (hψ₁nn _)) (hψ₂nn _)) (sq_nonneg _)
  have hmono : ∫ u : ℝ, S.indicator (fun u => (N : ℝ) * B * ‖Rfun W u‖ ^ 2) u ≤
      ∫ u : ℝ, (N : ℝ) * B * ψ₁ ((N : ℝ) * B * (x - u)) * ψ₂ u * ‖Rfun W u‖ ^ 2 := by
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall (fun u => by
        by_cases hu : u ∈ S
        · rw [Set.indicator_of_mem hu]; positivity
        · rw [Set.indicator_of_notMem hu]; norm_num)
    · simpa using hint
    · exact Filter.Eventually.of_forall hpt
  have hleft : ∫ u : ℝ, S.indicator (fun u => (N : ℝ) * B * ‖Rfun W u‖ ^ 2) u =
      (N : ℝ) * B * ∫ u in S, ‖Rfun W u‖ ^ 2 := by
    rw [MeasureTheory.integral_indicator hmeas, MeasureTheory.integral_const_mul]
  rw [hsq, RtildeSq, le_div_iff₀ hB]
  rw [hleft, mul_comm ((N : ℝ) * B)] at hmono
  exact hmono
private lemma sqrt_pair_le_Icc {x A Bq P Q c : ℝ} (hx0 : 0 < x) (hx2 : x ≤ 2) (hc0 : 0 < c)
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
/-- GM Prop 7.2, the per-`m` window majorisation (with the `m₂ ↦ -m₂` reflection of GM 10.1),
generalised from the plateau `[1/2,2]` of `ψ₂` to a pair `[c₁,c₂]` with `c₁ ≤ 1/2 ≤ 2 ≤ c₂`:
`hψ₂ge` is required on `[c₁,c₂]` and `hgood` only produces `u ∈ [c₁,c₂]`; the first `L²` factor
is bounded on `wwin ⊆ [1/2,2] ⊆ [c₁,c₂]`, the second on `T ⊆ [c₁,c₂]` by `hgood`.

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
theorem window_pair_bound_Icc {W : Finset ℝ} {N : ℕ} {B δ C₀ : ℝ} {ψ₁ ψ₂ : ℝ → ℝ}
    {c₁ c₂ : ℝ} {m₁ m₂ m₃ : ℤ}
    (hc₁ : c₁ ≤ 1 / 2) (hc₂ : 2 ≤ c₂)
    (hC₀ : 1 ≤ C₀) (h₁ : Work.GM.S3.IsBumpAtZero ψ₁ C₀) (h₂ : Work.GM.S3.IsBumpAtOne ψ₂ C₀)
    (hψ₁ge : ∀ x, |x| ≤ 1 → 1 ≤ ψ₁ x)
    (hψ₂ge : ∀ x ∈ Set.Icc c₁ c₂, 1 ≤ ψ₂ x)
    (hB : 0 < (N : ℝ) * B)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / (2 * ((N : ℝ) * B)))
    {x : ℝ} (hx : x ∈ Set.Icc (1 / 2 : ℝ) 2)
    (hgood : ∀ u : ℝ, x * u ∈ Set.Icc (1 / 2 : ℝ) 2 →
        |x * u - Work.GM.S3.wcen m₁ m₂ m₃ x| ≤ δ → u ∈ Set.Icc c₁ c₂) :
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
    Work.GM.S3.set_normSq_le_Rtilde_Icc hC₀ h₁ h₂ hB hψ₁ge hψ₂ge (Work.GM.S3.wcen m₁ m₂ m₃ x)
      hSmeas hSbdd (fun u hu => ⟨le_trans hc₁ (hSmem u hu).1.1, le_trans (hSmem u hu).1.2 hc₂⟩)
  have hT_int : ∫ u in T, ‖Submission.GM.Rfun W u‖ ^ 2
      ≤ Work.GM.S3.Rtilde W N B ψ₁ ψ₂ (Work.GM.S3.wcen m₁ m₂ m₃ x / x) ^ 2
          / ((N : ℝ) * B) :=
    Work.GM.S3.set_normSq_le_Rtilde_Icc hC₀ h₁ h₂ hB hψ₁ge hψ₂ge
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
  have harith := sqrt_pair_le_Icc (x := x) (A := ∫ u in T, ‖Submission.GM.Rfun W u‖ ^ 2)
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
theorem window_integral_le_Rtilde_Icc {W : Finset ℝ} {N : ℕ} {B η : ℝ} {ψ₁ ψ₂ : ℝ → ℝ}
    {C₀ : ℝ} {c₁ c₂ : ℝ}
    (hc₁ : c₁ ≤ 1 / 2) (hc₂ : 2 ≤ c₂)
    (hC₀ : 1 ≤ C₀) (h₁ : Work.GM.S3.IsBumpAtZero ψ₁ C₀) (h₂ : Work.GM.S3.IsBumpAtOne ψ₂ C₀)
    (hψ₁ge : ∀ x, |x| ≤ 1 → 1 ≤ ψ₁ x)
    (hψ₂ge : ∀ x ∈ Set.Icc c₁ c₂, 1 ≤ ψ₂ x)
    (hη : 0 < η) (hB : 0 < (N : ℝ) * B)
    {m₁ m₂ m₃ : ℤ}
    (hspace : B * (Submission.LargeValues.M N) ^ η ≤ |((m₂ : ℤ) : ℝ)| / 2)
    (hgood : ∀ v ∈ Work.GM.S3.pbox, |Work.GM.S3.phas (m₁, m₂, m₃) v| ≤
        (Submission.LargeValues.M N) ^ η / (N : ℝ) → v.2 / v.1 ∈ Set.Icc c₁ c₂) :
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
  -- ## 1. `hgood` in the form consumed by the window estimate (image in `[c₁,c₂]`)
  have hgood' : ∀ x : ℝ, x ∈ Set.Icc (1 / 2 : ℝ) 2 → ∀ u : ℝ,
      x * u ∈ Set.Icc (1 / 2 : ℝ) 2 → |x * u - wcen m₁ m₂ m₃ x| ≤ δ →
      u ∈ Set.Icc c₁ c₂ := by
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
      (window_pair_bound_Icc hc₁ hc₂ hC₀ h₁ h₂ hψ₁ge hψ₂ge hB hδ0 hδle hx (hgood' x hx))
      (norm_nonneg _)
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
/-- The per-`m` estimate of GM 7.2 with the plateau of `ψ₂` **generalised to a larger interval**.
This is `Work.GM.S3.norm_Iterm_le_Rtilde_of_good` with `[1/2,2]` replaced by a pair
`c₁ ≤ 1/2 ≤ 2 ≤ c₂`:

* the hypothesis `ψ₂ ≥ 1` on `[1/2,2]` is strengthened to `ψ₂ ≥ 1` on the larger set `[c₁,c₂]`;
* the "good window" hypothesis becomes `v.2/v.1 ∈ [c₁,c₂]` instead of `∈ [1/2,2]`, i.e. it is
  *weaker*, which is the point: the bumps `ψ₂` of GM 7.2 are existential witnesses and one may take
  `ψ₂ = 1` on a plateau `[c₁,c₂]` strictly containing `[1/2,2]` (subject to the support `[1/4,4]`
  of `IsBumpAtOne ψ₂ 4`), giving the constraint window's image more room.

The conclusion is *unchanged*.  Proof: the proof of `norm_Iterm_le_Rtilde_of_good` with the interval
replaced throughout; only `Work.GM.S3.window_pair_bound` (used through
`Work.GM.S3.window_integral_le_Rtilde`) mentions the interval, applied once to the window
`wwin ⊆ [1/2,2] ⊆ [c₁,c₂]` and once to its scaled image `wwin/v₁ ⊆ [c₁,c₂]` (which is what the
weakened `hgood` supplies).  Restate and reprove that generalised majorisation in your own file if
the original does not apply. -/
theorem norm_Iterm_le_Rtilde_of_window :
    ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ W : Finset ℝ, (∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N)) →
      Submission.GM.Separated W ((Submission.LargeValues.M N) ^ ε) →
    ∀ B : ℝ, ∀ ψ₁ ψ₂ : ℝ → ℝ, Work.GM.S3.IsBumpAtZero ψ₁ 4 → Work.GM.S3.IsBumpAtOne ψ₂ 4 →
      (∀ x, |x| ≤ 1 → 1 ≤ ψ₁ x) → ∀ c₁ c₂ : ℝ, c₁ ≤ 1 / 2 → 2 ≤ c₂ →
      (∀ x ∈ Set.Icc c₁ c₂, 1 ≤ ψ₂ x) →
      0 < (N : ℝ) * B →
    ∀ m₁ m₂ m₃ : ℤ,
      B * (Submission.LargeValues.M N) ^ η ≤ |((m₂ : ℤ) : ℝ)| / 2 →
      (∀ v ∈ Work.GM.S3.pbox, |Work.GM.S3.phas (m₁, m₂, m₃) v| ≤
          (Submission.LargeValues.M N) ^ η / (N : ℝ) → v.2 / v.1 ∈ Set.Icc c₁ c₂) →
      ‖Submission.GM.Iterm N W (m₁, m₂, m₃)‖ ≤
        C * ((N : ℝ) ^ 2 / B) *
          (∫ v in (1 / 2 : ℝ)..2, ‖Submission.GM.Rfun W v‖ *
            Work.GM.S3.Rtilde W N B ψ₁ ψ₂ (Work.GM.S3.arg1 m₁ (-m₂) m₃ v) *
            Work.GM.S3.Rtilde W N B ψ₁ ψ₂ (Work.GM.S3.arg2 m₁ (-m₂) m₃ v))
        + C * (N : ℝ) ^ (-20 : ℤ) := by
  intro ε η hε hη
  obtain ⟨C₁, hC₁pos, N₀₁, hmain71⟩ := prop71_main_window ε η hε hη
  refine ⟨C₁ * Real.sqrt 2, by positivity, max N₀₁ 1, ?_⟩
  intro N hN W hW hsep B ψ₁ ψ₂ hb1 hb2 hψ1ge c₁ c₂ hc₁ hc₂ hψ2ge hNB m₁ m₂ m₃ hspace hgood
  have hN1 : 1 ≤ N := le_trans (le_max_right N₀₁ 1) hN
  have hNne : (N : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    linarith
  have hBne : B ≠ 0 := by
    intro h
    rw [h, mul_zero] at hNB
    exact lt_irrefl 0 hNB
  have h71 := hmain71 N (le_trans (le_max_left N₀₁ 1) hN) W hW hsep (m₁, m₂, m₃)
  have hwin := window_integral_le_Rtilde_Icc (W := W) (N := N) (B := B) (η := η)
      (ψ₁ := ψ₁) (ψ₂ := ψ₂) (C₀ := 4) (c₁ := c₁) (c₂ := c₂)
      hc₁ hc₂ (by norm_num) hb1 hb2 hψ1ge hψ2ge hη hNB hspace hgood
  set A : ℝ := ∫ v in (1 / 2 : ℝ)..2, ‖Submission.GM.Rfun W v‖ *
      Rtilde W N B ψ₁ ψ₂ (arg1 m₁ (-m₂) m₃ v) *
      Rtilde W N B ψ₁ ψ₂ (arg2 m₁ (-m₂) m₃ v) with hA
  have h71' : ‖Submission.GM.Iterm N W (m₁, m₂, m₃)‖ ≤
      C₁ * (N : ℝ) ^ 3 *
        (∫ v in pbox, (if |phas (m₁, m₂, m₃) v| ≤
          (Submission.LargeValues.M N) ^ η / (N : ℝ) then ‖Rprod W v‖ else 0))
        + C₁ * (N : ℝ) ^ (-20 : ℤ) := h71
  have hwin' : (∫ v in pbox, (if |phas (m₁, m₂, m₃) v| ≤
        (Submission.LargeValues.M N) ^ η / (N : ℝ) then ‖Rprod W v‖ else 0))
      ≤ Real.sqrt 2 * A / ((N : ℝ) * B) := hwin
  have hsqrt2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hcoef : (0 : ℝ) ≤ C₁ * (N : ℝ) ^ 3 :=
    mul_nonneg (le_of_lt hC₁pos) (pow_nonneg (by positivity) 3)
  have key : C₁ * (N : ℝ) ^ 3 * (Real.sqrt 2 * A / ((N : ℝ) * B)) =
      (C₁ * Real.sqrt 2) * ((N : ℝ) ^ 2 / B) * A := by
    field_simp <;> ring
  have htail : C₁ * (N : ℝ) ^ (-20 : ℤ) ≤
      (C₁ * Real.sqrt 2) * (N : ℝ) ^ (-20 : ℤ) := by
    have hle : C₁ ≤ C₁ * Real.sqrt 2 := by nlinarith [hC₁pos, hsqrt2]
    exact mul_le_mul_of_nonneg_right hle (zpow_nonneg (le_of_lt hNpos) _)
  calc ‖Submission.GM.Iterm N W (m₁, m₂, m₃)‖
      ≤ C₁ * (N : ℝ) ^ 3 *
          (∫ v in pbox, (if |phas (m₁, m₂, m₃) v| ≤
            (Submission.LargeValues.M N) ^ η / (N : ℝ) then ‖Rprod W v‖ else 0))
          + C₁ * (N : ℝ) ^ (-20 : ℤ) := h71'
    _ ≤ C₁ * (N : ℝ) ^ 3 * (Real.sqrt 2 * A / ((N : ℝ) * B)) +
          C₁ * (N : ℝ) ^ (-20 : ℤ) := by
        have h := mul_le_mul_of_nonneg_left hwin' hcoef
        linarith [h]
    _ = (C₁ * Real.sqrt 2) * ((N : ℝ) ^ 2 / B) * A +
          C₁ * (N : ℝ) ^ (-20 : ℤ) := by
        rw [key]
    _ ≤ (C₁ * Real.sqrt 2) * ((N : ℝ) ^ 2 / B) * A +
          (C₁ * Real.sqrt 2) * (N : ℝ) ^ (-20 : ℤ) := by
        linarith [htail]

end Work.GM.S3
