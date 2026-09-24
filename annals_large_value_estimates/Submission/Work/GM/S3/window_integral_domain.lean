import Mathlib
import Submission.Work.GM.S3.Base
import Submission.Work.GM.S3.Defs
import Submission.Work.GM.S3.prop71_defs
import Submission.Work.GM.S3.window_defs
import Submission.Work.GM.S3.window_pair_bound
import Submission.Work.GM.S3.norm_Iterm_le_Rtilde_of_window
import Submission.Work.GM.S3.prop72_core

namespace Work.GM.S3

open Complex Finset MeasureTheory
open scoped BigOperators Pointwise
open Submission.GM (Rfun)

/-- Elementary square-root arithmetic: if `A ≤ P²/c`, `Bq ≤ Q²/c` with `P, Q ≥ 0`, `c > 0` and
`0 < x ≤ 2`, then `√(x A) √Bq ≤ √2 P Q / c`.  (Local copy of the private helper of the same name
in `Work.GM.S3.window_pair_bound`.) -/
private lemma sqrt_pair_le_dom {x A Bq P Q c : ℝ} (hx0 : 0 < x) (hx2 : x ≤ 2) (hc0 : 0 < c)
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

/-- **GM 7.2's pair bound on the true domain.**  This is `Work.GM.S3.window_pair_bound` with the
window `wwin m₁ m₂ m₃ δ x` restricted to `wwin ∩ {y : y/x ∈ [1/2,2]}` and *without* the `hgood`
hypothesis: on that restricted window the `[1/2,2]`-confinement of the scaled pre-image
`T = x⁻¹ • (wwin ∩ {y/x ∈ [1/2,2]})` is automatic, since `u ∈ T` gives `u = (x*u)/x ∈ [1/2,2]`.

For `x ∈ [1/2,2]`, `δ ≥ 0`, `δ ≤ 1/(2(N B))`:

`∫_{wwin ∩ {y/x ∈ [1/2,2]}} ‖R(y/x)‖‖R(y)‖ dy ≤ √2 R̃(wcen/x) R̃(wcen)/(N B)` -/
theorem window_pair_bound_domain {W : Finset ℝ} {N : ℕ} {B δ C₀ : ℝ} {ψ₁ ψ₂ : ℝ → ℝ}
    {m₁ m₂ m₃ : ℤ}
    (hC₀ : 1 ≤ C₀) (h₁ : IsBumpAtZero ψ₁ C₀) (h₂ : IsBumpAtOne ψ₂ C₀)
    (hψ₁ge : ∀ x, |x| ≤ 1 → 1 ≤ ψ₁ x)
    (hψ₂ge : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 2, 1 ≤ ψ₂ x)
    (hB : 0 < (N : ℝ) * B)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / (2 * ((N : ℝ) * B)))
    {x : ℝ} (hx : x ∈ Set.Icc (1 / 2 : ℝ) 2) :
    ∫ y in (wwin m₁ m₂ m₃ δ x ∩ {y : ℝ | y / x ∈ Set.Icc (1 / 2 : ℝ) 2}),
        ‖Rfun W (y / x)‖ * ‖Rfun W y‖
      ≤ Real.sqrt 2 * Rtilde W N B ψ₁ ψ₂ (arg1 m₁ (-m₂) m₃ x) *
          Rtilde W N B ψ₁ ψ₂ (arg2 m₁ (-m₂) m₃ x) / ((N : ℝ) * B) := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx.1
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have hc : 0 < (N : ℝ) * B := hB
  set S : Set ℝ := wwin m₁ m₂ m₃ δ x ∩ {y : ℝ | y / x ∈ Set.Icc (1 / 2 : ℝ) 2} with hSdef
  set T : Set ℝ := x⁻¹ • S with hTdef
  have hSmeas : MeasurableSet S := by
    rw [hSdef]
    exact (measurableSet_wwin m₁ m₂ m₃ δ x).inter
      (measurableSet_Icc.preimage (measurable_id.div_const x))
  have hSfin : volume S < ⊤ :=
    lt_of_le_of_lt (measure_mono Set.inter_subset_left) (volume_wwin_lt_top m₁ m₂ m₃ δ x)
  have hTmeas : MeasurableSet T := by rw [hTdef]; exact hSmeas.const_smul₀ x⁻¹
  have hSmem : ∀ y ∈ S, y ∈ Set.Icc (1 / 2 : ℝ) 2 ∧ |y - wcen m₁ m₂ m₃ x| ≤ δ := by
    intro y hy
    rw [hSdef] at hy
    have hyw : y ∈ wwin m₁ m₂ m₃ δ x := hy.1
    have hy1 : y ∈ Set.Icc (1 / 2 : ℝ) 2 := by
      rw [wwin] at hyw; exact hyw.1
    have hy2 : |y - wcen m₁ m₂ m₃ x| ≤ δ := by
      rw [wwin] at hyw
      have h' : y ∈ Set.Icc (wcen m₁ m₂ m₃ x - δ) (wcen m₁ m₂ m₃ x + δ) := hyw.2
      rw [Set.mem_Icc] at h'
      exact abs_le.mpr ⟨by linarith [h'.1], by linarith [h'.2]⟩
    exact ⟨hy1, hy2⟩
  have hSdiv : ∀ y ∈ S, y / x ∈ Set.Icc (1 / 2 : ℝ) 2 := by
    intro y hy
    rw [hSdef] at hy
    exact hy.2
  have hTmem : ∀ u ∈ T, x * u ∈ Set.Icc (1 / 2 : ℝ) 2 ∧
      |x * u - wcen m₁ m₂ m₃ x| ≤ δ := by
    intro u hu
    rw [hTdef] at hu
    rw [Set.mem_inv_smul_set_iff₀ hxne S u] at hu
    have hu2 : x * u ∈ S := by simpa [smul_eq_mul] using hu
    exact hSmem (x * u) hu2
  have hTdiv : ∀ u ∈ T, u ∈ Set.Icc (1 / 2 : ℝ) 2 := by
    intro u hu
    rw [hTdef] at hu
    rw [Set.mem_inv_smul_set_iff₀ hxne S u] at hu
    have hu2 : x * u ∈ S := by simpa [smul_eq_mul] using hu
    have h := hSdiv (x * u) hu2
    rwa [mul_div_cancel_left₀ u hxne] at h
  have hNBδ : (N : ℝ) * B * δ ≤ 1 / 2 := by
    have h4 : δ * (2 * ((N : ℝ) * B)) ≤ 1 := (le_div_iff₀ (by positivity)).mp hδ
    nlinarith [h4, hc]
  have hSbdd : ∀ y ∈ S, |(N : ℝ) * B * (wcen m₁ m₂ m₃ x - y)| ≤ 1 := by
    intro y hy
    obtain ⟨-, hyl⟩ := hSmem y hy
    have h6 : |wcen m₁ m₂ m₃ x - y| ≤ δ := by rw [abs_sub_comm]; exact hyl
    have h7 : (N : ℝ) * B * |wcen m₁ m₂ m₃ x - y| ≤ (N : ℝ) * B * δ :=
      mul_le_mul_of_nonneg_left h6 hc.le
    calc |(N : ℝ) * B * (wcen m₁ m₂ m₃ x - y)|
        = (N : ℝ) * B * |wcen m₁ m₂ m₃ x - y| := by rw [abs_mul, abs_of_pos hc]
      _ ≤ 1 := by linarith
  have hTbdd : ∀ u ∈ T, |(N : ℝ) * B * (wcen m₁ m₂ m₃ x / x - u)| ≤ 1 := by
    intro u hu
    obtain ⟨-, huδ⟩ := hTmem u hu
    have hdiv : |wcen m₁ m₂ m₃ x / x - u| ≤ δ / x := by
      have heq : wcen m₁ m₂ m₃ x / x - u = -(x * u - wcen m₁ m₂ m₃ x) / x := by
        field_simp
        ring
      rw [heq, abs_div, abs_neg, abs_of_pos hxpos]
      exact (div_le_div_iff_of_pos_right hxpos).mpr huδ
    have h6 : (N : ℝ) * B * |wcen m₁ m₂ m₃ x / x - u| ≤ (N : ℝ) * B * (δ / x) :=
      mul_le_mul_of_nonneg_left hdiv hc.le
    have h8 : (N : ℝ) * B * δ ≤ x := by linarith [hx.1]
    have h9 : (N : ℝ) * B * δ / x ≤ 1 := (div_le_one hxpos).mpr h8
    have h7 : (N : ℝ) * B * (δ / x) ≤ 1 := by simpa [mul_div_assoc] using h9
    calc |(N : ℝ) * B * (wcen m₁ m₂ m₃ x / x - u)|
        = (N : ℝ) * B * |wcen m₁ m₂ m₃ x / x - u| := by rw [abs_mul, abs_of_pos hc]
      _ ≤ 1 := by linarith
  have hS_int : ∫ y in S, ‖Rfun W y‖ ^ 2
      ≤ Rtilde W N B ψ₁ ψ₂ (wcen m₁ m₂ m₃ x) ^ 2 / ((N : ℝ) * B) :=
    set_normSq_le_Rtilde hC₀ h₁ h₂ hB hψ₁ge hψ₂ge (wcen m₁ m₂ m₃ x)
      hSmeas hSbdd (fun u hu => (hSmem u hu).1)
  have hT_int : ∫ u in T, ‖Rfun W u‖ ^ 2
      ≤ Rtilde W N B ψ₁ ψ₂ (wcen m₁ m₂ m₃ x / x) ^ 2 / ((N : ℝ) * B) :=
    set_normSq_le_Rtilde hC₀ h₁ h₂ hB hψ₁ge hψ₂ge (wcen m₁ m₂ m₃ x / x)
      hTmeas hTbdd hTdiv
  have hf_meas : AEStronglyMeasurable (fun y : ℝ => ‖Rfun W (y / x)‖) (volume.restrict S) :=
    (((Rfun_measurable W).comp (measurable_id.div_const x)).norm).aestronglyMeasurable
  have hg_meas : AEStronglyMeasurable (fun y : ℝ => ‖Rfun W y‖) (volume.restrict S) :=
    (Rfun_measurable W).norm.aestronglyMeasurable
  have hfC : ∀ᵐ y ∂(volume.restrict S),
      ‖(fun y : ℝ => ‖Rfun W (y / x)‖) y‖ ≤ (W.card : ℝ) :=
    Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact Rfun_norm_le_card W _
  have hgC : ∀ᵐ y ∂(volume.restrict S),
      ‖(fun y : ℝ => ‖Rfun W y‖) y‖ ≤ (W.card : ℝ) :=
    Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact Rfun_norm_le_card W _
  have hCS := set_integral_mul_le_sqrt (s := S)
    (f := fun y : ℝ => ‖Rfun W (y / x)‖)
    (g := fun y : ℝ => ‖Rfun W y‖)
    hSfin (Filter.Eventually.of_forall fun y => norm_nonneg _)
    (Filter.Eventually.of_forall fun y => norm_nonneg _) hf_meas hg_meas hfC hgC
  have hsub : ∫ y in S, ‖Rfun W (y / x)‖ ^ 2 = x * ∫ u in T, ‖Rfun W u‖ ^ 2 := by
    have hkey := MeasureTheory.Measure.setIntegral_comp_smul (μ := volume)
      (f := fun u : ℝ => ‖Rfun W u‖ ^ 2) (s := S) (R := x⁻¹) (inv_ne_zero hxne)
    have hL : ∫ y in S, ‖Rfun W (y / x)‖ ^ 2
        = ∫ y in S, (fun u : ℝ => ‖Rfun W u‖ ^ 2) (x⁻¹ • y) := by
      refine MeasureTheory.setIntegral_congr_fun hSmeas fun y hy => ?_
      have h : x⁻¹ • y = y / x := by rw [smul_eq_mul, div_eq_mul_inv, mul_comm]
      rw [h]
    rw [hL, hkey, hTdef]
    simp [smul_eq_mul, abs_of_pos hxpos]
  have hR1nn : 0 ≤ Rtilde W N B ψ₁ ψ₂ (wcen m₁ m₂ m₃ x / x) := Rtilde_nonneg W N B ψ₁ ψ₂ _
  have hR2nn : 0 ≤ Rtilde W N B ψ₁ ψ₂ (wcen m₁ m₂ m₃ x) := Rtilde_nonneg W N B ψ₁ ψ₂ _
  have harith := sqrt_pair_le_dom (x := x) (A := ∫ u in T, ‖Rfun W u‖ ^ 2)
    (Bq := ∫ y in S, ‖Rfun W y‖ ^ 2)
    (P := Rtilde W N B ψ₁ ψ₂ (wcen m₁ m₂ m₃ x / x))
    (Q := Rtilde W N B ψ₁ ψ₂ (wcen m₁ m₂ m₃ x)) (c := (N : ℝ) * B)
    hxpos hx.2 hc hR1nn hR2nn hT_int hS_int
  calc ∫ y in S, ‖Rfun W (y / x)‖ * ‖Rfun W y‖
      ≤ Real.sqrt (∫ y in S, ‖Rfun W (y / x)‖ ^ 2) *
          Real.sqrt (∫ y in S, ‖Rfun W y‖ ^ 2) := hCS
    _ = Real.sqrt (x * ∫ u in T, ‖Rfun W u‖ ^ 2) *
          Real.sqrt (∫ y in S, ‖Rfun W y‖ ^ 2) := by rw [hsub]
    _ ≤ Real.sqrt 2 * Rtilde W N B ψ₁ ψ₂ (arg1 m₁ (-m₂) m₃ x) *
          Rtilde W N B ψ₁ ψ₂ (arg2 m₁ (-m₂) m₃ x) / ((N : ℝ) * B) := by
        rw [arg1_eq_wcen, arg2_eq_wcen]
        exact harith

/-- **GM 7.2's window step on the true domain, with no `hgood` hypothesis.**
This is `Work.GM.S3.window_integral_le_Rtilde_Icc` (in `GM/S3/norm_Iterm_le_Rtilde_of_window`) with
two changes:

* the `pbox`-integral is restricted to `pbox ∩ {v : v₂/v₁ ∈ [1/2,2]}` (the true domain of the
  `u₃`-weight `w2v`, see `GM/S3/prop71_domain`);
* the hypothesis `hgood` (`∀ v ∈ pbox, |phas m v| ≤ (MN)^η/N → v.2/v.1 ∈ [c₁,c₂]`) is **dropped**,
  and the plateau is fixed at `[c₁,c₂] = [1/2,2]`.

The reason `hgood` becomes unnecessary: on the true domain every point satisfies `v₂/v₁ ∈ [1/2,2]`,
so when the proof applies the pair bound at a fixed outer point `x` it may restrict the window
`wwin m₁ m₂ m₃ δ x` to `wwin ∩ {y : y/x ∈ [1/2,2]} = wwin ∩ [x/2,2x]`; for that smaller window the
`hgood` hypothesis of `Work.GM.S3.window_pair_bound_Icc` (which asks
`∀ u, x*u ∈ [1/2,2] → |x*u - wcen| ≤ δ → u ∈ [c₁,c₂]`) holds *trivially*, because `u = y/x` with
`y ∈ [x/2,2x]` lies in `[1/2,2] = [c₁,c₂]`.  (This is what makes the per-`m` estimate of GM 7.2
applicable to the "corner" triples `4m₁+2m₃+m₂ = 0` whose formal `pbox` constraint band touches the
corner `(v₁,v₂) = (2,1/2)`.) -/
theorem window_integral_domain {W : Finset ℝ} {N : ℕ} {B η : ℝ} {ψ₁ ψ₂ : ℝ → ℝ}
    {C₀ : ℝ}
    (hC₀ : 1 ≤ C₀) (h₁ : Work.GM.S3.IsBumpAtZero ψ₁ C₀) (h₂ : Work.GM.S3.IsBumpAtOne ψ₂ C₀)
    (hψ₁ge : ∀ x, |x| ≤ 1 → 1 ≤ ψ₁ x)
    (hψ₂ge : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 2, 1 ≤ ψ₂ x)
    (hη : 0 < η) (hB : 0 < (N : ℝ) * B)
    {m₁ m₂ m₃ : ℤ}
    (hspace : B * (Submission.LargeValues.M N) ^ η ≤ |((m₂ : ℤ) : ℝ)| / 2) :
    (∫ v in (Work.GM.S3.pbox ∩ {v : ℝ × ℝ | v.2 / v.1 ∈ Set.Icc (1 / 2 : ℝ) 2}),
        (if |Work.GM.S3.phas (m₁, m₂, m₃) v| ≤ (Submission.LargeValues.M N) ^ η / (N : ℝ)
          then ‖Work.GM.S3.Rprod W v‖ else 0))
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
  set cph : ℝ := (Submission.LargeValues.M N) ^ η / (N : ℝ) with hcphdef
  set δ : ℝ := (Submission.LargeValues.M N) ^ η / ((N : ℝ) * |((m₂ : ℤ) : ℝ)|) with hδdef
  have hδ0 : 0 ≤ δ := by rw [hδdef]; positivity
  have hδle : δ ≤ 1 / (2 * ((N : ℝ) * B)) := by
    rw [hδdef, div_le_div_iff₀ (by positivity) (by positivity)]
    have h2 : 2 * (B * (Submission.LargeValues.M N) ^ η) ≤ |((m₂ : ℤ) : ℝ)| := by linarith
    have h3 : 2 * (B * (Submission.LargeValues.M N) ^ η) * (N : ℝ)
        ≤ |((m₂ : ℤ) : ℝ)| * (N : ℝ) := mul_le_mul_of_nonneg_right h2 (le_of_lt hNpos)
    linarith [h3]
  have hcdelta : |((m₂ : ℤ) : ℝ)| * δ = cph := by rw [hδdef, hcphdef]; field_simp
  -- ## 1. the integrand and its integrability
  set F : ℝ × ℝ → ℝ := fun v => if |phas (m₁, m₂, m₃) v| ≤ cph then ‖Rprod W v‖ else 0
    with hFdef
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
      by_cases h : |phas (m₁, m₂, m₃) v| ≤ cph
      · rw [if_pos h, Real.norm_of_nonneg (norm_nonneg _)]; exact norm_Rprod_le W v
      · rw [if_neg h]; simp
  -- ## 2. the domain `D` and Fubini on the box
  set D : Set (ℝ × ℝ) := pbox ∩ {v : ℝ × ℝ | v.2 / v.1 ∈ Set.Icc (1 / 2 : ℝ) 2} with hDdef
  have hDmeas : MeasurableSet D := by
    rw [hDdef]
    refine measurableSet_pbox.inter ?_
    exact measurableSet_Icc.preimage (measurable_snd.div measurable_fst)
  have hDsub : D ⊆ pbox := by rw [hDdef]; exact Set.inter_subset_left
  have hIntD : IntegrableOn (D.indicator F) (Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (1 / 2 : ℝ) 2)
      volume := hInt.indicator hDmeas
  have hFub : (∫ v in pbox, D.indicator F v) = ∫ x in Set.Icc (1 / 2 : ℝ) 2,
      ∫ y in Set.Icc (1 / 2 : ℝ) 2, D.indicator F (x, y) := by
    rw [pbox]
    exact MeasureTheory.setIntegral_prod (fun z : ℝ × ℝ => D.indicator F z) hIntD
  -- ## 3. pointwise rewriting of the inner integrand
  have hkey : ∀ x y : ℝ, x ∈ Set.Icc (1 / 2 : ℝ) 2 → y ∈ Set.Icc (1 / 2 : ℝ) 2 →
      D.indicator F (x, y) = ‖Rfun W x‖ *
        (wwin m₁ m₂ m₃ δ x ∩ {y : ℝ | y / x ∈ Set.Icc (1 / 2 : ℝ) 2}).indicator
          (fun y => ‖Rfun W (y / x)‖ * ‖Rfun W y‖) y := by
    intro x y hx hy
    have hyne : y ≠ 0 := by linarith [hy.1]
    have hmemD : ((x, y) ∈ D) ↔ y / x ∈ Set.Icc (1 / 2 : ℝ) 2 := by
      rw [hDdef, Set.mem_inter_iff]
      constructor
      · intro h; exact h.2
      · intro h; exact ⟨by rw [pbox]; exact ⟨hx, hy⟩, h⟩
    have hcond : (|phas (m₁, m₂, m₃) (x, y)| ≤ cph) ↔ |y - wcen m₁ m₂ m₃ x| ≤ δ := by
      rw [phas_eq_wcen m₁ m₂ m₃ hm2ne, abs_mul]
      constructor
      · intro h
        rw [← hcdelta] at h
        exact (mul_le_mul_iff_of_pos_left hm2pos).mp h
      · intro h
        rw [← hcdelta]
        exact mul_le_mul_of_nonneg_left h (abs_nonneg _)
    have hyw1 : (y ∈ wwin m₁ m₂ m₃ δ x) → y ∈ Set.Icc (1 / 2 : ℝ) 2 := by
      intro h; rw [wwin] at h; exact h.1
    have hyw2 : (y ∈ wwin m₁ m₂ m₃ δ x) ↔ |y - wcen m₁ m₂ m₃ x| ≤ δ := by
      constructor
      · intro h
        rw [wwin, Set.mem_inter_iff] at h
        have h' : y ∈ Set.Icc (wcen m₁ m₂ m₃ x - δ) (wcen m₁ m₂ m₃ x + δ) := h.2
        rw [Set.mem_Icc] at h'
        exact abs_le.mpr ⟨by linarith [h'.1], by linarith [h'.2]⟩
      · intro h
        rw [wwin, Set.mem_inter_iff]
        refine ⟨hy, ?_⟩
        rw [Set.mem_Icc]
        exact ⟨by linarith [(abs_le.mp h).1], by linarith [(abs_le.mp h).2]⟩
    have hRp : ‖Rprod W (x, y)‖ = ‖Rfun W x‖ * ‖Rfun W (y / x)‖ * ‖Rfun W y‖ := by
      simp only [Rprod, norm_mul, Rfun_norm_one_div W (v := y) hyne]
    have hstep : D.indicator F (x, y) = ‖Rfun W x‖ *
        (if y / x ∈ Set.Icc (1 / 2 : ℝ) 2 then
          (if y ∈ wwin m₁ m₂ m₃ δ x then ‖Rfun W (y / x)‖ * ‖Rfun W y‖ else 0)
          else 0) := by
      rw [Set.indicator_apply]
      simp only [hFdef]
      by_cases hDxy : (x, y) ∈ D
      · rw [if_pos hDxy, if_pos (hmemD.mp hDxy)]
        by_cases hw : y ∈ wwin m₁ m₂ m₃ δ x
        · rw [if_pos (hcond.mpr (hyw2.mp hw)), if_pos hw, hRp]
          ring
        · rw [if_neg (fun h => hw (hyw2.mpr (hcond.mp h))), if_neg hw]
          ring
      · rw [if_neg hDxy, if_neg (fun h => hDxy (hmemD.mpr h))]
        ring
    rw [hstep, Set.indicator_apply]
    by_cases h : y / x ∈ Set.Icc (1 / 2 : ℝ) 2
    · rw [if_pos h]
      by_cases hw : y ∈ wwin m₁ m₂ m₃ δ x
      · rw [if_pos hw, if_pos (show y ∈ wwin m₁ m₂ m₃ δ x ∩
            {y : ℝ | y / x ∈ Set.Icc (1 / 2 : ℝ) 2} from ⟨hw, h⟩)]
      · rw [if_neg hw, if_neg (fun hmem => hw hmem.1)]
    · rw [if_neg h, if_neg (fun hmem => h hmem.2)]
  -- ## 4. the per-`x` bound
  have hinner : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 2,
      (∫ y in Set.Icc (1 / 2 : ℝ) 2, D.indicator F (x, y)) ≤
      ‖Rfun W x‖ * (Real.sqrt 2 * Rtilde W N B ψ₁ ψ₂ (arg1 m₁ (-m₂) m₃ x) *
        Rtilde W N B ψ₁ ψ₂ (arg2 m₁ (-m₂) m₃ x) / ((N : ℝ) * B)) := by
    intro x hx
    have hW'meas : MeasurableSet (wwin m₁ m₂ m₃ δ x ∩
        {y : ℝ | y / x ∈ Set.Icc (1 / 2 : ℝ) 2}) :=
      (measurableSet_wwin m₁ m₂ m₃ δ x).inter
        (measurableSet_Icc.preimage (measurable_id.div_const x))
    have hW'sub : (wwin m₁ m₂ m₃ δ x ∩ {y : ℝ | y / x ∈ Set.Icc (1 / 2 : ℝ) 2})
        ⊆ Set.Icc (1 / 2 : ℝ) 2 := fun y hy => wwin_subset_Icc m₁ m₂ m₃ δ x hy.1
    have heq : (∫ y in Set.Icc (1 / 2 : ℝ) 2, D.indicator F (x, y))
        = ‖Rfun W x‖ * ∫ y in (wwin m₁ m₂ m₃ δ x ∩
            {y : ℝ | y / x ∈ Set.Icc (1 / 2 : ℝ) 2}),
            ‖Rfun W (y / x)‖ * ‖Rfun W y‖ := by
      have h1 : (∫ y in Set.Icc (1 / 2 : ℝ) 2, D.indicator F (x, y))
          = ∫ y in Set.Icc (1 / 2 : ℝ) 2, ‖Rfun W x‖ *
              (wwin m₁ m₂ m₃ δ x ∩ {y : ℝ | y / x ∈ Set.Icc (1 / 2 : ℝ) 2}).indicator
                (fun y => ‖Rfun W (y / x)‖ * ‖Rfun W y‖) y := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
        intro y hy
        exact hkey x y hx hy
      rw [h1, setIntegral_const_mul' ‖Rfun W x‖ _]
      congr 1
      exact setIntegral_indicator_of_subset hW'meas hW'sub _
    rw [heq]
    exact mul_le_mul_of_nonneg_left
      (window_pair_bound_domain hC₀ h₁ h₂ hψ₁ge hψ₂ge hB hδ0 hδle hx)
      (norm_nonneg _)
  -- ## 5. the outer comparison
  have hmono : (∫ x in Set.Icc (1 / 2 : ℝ) 2,
        ∫ y in Set.Icc (1 / 2 : ℝ) 2, D.indicator F (x, y))
      ≤ ∫ x in Set.Icc (1 / 2 : ℝ) 2, ‖Rfun W x‖ *
          (Real.sqrt 2 * Rtilde W N B ψ₁ ψ₂ (arg1 m₁ (-m₂) m₃ x) *
            Rtilde W N B ψ₁ ψ₂ (arg2 m₁ (-m₂) m₃ x) / ((N : ℝ) * B)) := by
    apply MeasureTheory.setIntegral_mono_of_nonneg
    · intro x hx
      refine MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun y hy => ?_)
      rw [Set.indicator_apply]
      split_ifs with hmem
      · simp only [hFdef]; split_ifs <;> positivity
      · norm_num
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
            ≤ Real.sqrt 2 * K * K / ((N : ℝ) * B) := by gcongr
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
  -- ## 7. assembly
  have hfirst : (∫ v in D, F v) = ∫ v in pbox, D.indicator F v := by
    rw [MeasureTheory.setIntegral_indicator (f := F) (s := pbox) hDmeas]
    rw [Set.inter_eq_right.mpr hDsub]
  have hFD : (∫ v in D, (if |phas (m₁, m₂, m₃) v| ≤ cph then ‖Rprod W v‖ else 0))
      = ∫ v in D, F v := by
    apply MeasureTheory.setIntegral_congr_fun hDmeas
    intro v hv
    simp only [hFdef]
  rw [hFD]
  calc (∫ v in D, F v)
      = ∫ v in pbox, D.indicator F v := hfirst
    _ = ∫ x in Set.Icc (1 / 2 : ℝ) 2, ∫ y in Set.Icc (1 / 2 : ℝ) 2, D.indicator F (x, y) :=
        hFub
    _ ≤ ∫ x in Set.Icc (1 / 2 : ℝ) 2, ‖Rfun W x‖ *
          (Real.sqrt 2 * Rtilde W N B ψ₁ ψ₂ (arg1 m₁ (-m₂) m₃ x) *
            Rtilde W N B ψ₁ ψ₂ (arg2 m₁ (-m₂) m₃ x) / ((N : ℝ) * B)) := hmono
    _ = Real.sqrt 2 * (∫ v in (1 / 2 : ℝ)..2, ‖Rfun W v‖ *
            Rtilde W N B ψ₁ ψ₂ (arg1 m₁ (-m₂) m₃ v) *
            Rtilde W N B ψ₁ ψ₂ (arg2 m₁ (-m₂) m₃ v)) / ((N : ℝ) * B) := hfinal

end Work.GM.S3
