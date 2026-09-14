import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory Set
open scoped ENNReal

namespace Commons.Analysis.Integral

lemma cos_ge_of_cos_affine {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {q e : E} {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hcos : c * (‖q‖ * ‖e‖) ≤ inner ℝ q e) {s : ℝ} (hs : 0 ≤ s) :
    c * ‖e‖ * ‖q + s • e‖ ≤ inner ℝ (q + s • e) e := by
  have hnormsq : ‖q + s • e‖ ^ 2 = ‖q‖ ^ 2 + 2 * s * inner ℝ q e + s ^ 2 * ‖e‖ ^ 2 := by
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
    ring
  have hqe : inner ℝ (q + s • e) e = inner ℝ q e + s * ‖e‖ ^ 2 := by
    rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have ha0 : 0 ≤ inner ℝ q e := le_trans (by positivity) hcos
  have hkey : (c * ‖e‖ * ‖q + s • e‖) ^ 2 ≤ (inner ℝ (q + s • e) e) ^ 2 := by
    have e1 : (c * ‖e‖ * ‖q + s • e‖) ^ 2 = c ^ 2 * ‖e‖ ^ 2 * ‖q + s • e‖ ^ 2 := by ring
    have hdiff : (inner ℝ (q + s • e) e) ^ 2 - (c * ‖e‖ * ‖q + s • e‖) ^ 2
        = (inner ℝ q e ^ 2 - c ^ 2 * ‖e‖ ^ 2 * ‖q‖ ^ 2)
          + (1 - c ^ 2) * ‖e‖ ^ 2 * s * (2 * inner ℝ q e + s * ‖e‖ ^ 2) := by
      rw [hqe, e1, hnormsq]; ring
    have hcqn : 0 ≤ c * (‖q‖ * ‖e‖) := mul_nonneg hc (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    have hmul := mul_self_le_mul_self hcqn hcos
    have h1 : 0 ≤ inner ℝ q e ^ 2 - c ^ 2 * ‖e‖ ^ 2 * ‖q‖ ^ 2 := by nlinarith [hmul]
    have h2 : 0 ≤ 1 - c ^ 2 := by nlinarith [hc, hc1]
    have h4 : 0 ≤ 2 * inner ℝ q e + s * ‖e‖ ^ 2 :=
      add_nonneg (by linarith) (by positivity)
    have h3 : 0 ≤ (1 - c ^ 2) * ‖e‖ ^ 2 * s * (2 * inner ℝ q e + s * ‖e‖ ^ 2) :=
      mul_nonneg (mul_nonneg (mul_nonneg h2 (sq_nonneg _)) hs) h4
    have : 0 ≤ (inner ℝ (q + s • e) e) ^ 2 - (c * ‖e‖ * ‖q + s • e‖) ^ 2 := by
      rw [hdiff]; linarith
    linarith
  have h1 : 0 ≤ c * ‖e‖ * ‖q + s • e‖ :=
    mul_nonneg (mul_nonneg hc (norm_nonneg _)) (norm_nonneg _)
  have h2 : 0 ≤ inner ℝ (q + s • e) e := by
    rw [hqe]; exact add_nonneg ha0 (mul_nonneg hs (sq_nonneg _))
  have := sq_le_sq.mp hkey
  simpa [abs_of_nonneg h1, abs_of_nonneg h2] using this

lemma add_smul_ne_zero_of_cos {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {q e : E} {c : ℝ} (he : 0 < ‖e‖) (hc : 0 ≤ c)
    (hcos : c * (‖q‖ * ‖e‖) ≤ inner ℝ q e) {s : ℝ} (hs : 0 < s) :
    q + s • e ≠ 0 := by
  intro h
  have h0 : inner ℝ (q + s • e) e = 0 := by rw [h, inner_zero_left]
  rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at h0
  have h1 : 0 ≤ c * (‖q‖ * ‖e‖) := mul_nonneg hc (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have h2 : 0 < s * ‖e‖ ^ 2 := mul_pos hs (pow_pos he 2)
  linarith

lemma hasDerivAt_norm_add_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (q e : E) {x : ℝ} (hx : q + x • e ≠ 0) :
    HasDerivAt (fun s : ℝ => ‖q + s • e‖) (inner ℝ (q + x • e) e / ‖q + x • e‖) x := by
  have hw : HasDerivAt (fun s : ℝ => q + s • e) e x :=
    by simpa using ((hasDerivAt_id x).smul_const e).const_add q
  have hsq : HasDerivAt (fun s : ℝ => ‖q + s • e‖ ^ 2) (2 * inner ℝ (q + x • e) e) x :=
    hw.norm_sq
  have hne : ‖q + x • e‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  have hsqrt := hsq.sqrt hne
  have hfun : (fun s : ℝ => Real.sqrt (‖q + s • e‖ ^ 2)) = fun s => ‖q + s • e‖ := by
    funext s; exact Real.sqrt_sq (norm_nonneg _)
  rw [hfun] at hsqrt
  have hval : (2 * inner ℝ (q + x • e) e) / (2 * Real.sqrt (‖q + x • e‖ ^ 2))
      = inner ℝ (q + x • e) e / ‖q + x • e‖ := by
    rw [Real.sqrt_sq (norm_nonneg _), mul_div_mul_left _ _ (by norm_num : (2:ℝ) ≠ 0)]
  exact hsqrt.congr_deriv hval

lemma setIntegral_le_inv_mul_of_ae_le {G H : ℝ → ℝ} {m C T : ℝ} (hm : 0 < m)
    (hGnn : ∀ s, 0 ≤ G s)
    (hdom : ∀ s, ‖H s‖ ≤ C * ‖G s‖)
    (hGH : ∀ᵐ s ∂(volume.restrict (Icc (0:ℝ) T)), G s ≤ m⁻¹ * H s)
    (hGm : Measurable G) (hHm : Measurable H) :
    ∫ s in Icc (0:ℝ) T, G s ≤ m⁻¹ * ∫ s in Icc (0:ℝ) T, H s := by
  by_cases hHint : IntegrableOn H (Icc (0:ℝ) T)
  · have hGint : IntegrableOn G (Icc (0:ℝ) T) := by
      refine (hHint.norm.const_mul m⁻¹).mono' hGm.aestronglyMeasurable.restrict ?_
      filter_upwards [hGH] with s hs
      rw [Real.norm_of_nonneg (hGnn s)]
      exact le_trans hs (mul_le_mul_of_nonneg_left (le_abs_self _) (inv_nonneg.mpr hm.le))
    have hH2 : IntegrableOn (fun s => m⁻¹ * H s) (Icc (0:ℝ) T) := hHint.const_mul m⁻¹
    calc ∫ s in Icc (0:ℝ) T, G s ≤ ∫ s in Icc (0:ℝ) T, m⁻¹ * H s :=
          setIntegral_mono_ae_restrict hGint hH2 hGH
      _ = m⁻¹ * ∫ s in Icc (0:ℝ) T, H s := by rw [integral_const_mul]
  · have hGnot : ¬ IntegrableOn G (Icc (0:ℝ) T) := by
      intro hGint
      exact hHint ((hGint.norm.const_mul C).mono' hHm.aestronglyMeasurable.restrict
        (Filter.Eventually.of_forall hdom))
    rw [integral_undef hHint, mul_zero, integral_undef hGnot]

theorem intervalIntegral_comp_norm_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {q e : E} {c : ℝ} (he : 0 < ‖e‖) (hc : 0 < c) (hc1 : c ≤ 1)
    (hcos : c * (‖q‖ * ‖e‖) ≤ inner ℝ q e) {f : ℝ → ℝ} (hf : ∀ t, 0 ≤ f t)
    (hfm : Measurable f) {T : ℝ} (hT : 0 ≤ T) :
    ∫ s in (0:ℝ)..T, f ‖q + s • e‖ ≤ c⁻¹ * (‖e‖⁻¹ * ∫ t in ‖q‖..‖q + T • e‖, f t) := by
  have hc0 : 0 ≤ c := hc.le
  have hangle : 0 ≤ inner ℝ q e :=
    le_trans (mul_nonneg hc0 (mul_nonneg (norm_nonneg _) (norm_nonneg _))) hcos
  set m : ℝ := c * ‖e‖ with hm
  have hmpos : 0 < m := by rw [hm]; exact mul_pos hc he
  have hφcont : Continuous (fun s : ℝ => q + s • e) := by fun_prop
  have hcont : ContinuousOn (fun s : ℝ => ‖q + s • e‖) (Icc (0:ℝ) T) :=
    (continuous_norm.comp hφcont).continuousOn
  have hφm : Measurable (fun s : ℝ => ‖q + s • e‖) := (continuous_norm.comp hφcont).measurable
  have hderiv : ∀ x ∈ Ioo (0:ℝ) T, HasDerivAt (fun s : ℝ => ‖q + s • e‖)
      (inner ℝ (q + x • e) e / ‖q + x • e‖) x := by
    intro x hx
    exact hasDerivAt_norm_add_smul q e (add_smul_ne_zero_of_cos he hc0 hcos hx.1)
  have hPnn : ∀ x ∈ Ioo (0:ℝ) T, 0 ≤ inner ℝ (q + x • e) e / ‖q + x • e‖ := by
    intro x hx
    exact div_nonneg
      (le_trans (mul_nonneg (mul_nonneg hc0 (norm_nonneg _)) (norm_nonneg _))
        (cos_ge_of_cos_affine hc0 hc1 hcos hx.1.le)) (norm_nonneg _)
  have hcv : ∫ s in Icc (0:ℝ) T, (inner ℝ (q + s • e) e / ‖q + s • e‖) * f ‖q + s • e‖
      = ∫ t in Icc ‖q‖ ‖q + T • e‖, f t := by
    have h2 : (∫ s in Icc (0:ℝ) T, (inner ℝ (q + s • e) e / ‖q + s • e‖) * f ‖q + s • e‖)
        = ∫ s in Icc (0:ℝ) T, (inner ℝ (q + s • e) e / ‖q + s • e‖) • f ‖q + s • e‖ := rfl
    have h3 := integral_Icc_deriv_smul_of_deriv_nonneg (f := fun s : ℝ => ‖q + s • e‖)
      (f' := fun x => inner ℝ (q + x • e) e / ‖q + x • e‖) (g := f) hcont hderiv hPnn hT
    rw [h2, h3]
    simp
  have hPbound : ∀ s : ℝ, ‖inner ℝ (q + s • e) e / ‖q + s • e‖‖ ≤ ‖e‖ := by
    intro s
    rcases eq_or_lt_of_le (norm_nonneg (q + s • e)) with h0 | h0
    · rw [← h0, div_zero, norm_zero]
      exact norm_nonneg e
    · rw [norm_div, norm_norm, div_le_iff₀ h0]
      calc ‖inner ℝ (q + s • e) e‖ ≤ ‖q + s • e‖ * ‖e‖ := norm_inner_le_norm (𝕜 := ℝ) _ _
        _ = ‖e‖ * ‖q + s • e‖ := by ring
  have hGnn : ∀ s : ℝ, 0 ≤ f ‖q + s • e‖ := fun s => hf _
  have hdom : ∀ s : ℝ, ‖(inner ℝ (q + s • e) e / ‖q + s • e‖) * f ‖q + s • e‖‖
      ≤ ‖e‖ * ‖f ‖q + s • e‖‖ := by
    intro s
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hPbound s) (norm_nonneg _)
  have hGm : Measurable (fun s : ℝ => f ‖q + s • e‖) := hfm.comp hφm
  have hPm : Measurable (fun s : ℝ => inner ℝ (q + s • e) e / ‖q + s • e‖) :=
    (hφcont.inner continuous_const).measurable.div hφm
  have hHm : Measurable (fun s : ℝ => (inner ℝ (q + s • e) e / ‖q + s • e‖) * f ‖q + s • e‖) :=
    hPm.mul hGm
  have hGH : ∀ᵐ s ∂(volume.restrict (Icc (0:ℝ) T)),
      f ‖q + s • e‖ ≤ m⁻¹ * (inner ℝ (q + s • e) e / ‖q + s • e‖ * f ‖q + s • e‖) := by
    have hpt : ∀ s ∈ Ioo (0:ℝ) T, f ‖q + s • e‖ ≤
        m⁻¹ * (inner ℝ (q + s • e) e / ‖q + s • e‖ * f ‖q + s • e‖) := by
      intro s hs
      have hne : q + s • e ≠ 0 := add_smul_ne_zero_of_cos he hc0 hcos hs.1
      have hPge : m ≤ inner ℝ (q + s • e) e / ‖q + s • e‖ := by
        rw [hm, le_div_iff₀ (norm_pos_iff.mpr hne)]
        exact cos_ge_of_cos_affine hc0 hc1 hcos hs.1.le
      have hone : 1 ≤ m⁻¹ * (inner ℝ (q + s • e) e / ‖q + s • e‖) := by
        have := mul_le_mul_of_nonneg_left hPge (inv_nonneg.mpr hmpos.le)
        rwa [inv_mul_cancel₀ hmpos.ne'] at this
      have := mul_le_mul_of_nonneg_right hone (hf ‖q + s • e‖)
      simpa [mul_assoc, one_mul] using this
    have hfin : volume ({0, T} : Set ℝ) = 0 := by
      rw [show ({0, T} : Set ℝ) = {0} ∪ {T} from rfl, measure_union_null_iff]
      exact ⟨measure_singleton 0, measure_singleton T⟩
    have hnull : volume (Icc (0:ℝ) T \ Ioo (0:ℝ) T) = 0 := by
      apply measure_mono_null (t := ({0, T} : Set ℝ)) _ hfin
      intro s hs
      simp only [Set.mem_sdiff, mem_Icc, mem_Ioo, mem_insert_iff, mem_singleton_iff] at hs ⊢
      obtain ⟨⟨h1, h2⟩, h3⟩ := hs
      rcases eq_or_lt_of_le h1 with h0 | h0
      · exact Or.inl h0.symm
      · exact Or.inr (le_antisymm h2 (not_lt.mp fun hlt => h3 ⟨h0, hlt⟩))
    have hae : ∀ᵐ s ∂(volume : Measure ℝ), s ∉ Icc (0:ℝ) T \ Ioo (0:ℝ) T := by
      rw [ae_iff]
      have hset : {a : ℝ | ¬ a ∉ Icc (0:ℝ) T \ Ioo (0:ℝ) T} = Icc (0:ℝ) T \ Ioo (0:ℝ) T := by
        ext a; simp only [Set.mem_ofPred_eq, not_not]
      rw [hset]
      exact hnull
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hae] with s hs hmem
    exact hpt s (by by_contra h; exact hs ⟨hmem, h⟩)
  have hcmp := setIntegral_le_inv_mul_of_ae_le (G := fun s => f ‖q + s • e‖)
      (H := fun s => (inner ℝ (q + s • e) e / ‖q + s • e‖) * f ‖q + s • e‖)
      (C := ‖e‖) (T := T) hmpos hGnn hdom hGH hGm hHm
  have hmono : ‖q‖ ≤ ‖q + T • e‖ := by
    have h1 : 0 ≤ inner ℝ q (T • e) := by
      rw [real_inner_smul_right]; exact mul_nonneg hT hangle
    have h2 : ‖q‖ ^ 2 ≤ ‖q + T • e‖ ^ 2 := by
      rw [norm_add_sq_real]; nlinarith [h1, sq_nonneg ‖T • e‖]
    nlinarith [h2, norm_nonneg q, norm_nonneg (q + T • e)]
  calc ∫ s in (0:ℝ)..T, f ‖q + s • e‖
      = ∫ s in Icc (0:ℝ) T, f ‖q + s • e‖ := by
          rw [intervalIntegral.integral_of_le hT, ← integral_Icc_eq_integral_Ioc]
    _ ≤ m⁻¹ * ∫ s in Icc (0:ℝ) T, (inner ℝ (q + s • e) e / ‖q + s • e‖) * f ‖q + s • e‖ := hcmp
    _ = m⁻¹ * ∫ t in Icc ‖q‖ ‖q + T • e‖, f t := by rw [hcv]
    _ = c⁻¹ * (‖e‖⁻¹ * ∫ t in ‖q‖..‖q + T • e‖, f t) := by
          rw [intervalIntegral.integral_of_le hmono, ← integral_Icc_eq_integral_Ioc, hm, mul_inv,
            mul_assoc]

end Commons.Analysis.Integral