import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Submission.Commons.Analysis.Calculus.integral_Ioi_mul_inv_sq_eq_integral_Ioi_deriv_mul_inv

namespace Commons.Analysis.Calculus

open MeasureTheory Set Filter
open scoped Topology

/-- General-`δ` version of `integrable_div_sq_of_continuous_hasCompactSupport`: if `f` is
continuous, compactly supported and vanishes on `[-δ,δ]`, then `t ↦ f t / t²` is integrable. -/
theorem integrable_div_sq_of_continuous_hasCompactSupport_pos {f : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hf : Continuous f) (hs : HasCompactSupport f) (h0 : ∀ t : ℝ, |t| ≤ δ → f t = 0) :
    Integrable (fun t : ℝ => f t / t ^ 2) := by
  have hcont : Continuous (fun t : ℝ => f t / t ^ 2) := by
    rw [continuous_iff_continuousAt]
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · have hmem : Set.Ioo (-δ) δ ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by linarith) hδ
      have heq : (fun t : ℝ => f t / t ^ 2) =ᶠ[𝓝 (0 : ℝ)] (fun _ => (0 : ℝ)) := by
        filter_upwards [hmem] with t ht
        have hlt : |t| < δ := by rw [abs_lt]; exact ⟨ht.1, ht.2⟩
        rw [h0 t (le_of_lt hlt)]
        simp
      exact continuousAt_const.congr heq.symm
    · exact (hf.continuousAt).div ((continuous_id.pow 2).continuousAt) (pow_ne_zero 2 hx)
  have hsupp : HasCompactSupport (fun t : ℝ => f t / t ^ 2) := by
    refine hs.mono' ?_
    intro x hx
    rw [Function.mem_support] at hx
    exact subset_tsupport f (by rw [Function.mem_support]; intro hfx; exact hx (by rw [hfx]; simp))
  exact hcont.integrable_of_hasCompactSupport hsupp

/-- General-`δ` version of `integral_Ioi_mul_inv_sq_eq_integral_Ioi_deriv_mul_inv`: integration by
parts on `(0,∞)` for a `C¹` compactly supported function vanishing on `(0,δ]`. -/
theorem integral_Ioi_mul_inv_sq_eq_integral_Ioi_deriv_mul_inv_pos {φ : ℝ → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hφ : ContDiff ℝ 1 φ) (hsupp : HasCompactSupport φ)
    (h0 : ∀ t : ℝ, 0 < t → t ≤ δ → φ t = 0) :
    (∫ t in Set.Ioi (0 : ℝ), φ t * (t ^ 2)⁻¹) = ∫ t in Set.Ioi (0 : ℝ), deriv φ t * t⁻¹ := by
  obtain ⟨N, hN⟩ := exists_forall_ge_eq_zero_of_hasCompactSupport hsupp
  let M : ℝ := max N δ
  have hM_ge : δ ≤ M := le_max_right N δ
  have hM : ∀ t : ℝ, M ≤ t → φ t = 0 := fun t ht => hN t (le_trans (le_max_left N δ) ht)
  have hcont1 : ContinuousOn (fun t : ℝ => φ t * (t ^ 2)⁻¹) (Set.Icc δ M) := by
    apply ContinuousOn.mul
    · exact hφ.continuous.continuousOn
    · apply ContinuousOn.inv₀
      · exact (continuous_id.pow 2).continuousOn
      · intro t ht
        exact pow_ne_zero 2 (ne_of_gt (by linarith [ht.1, hδ] : (0 : ℝ) < t))
  have hcont2 : ContinuousOn (fun t : ℝ => deriv φ t * (-(t)⁻¹)) (Set.Icc δ M) := by
    apply ContinuousOn.mul
    · exact (hφ.continuous_deriv le_rfl).continuousOn
    · exact ContinuousOn.neg (ContinuousOn.inv₀ continuousOn_id
        (fun t ht => ne_of_gt (by linarith [ht.1, hδ] : (0 : ℝ) < t)))
  have hf1 : IntegrableOn (fun t : ℝ => φ t * (t ^ 2)⁻¹) (Set.Ioi (0 : ℝ)) := by
    have hbase : IntegrableOn (fun t : ℝ => φ t * (t ^ 2)⁻¹) (Set.Icc δ M) :=
      ContinuousOn.integrableOn_compact isCompact_Icc hcont1
    refine hbase.of_forall_sdiff_eq_zero measurableSet_Ioi ?_
    intro t ht
    rcases ht with ⟨htpos, htnot⟩
    have hφt0 : φ t = 0 := by
      rcases not_and_or.mp htnot with hlt | hgt
      · exact h0 t htpos (le_of_lt (not_le.mp hlt))
      · exact hM t (le_of_lt (not_le.mp hgt))
    simp [hφt0]
  have hf2 : IntegrableOn (fun t : ℝ => deriv φ t * (-(t)⁻¹)) (Set.Ioi (0 : ℝ)) := by
    have hbase : IntegrableOn (fun t : ℝ => deriv φ t * (-(t)⁻¹)) (Set.Icc δ M) :=
      ContinuousOn.integrableOn_compact isCompact_Icc hcont2
    refine hbase.of_forall_sdiff_eq_zero measurableSet_Ioi ?_
    intro t ht
    rcases ht with ⟨htpos, htnot⟩
    have hd0 : deriv φ t = 0 := by
      rcases not_and_or.mp htnot with hlt | hgt
      · have hmem : Set.Ioo (0 : ℝ) δ ∈ 𝓝 t := Ioo_mem_nhds htpos (not_le.mp hlt)
        have heq : φ =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
          apply Filter.eventually_of_mem hmem
          intro s hs
          exact h0 s hs.1 (le_of_lt hs.2)
        simpa using heq.deriv_eq
      · have hmem : Set.Ioi M ∈ 𝓝 t := Ioi_mem_nhds (not_le.mp hgt)
        have heq : φ =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
          apply Filter.eventually_of_mem hmem
          intro s hs
          exact hM s (le_of_lt hs)
        simpa using heq.deriv_eq
    simp [hd0]
  have hzero : Tendsto (fun t : ℝ => φ t * (-(t)⁻¹)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hmem : Set.Ioc (0 : ℝ) δ ∈ 𝓝[>] (0 : ℝ) := by
      rw [mem_nhdsGT_iff_exists_Ioc_subset]
      exact ⟨δ, hδ, subset_rfl⟩
    have heq : (fun t : ℝ => φ t * (-(t)⁻¹)) =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => (0 : ℝ)) := by
      apply Filter.eventually_of_mem hmem
      intro t ht
      change φ t * (-(t⁻¹)) = 0
      rw [h0 t ht.1 ht.2]
      ring
    exact tendsto_const_nhds.congr' heq.symm
  have hinfty : Tendsto (fun t : ℝ => φ t * (-(t)⁻¹)) atTop (𝓝 0) := by
    have heq : (fun t : ℝ => φ t * (-(t)⁻¹)) =ᶠ[atTop] (fun _ => (0 : ℝ)) := by
      filter_upwards [eventually_ge_atTop M] with t ht
      rw [hM t ht]
      ring
    exact tendsto_const_nhds.congr' heq.symm
  have hu : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt φ (deriv φ x) x := by
    intro x _
    exact (hφ.differentiable one_ne_zero x).hasDerivAt
  have hv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => -(t)⁻¹) ((x ^ 2)⁻¹) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have h : HasDerivAt (fun t : ℝ => (t⁻¹)) (-(x ^ 2)⁻¹) x := hasDerivAt_inv hx0
    exact h.neg.congr_deriv (by ring)
  have key := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul (a := (0 : ℝ)) (a' := (0 : ℝ))
    (b' := (0 : ℝ)) (u := φ) (u' := deriv φ) (v := fun t : ℝ => -(t)⁻¹)
    (v' := fun t : ℝ => (t ^ 2)⁻¹) hu hv hf1 hf2 hzero hinfty
  rw [key]
  have hab : (∫ t in Set.Ioi (0 : ℝ), deriv φ t * (-(t)⁻¹)) =
      - ∫ t in Set.Ioi (0 : ℝ), deriv φ t * t⁻¹ := by
    have hneg : (fun t : ℝ => deriv φ t * (-(t)⁻¹)) =
        (fun t : ℝ => -(deriv φ t * t⁻¹)) := by
      funext t
      ring
    rw [hneg, MeasureTheory.integral_neg]
  rw [hab]
  ring

/-- General-`δ` version of `integral_Ioi_slope_eq_integral_div_sq`: the exact integration-by-parts
identity behind the slope estimate. -/
theorem integral_Ioi_slope_eq_integral_div_sq_pos {f : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) (h0 : ∀ t : ℝ, |t| ≤ δ → f t = 0) :
    (∫ t in Set.Ioi (0 : ℝ), (deriv f t - deriv f (-t)) / t) = ∫ t : ℝ, f t / t ^ 2 := by
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  set φ : ℝ → ℝ := fun t => f t + f (-t) with hφdef
  have hφcd : ContDiff ℝ 1 φ := by
    have h : ContDiff ℝ 2 φ := by
      rw [hφdef]
      exact hf.add (hf.comp contDiff_neg)
    exact h.of_le (by norm_num)
  have hφsupp : HasCompactSupport φ := by
    rw [hφdef]
    exact hs.add (hs.comp_homeomorph (Homeomorph.neg ℝ))
  have hφ0 : ∀ t : ℝ, 0 < t → t ≤ δ → φ t = 0 := by
    intro t ht0 ht1
    rw [hφdef]
    show f t + f (-t) = 0
    rw [h0 t (by rw [abs_of_pos ht0]; exact ht1),
        h0 (-t) (by rw [abs_neg, abs_of_pos ht0]; exact ht1)]
    ring
  have hkey := integral_Ioi_mul_inv_sq_eq_integral_Ioi_deriv_mul_inv_pos hδ hφcd hφsupp hφ0
  have hA : (∫ t in Ioi (0 : ℝ), deriv φ t * t⁻¹)
      = ∫ t in Ioi (0 : ℝ), (deriv f t - deriv f (-t)) / t := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    show deriv φ t * t⁻¹ = (deriv f t - deriv f (-t)) / t
    have h1 : deriv φ t = deriv f t - deriv f (-t) := by
      rw [hφdef]
      change deriv (f + (f ∘ Neg.neg)) t = deriv f t - deriv f (-t)
      rw [deriv_add hfd.differentiableAt
            (hfd.differentiableAt.comp t (differentiable_neg.differentiableAt))]
      have hc : deriv (f ∘ Neg.neg) t = -deriv f (-t) := deriv_comp_neg f t
      rw [hc]
      ring
    rw [h1, div_eq_mul_inv]
  have hF : Integrable (fun t : ℝ => f t / t ^ 2) :=
    integrable_div_sq_of_continuous_hasCompactSupport_pos hδ hf.continuous hs h0
  have hFneg : Integrable (fun t : ℝ => f (-t) / t ^ 2) := by
    refine integrable_div_sq_of_continuous_hasCompactSupport_pos hδ
      (hf.continuous.comp continuous_neg)
      (hs.comp_homeomorph (Homeomorph.neg ℝ)) ?_
    intro t ht
    rw [h0 (-t) (by rwa [abs_neg])]
  have hrefl : (∫ t in Ioi (0 : ℝ), f (-t) / t ^ 2) = ∫ t in Iic (0 : ℝ), f t / t ^ 2 := by
    have h := integral_comp_neg_Iic (c := (0 : ℝ)) (f := fun x : ℝ => f (-x) / x ^ 2)
    simpa using h.symm
  have hsplit : (∫ t in Ioi (0 : ℝ), f t / t ^ 2) + (∫ t in Iic (0 : ℝ), f t / t ^ 2)
      = ∫ t : ℝ, f t / t ^ 2 := by
    have h := integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hF
    rwa [Set.compl_Ioi] at h
  have hsymm : (∫ t in Ioi (0 : ℝ), (f t / t ^ 2 + f (-t) / t ^ 2)) = ∫ t : ℝ, f t / t ^ 2 := by
    rw [MeasureTheory.integral_add hF.integrableOn hFneg.integrableOn, hrefl]
    exact hsplit
  have hB : (∫ t in Ioi (0 : ℝ), φ t * (t ^ 2)⁻¹) = ∫ t : ℝ, f t / t ^ 2 := by
    rw [hφdef]
    trans ∫ t in Ioi (0 : ℝ), (f t / t ^ 2 + f (-t) / t ^ 2)
    · apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      ring
    · exact hsymm
  rw [hA, hB] at hkey
  exact hkey.symm

theorem abs_integral_Ioi_slope_le_integral_abs_div_sq {f : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) (h0 : ∀ t : ℝ, |t| ≤ δ → f t = 0) :
    |∫ t in Set.Ioi (0 : ℝ), (deriv f t - deriv f (-t)) / t| ≤ ∫ t : ℝ, |f t| / t ^ 2 := by
  rw [integral_Ioi_slope_eq_integral_div_sq_pos hδ hf hs h0]
  calc |∫ t : ℝ, f t / t ^ 2|
      ≤ ∫ t : ℝ, |f t / t ^ 2| := abs_integral_le_integral_abs
    _ = ∫ t : ℝ, |f t| / t ^ 2 := by
        apply integral_congr_ae
        filter_upwards with t
        rw [abs_div, abs_of_nonneg (sq_nonneg t)]

end Commons.Analysis.Calculus