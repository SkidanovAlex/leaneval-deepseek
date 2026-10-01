import Mathlib.Algebra.Order.Ring.Star
import Submission.Commons.Analysis.Complex.laplace_transform_bound_complex
import Submission.Commons.Analysis.Calculus.tendsto_integral_poisson_kernel
import Submission.Commons.Analysis.Fourier.exp_neg_abs_fourier

namespace Commons.Analysis.Complex
open Complex MeasureTheory intervalIntegral Filter Set Topology
open scoped Real Topology BigOperators
set_option autoImplicit false


private theorem laplace_bound_C2_neg {x₀ B : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B) {f : ℝ → ℂ}
    (hcont : ContinuousOn f (Set.Icc 0 x₀)) (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hf0 : f 0 = 0) (hfx₀ : f x₀ = 0) {z : ℂ} (hz : z.re < 0) :
    ‖∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t:ℂ))) * f t‖
      ≤ 3 * B * x₀ * Real.exp (-z.re * x₀) / ‖z‖^2 := by
  let fExt : ℝ → ℂ := fun t => if t ∈ Set.Icc (0:ℝ) x₀ then f t else 0
  have hF : ∀ t, fExt t = if t ∈ Set.Icc (0:ℝ) x₀ then f t else 0 := fun t => rfl
  have hfExt_eq : ∀ t ∈ Set.Ioo (0:ℝ) x₀, fExt t = f t := by
    intro t ht
    rw [hF t, if_pos ⟨le_of_lt ht.1, le_of_lt ht.2⟩]
  have hfExtIcc : ∀ t ∈ Set.Icc (0:ℝ) x₀, fExt t = f t := by
    intro t ht; rw [hF t, if_pos ht]
  have hcontExt : ContinuousOn fExt (Set.Icc 0 x₀) := ContinuousOn.congr hcont hfExtIcc
  have hf2Ext : ContDiffOn ℝ 2 fExt (Set.Ioo 0 x₀) :=
    ContDiffOn.congr hf2 (fun t ht => hfExt_eq t ht)
  let g : ℝ → ℂ := fun s => fExt (x₀ - s)
  have hx₀sub : Set.MapsTo (fun s : ℝ => x₀ - s) (Set.Ioo (0:ℝ) x₀) (Set.Ioo (0:ℝ) x₀) := by
    intro s hs; exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hmapIcc : Set.MapsTo (fun s : ℝ => x₀ - s) (Set.Icc (0:ℝ) x₀) (Set.Icc (0:ℝ) x₀) := by
    intro s hs; exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hcontg : ContinuousOn g (Set.Icc (0:ℝ) x₀) :=
    hcontExt.comp (by fun_prop) hmapIcc
  have hf2g : ContDiffOn ℝ 2 g (Set.Ioo (0:ℝ) x₀) :=
    hf2Ext.comp (by fun_prop : ContDiffOn ℝ 2 (fun s : ℝ => x₀ - s) (Set.Ioo 0 x₀)) hx₀sub
  have hg_apply : ∀ s, g s = fExt (x₀ - s) := fun s => rfl
  have hBndg : ∀ s ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 g s‖ ≤ B := by
    intro s hs
    have hs' : x₀ - s ∈ Set.Ioo (0:ℝ) x₀ := hx₀sub hs
    have h1 : iteratedDeriv 2 g s = iteratedDeriv 2 fExt (x₀ - s) := by
      simp only [g]
      have hcf := congrFun (iteratedDeriv_comp_const_sub (𝕜 := ℝ) 2 fExt x₀) s
      simpa using hcf
    rw [h1]
    have hev : fExt =ᶠ[𝓝 (x₀ - s)] f := by
      filter_upwards [IsOpen.mem_nhds isOpen_Ioo hs'] with y hy
      exact hfExt_eq y hy
    rw [hev.iteratedDeriv_eq 2]
    exact hBnd (x₀ - s) hs'
  have hvang : ∀ s : ℝ, x₀ ≤ s → g s = 0 := by
    intro s hs
    rcases eq_or_lt_of_le hs with h | h
    · rw [← h, hg_apply, sub_self, hF]
      rw [if_pos (show (0:ℝ) ∈ Set.Icc (0:ℝ) x₀ from ⟨le_refl 0, hx₀.le⟩)]
      exact hf0
    · have hmem : x₀ - s ∉ Set.Icc (0:ℝ) x₀ := by
        intro hh; linarith [hh.1]
      rw [hg_apply s, hF, if_neg hmem]
  have hf0g : g 0 = 0 := by
    rw [hg_apply 0, sub_zero, hF, if_pos ⟨le_of_lt hx₀, le_refl x₀⟩]; exact hfx₀
  have hw : (-z).re > 0 := by simpa using hz
  have hb := laplace_transform_bound_complex hx₀ hB hcontg hf2g hBndg hvang hf0g (z := -z) hw
  have hnorm : ‖(-z : ℂ)‖ = ‖z‖ := by simp
  rw [hnorm] at hb
  have hb' : ‖∫ s in (0:ℝ)..x₀, Complex.exp (z * (s:ℂ)) * g s‖ ≤ 3 * B * x₀ / ‖z‖^2 := by
    have heq : (∫ s in (0:ℝ)..x₀, Complex.exp (-((-z) * (s:ℂ))) * g s)
        = ∫ s in (0:ℝ)..x₀, Complex.exp (z * (s:ℂ)) * g s := by
      apply intervalIntegral.integral_congr; intro s hs; congr 1; ring
    rw [← heq]; exact hb
  have hstep1 : ∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t:ℂ))) * f t
      = ∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t:ℂ))) * fExt t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hx₀.le] at ht
    dsimp only
    rw [hfExtIcc t ht]
  have hstep2 : ∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t:ℂ))) * fExt t
      = Complex.exp (-(z * (x₀:ℂ))) * ∫ s in (0:ℝ)..x₀, Complex.exp (z * (s:ℂ)) * g s := by
    have hcl := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := x₀)
      (fun y : ℝ => Complex.exp (-(z * (y:ℂ))) * fExt y) x₀
    simp only [sub_self, sub_zero] at hcl
    rw [← hcl, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp only
    rw [hg_apply s]
    have h2 : Complex.exp (-(z * ((x₀ - s : ℝ):ℂ)))
        = Complex.exp (-(z * (x₀:ℂ))) * Complex.exp (z * (s:ℂ)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [h2]; ring
  rw [hstep1, hstep2, norm_mul]
  have hE : ‖Complex.exp (-(z * (x₀:ℂ)))‖ = Real.exp (-z.re * x₀) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im]
  rw [hE]
  calc Real.exp (-z.re * x₀) * ‖∫ s in (0:ℝ)..x₀, Complex.exp (z * (s:ℂ)) * g s‖
      ≤ Real.exp (-z.re * x₀) * (3 * B * x₀ / ‖z‖^2) :=
        mul_le_mul_of_nonneg_left hb' (Real.exp_nonneg _)
    _ = 3 * B * x₀ * Real.exp (-z.re * x₀) / ‖z‖^2 := by ring

private lemma hKcont {ε : ℝ} (hε : ε ≠ 0) :
    Continuous (fun u : ℝ => (2 * ε) / (u ^ 2 + ε ^ 2)) :=
  continuous_const.div (by fun_prop) (fun u => by
    have : 0 < u ^ 2 + ε ^ 2 := by nlinarith [sq_nonneg u, sq_pos_of_ne_zero hε]
    exact ne_of_gt this)

private lemma two_mul_div_sq_add_sq_le {ε u : ℝ} (hε : 0 < ε) :
    (2 * ε) / (u ^ 2 + ε ^ 2) ≤ 2 * (ε + ε⁻¹) * (1 + u ^ 2)⁻¹ := by
  rw [div_le_iff₀ (by positivity : (0:ℝ) < u ^ 2 + ε ^ 2)]
  rw [show 2 * (ε + ε⁻¹) * (1 + u ^ 2)⁻¹ * (u ^ 2 + ε ^ 2)
        = 2 * (ε + ε⁻¹) * (u ^ 2 + ε ^ 2) / (1 + u ^ 2) by ring]
  rw [le_div_iff₀ (by positivity : (0:ℝ) < 1 + u ^ 2)]
  have hεne : ε ≠ 0 := ne_of_gt hε
  field_simp
  nlinarith [sq_nonneg u, sq_nonneg ε, hε.le]

private lemma integrable_two_mul_div_sq_add_sq {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun u : ℝ => (2 * ε) / (u ^ 2 + ε ^ 2)) volume := by
  set C : ℝ := 2 * (ε + ε⁻¹) with hCdef
  refine Integrable.mono' (Integrable.const_mul integrable_inv_one_add_sq C) ?_ ?_
  · exact (hKcont (ne_of_gt hε)).aestronglyMeasurable
  · filter_upwards with u
    rw [Real.norm_of_nonneg (by positivity)]
    exact two_mul_div_sq_add_sq_le hε

private lemma integral_univ_two_mul_div_sq_add_sq {ε : ℝ} (hε : 0 < ε) :
    ∫ u : ℝ, (2 * ε) / (u ^ 2 + ε ^ 2) = 2 * Real.pi := by
  have hrew : ∀ u : ℝ, (2 * ε) / (u ^ 2 + ε ^ 2) = (2 / ε) * (1 + (u / ε) ^ 2)⁻¹ := by
    intro u; field_simp; ring
  simp_rw [hrew]
  rw [MeasureTheory.integral_const_mul]
  have hcomp := Measure.integral_comp_mul_left (fun t : ℝ => (1 + t ^ 2)⁻¹) (1/ε)
  have harg : ∀ x : ℝ, (1/ε) * x = x / ε := fun x => by ring
  simp_rw [harg] at hcomp
  rw [hcomp, show (1/ε)⁻¹ = ε by field_simp, abs_of_pos hε, integral_univ_inv_one_add_sq,
    smul_eq_mul]
  field_simp

private theorem tendsto_integral_poisson_kernel_line {φ : ℝ → ℂ} {M δ : ℝ} (hδ : 0 < δ)
    (hcont : ContinuousOn φ (Set.Icc (-δ) δ)) (hmeas : AEStronglyMeasurable φ volume)
    (_hM : 0 ≤ M) (hbound : ∀ u : ℝ, ‖φ u‖ ≤ M) :
    Filter.Tendsto (fun ε : ℝ => ∫ u : ℝ, ((2 * ε) / (u ^ 2 + ε ^ 2) : ℝ) • φ u)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((2 * Real.pi : ℝ) • φ 0)) := by
  have hδle : (-δ : ℝ) ≤ δ := by linarith
  set T : Set ℝ := Set.Icc (-δ) δ with hTdef
  have hTmeas : MeasurableSet T := measurableSet_Icc
  have hintR : ∀ ε : ℝ, 0 < ε → Integrable (fun u : ℝ => ((2 * ε) / (u ^ 2 + ε ^ 2) : ℝ) • φ u) volume := by
    intro ε hε
    set C : ℝ := 2 * (ε + ε⁻¹) with hCdef
    refine Integrable.mono' (Integrable.const_mul integrable_inv_one_add_sq (C * M)) ?_ ?_
    · exact AEStronglyMeasurable.smul (hKcont (ne_of_gt hε)).aestronglyMeasurable hmeas
    · filter_upwards with u
      have hKnn : 0 ≤ (2 * ε) / (u ^ 2 + ε ^ 2) := by positivity
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hKnn]
      have h1 := two_mul_div_sq_add_sq_le (ε := ε) hε (u := u)
      have hCnn : 0 ≤ C := by rw [hCdef]; positivity
      calc (2 * ε) / (u ^ 2 + ε ^ 2) * ‖φ u‖
          ≤ (C * (1 + u ^ 2)⁻¹) * M :=
            mul_le_mul h1 (hbound u) (norm_nonneg _) (mul_nonneg hCnn (inv_nonneg.mpr (by positivity)))
        _ = (C * M) * ((1 + u ^ 2)⁻¹) := by ring
  have hmid : Tendsto (fun ε : ℝ => ∫ u in T, ((2 * ε) / (u ^ 2 + ε ^ 2) : ℝ) • φ u)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((2 * Real.pi : ℝ) • φ 0)) := by
    have hbase := Commons.Analysis.Calculus.tendsto_integral_poisson_kernel (h := φ) hδ hcont
    refine hbase.congr' ?_
    filter_upwards with ε
    rw [hTdef, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hδle]
  have htail : Tendsto (fun ε : ℝ => ∫ u in Tᶜ, ((2 * ε) / (u ^ 2 + ε ^ 2) : ℝ) • φ u)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hg : Tendsto (fun ε : ℝ => M * (2 * Real.pi - 4 * Real.arctan (δ / ε)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have h1 : Tendsto (fun ε : ℝ => Real.arctan (δ / ε)) (nhdsWithin 0 (Set.Ioi 0))
          (nhds (Real.pi / 2)) := Commons.Analysis.Calculus.tendsto_arctan_div_self_nhdsGT hδ
      have h2 : Tendsto (fun ε : ℝ => 2 * Real.pi - 4 * Real.arctan (δ / ε))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (2 * Real.pi - 4 * (Real.pi/2))) :=
        tendsto_const_nhds.sub (h1.const_mul 4)
      have h3 := h2.const_mul M
      have : 2 * Real.pi - 4 * (Real.pi / 2) = 0 := by ring
      simpa [this] using h3
    refine squeeze_zero' ?_ ?_ hg
    · filter_upwards with ε; exact norm_nonneg _
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : (0:ℝ) < ε := hε
      have hKint : Integrable (fun u : ℝ => ((2*ε)/(u^2+ε^2):ℝ)) volume :=
        integrable_two_mul_div_sq_add_sq hε'
      have hTcompl : ∫ u in Tᶜ, ((2*ε)/(u^2+ε^2):ℝ) = 2*Real.pi - 4*Real.arctan (δ/ε) := by
        have hfull := integral_univ_two_mul_div_sq_add_sq hε'
        have hT : ∫ u in T, ((2*ε)/(u^2+ε^2):ℝ) = 4 * Real.arctan (δ/ε) := by
          rw [hTdef, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hδle,
            Commons.Analysis.Calculus.integral_two_mul_s_div_sq_add_sq hε' δ]
        have hc := integral_add_compl hTmeas hKint
        rw [hT, hfull] at hc
        linarith [hc]
      have hnorm_le : ∀ u : ℝ,
          ‖((2 * ε) / (u ^ 2 + ε ^ 2) : ℝ) • φ u‖ ≤ M * ((2*ε)/(u^2+ε^2)) := by
        intro u
        have hKnn : 0 ≤ (2*ε)/(u^2+ε^2) := by positivity
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hKnn]
        rw [mul_comm ((2*ε)/(u^2+ε^2)) ‖φ u‖]
        exact mul_le_mul_of_nonneg_right (hbound u) hKnn
      have hnorm_int : Integrable (fun u : ℝ => ‖((2 * ε) / (u ^ 2 + ε ^ 2) : ℝ) • φ u‖)
          (volume.restrict Tᶜ) := (hintR ε hε').norm.integrableOn
      have hbnd_int : Integrable (fun u : ℝ => M * ((2*ε)/(u^2+ε^2))) (volume.restrict Tᶜ) :=
        (hKint.const_mul M).integrableOn
      calc ‖∫ u in Tᶜ, ((2 * ε) / (u ^ 2 + ε ^ 2) : ℝ) • φ u‖
          ≤ ∫ u in Tᶜ, ‖((2 * ε) / (u ^ 2 + ε ^ 2) : ℝ) • φ u‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ u in Tᶜ, M * ((2*ε)/(u^2+ε^2)) :=
            integral_mono hnorm_int hbnd_int hnorm_le
        _ = M * ∫ u in Tᶜ, ((2*ε)/(u^2+ε^2):ℝ) := by rw [MeasureTheory.integral_const_mul]
        _ = M * (2 * Real.pi - 4 * Real.arctan (δ / ε)) := by rw [hTcompl]
  have hsum := hmid.add htail
  simp only [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [← integral_add_compl hTmeas (hintR ε hε)]

private lemma integrable_exp_neg_abs {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun τ : ℝ => Real.exp (-(ε * |τ|))) volume := by
  have hpos : IntegrableOn (fun τ : ℝ => Real.exp (-(ε * |τ|))) (Set.Ioi 0) volume :=
    (integrableOn_exp_mul_Ioi (a := -ε) (by linarith) 0).congr_fun
      (fun τ hτ => by simp only [Set.mem_Ioi] at hτ; rw [abs_of_pos hτ]; ring_nf)
      measurableSet_Ioi
  have hcomp := (integrableOn_exp_mul_Ioi (a := -ε) (by linarith) 0).comp_neg
  rw [show -Set.Ioi (0:ℝ) = Set.Iio 0 by ext x; simp [Set.mem_Iio]] at hcomp
  have hneg : IntegrableOn (fun τ : ℝ => Real.exp (-(ε * |τ|))) (Set.Iio 0) volume :=
    hcomp.congr_fun
      (fun τ hτ => by simp only [Set.mem_Iio] at hτ; rw [abs_of_neg hτ]; ring_nf)
      measurableSet_Iio
  have hzero : IntegrableOn (fun τ : ℝ => Real.exp (-(ε * |τ|))) {0} volume :=
    IntegrableOn.of_measure_zero (measure_singleton 0)
  rw [← integrableOn_univ]
  rw [show (Set.univ : Set ℝ) = (Set.Ioi 0 ∪ Set.Iio 0) ∪ {0} from by
    ext x
    simp only [Set.mem_univ, Set.mem_union, Set.mem_Ioi, Set.mem_Iio, Set.mem_singleton_iff, true_iff]
    rcases lt_trichotomy x 0 with h | h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
    · exact Or.inl (Or.inl h)]
  exact (hpos.union hneg).union hzero

private lemma inv_eq_neg_integral {A : ℂ} (hA : A.re < 0) (τ : ℝ) :
    (A - (τ:ℂ)*Complex.I)⁻¹
      = - ∫ v : ℝ in Set.Ioi 0, Complex.exp ((A - (τ:ℂ)*Complex.I) * (v:ℂ)) := by
  have hre : (A - (τ:ℂ)*Complex.I).re < 0 := by
    rw [show (A - (τ:ℂ)*Complex.I).re = A.re by
      simp [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]]
    exact hA
  have h := integral_exp_mul_complex_Ioi (a := A - (τ:ℂ)*Complex.I) hre 0
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero] at h
  rw [h, inv_eq_one_div]
  ring

private theorem integral_exp_neg_abs_div_neg_re_tendsto_zero {A : ℂ} (hA : A.re < 0) {b : ℝ} (hb : 0 < b) :
    Filter.Tendsto (fun ε : ℝ => ∫ τ : ℝ,
        Complex.exp (-(ε * |τ|)) * Complex.exp (-(((τ * b : ℝ) : ℂ) * Complex.I))
          / (A - (τ : ℂ) * Complex.I))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  set C : ℝ := 2 / (b^2 * (-A.re)) with hCdef
  have hAreneg : 0 < -A.re := neg_pos.mpr hA
  have hCnn : 0 ≤ C := by rw [hCdef]; positivity
  have hf2 : Integrable (fun v : ℝ => Real.exp (A.re * v)) (volume.restrict (Set.Ioi 0)) :=
    (integrableOn_exp_mul_Ioi hA 0)
  -- The key identity for ε > 0.
  have hkey : ∀ ε : ℝ, 0 < ε →
      (∫ τ : ℝ, Complex.exp (-(ε * |τ|)) * Complex.exp (-(((τ * b : ℝ) : ℂ) * Complex.I))
          / (A - (τ : ℂ) * Complex.I))
      = - ∫ v : ℝ in Set.Ioi 0, Complex.exp (A * (v:ℂ)) * ((2*ε/(ε^2 + (b+v)^2) : ℝ) : ℂ) := by
    intro ε hε
    -- integrability of the double integrand
    have hf1 : Integrable (fun τ : ℝ => Real.exp (-(ε*|τ|))) volume := integrable_exp_neg_abs hε
    have hg : Integrable (fun p : ℝ × ℝ => Real.exp (-(ε*|p.1|)) * Real.exp (A.re * p.2))
        (volume.prod (volume.restrict (Set.Ioi 0))) := Integrable.mul_prod hf1 hf2
    set F : ℝ → ℝ → ℂ := fun τ v =>
      Complex.exp (-(ε * |τ|)) * Complex.exp (-(((τ * b : ℝ) : ℂ) * Complex.I))
        * Complex.exp ((A - (τ:ℂ)*Complex.I) * (v:ℂ)) with hF
    have hnorm : ∀ τ v : ℝ, ‖F τ v‖ = Real.exp (-(ε*|τ|)) * Real.exp (A.re * v) := by
      intro τ v
      simp only [hF]
      rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp, Complex.norm_exp]
      have h1 : (-(↑ε * ↑|τ| : ℂ)).re = -(ε * |τ|) := by simp
      have h2 : (-(↑(τ * b) * Complex.I)).re = 0 := by
        simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      have h3 : ((A - ↑τ * Complex.I) * ↑v).re = A.re * v := by
        simp [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
          Complex.I_im]
      rw [h1, h2, h3, Real.exp_zero, mul_one]
    have hFint : Integrable (Function.uncurry F) (volume.prod (volume.restrict (Set.Ioi 0))) := by
      refine Integrable.mono' hg ?_ ?_
      · exact (by fun_prop : Continuous (Function.uncurry F)).aestronglyMeasurable
      · filter_upwards with p
        obtain ⟨τ, v⟩ := p
        simp only [Function.uncurry_apply_pair]
        rw [hnorm τ v]
    have hswap := integral_integral_swap hFint
    rw [show (∫ τ : ℝ, Complex.exp (-(ε * |τ|)) * Complex.exp (-(((τ * b : ℝ) : ℂ) * Complex.I))
          / (A - (τ : ℂ) * Complex.I))
        = - ∫ τ : ℝ, ∫ v : ℝ, F τ v ∂(volume.restrict (Set.Ioi 0)) from by
      rw [← MeasureTheory.integral_neg]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with τ
      rw [div_eq_mul_inv, inv_eq_neg_integral hA τ, mul_neg, ← MeasureTheory.integral_const_mul]]
    rw [hswap]
    congr 1
    -- inner τ-integral
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    have hinner : (∫ τ : ℝ, F τ v)
        = Complex.exp (A*(v:ℂ)) * ((2*ε/(ε^2+(b+v)^2):ℝ):ℂ) := by
      have hfac : ∀ τ : ℝ, F τ v = Complex.exp (A*(v:ℂ)) *
          (Complex.exp (-(ε*|τ|)) * Complex.exp (-(((τ*(b+v):ℝ):ℂ)*Complex.I))) := by
        intro τ
        have hL : F τ v = Complex.exp ((A*(v:ℂ)) + (-(ε*|τ|) : ℂ) + (-(((τ*(b+v):ℝ):ℂ)*Complex.I))) := by
          simp only [hF]
          rw [← Complex.exp_add, ← Complex.exp_add]
          congr 1
          push_cast
          ring
        have hR : Complex.exp (A*(v:ℂ)) *
            (Complex.exp (-(ε*|τ|)) * Complex.exp (-(((τ*(b+v):ℝ):ℂ)*Complex.I)))
            = Complex.exp ((A*(v:ℂ)) + (-(ε*|τ|) : ℂ) + (-(((τ*(b+v):ℝ):ℂ)*Complex.I))) := by
          rw [← Complex.exp_add, ← Complex.exp_add]
          congr 1
          ring
        rw [hL, hR]
      simp_rw [hfac]
      rw [MeasureTheory.integral_const_mul,
        Commons.Analysis.Fourier.exp_neg_abs_fourier hε (ω := b+v)]
    exact hinner
  -- Bound for ε > 0
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hbdd : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
      ‖∫ τ : ℝ, Complex.exp (-(ε * |τ|)) * Complex.exp (-(((τ * b : ℝ) : ℂ) * Complex.I))
          / (A - (τ : ℂ) * Complex.I)‖ ≤ C * ε := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : (0:ℝ) < ε := hε
    rw [hkey ε hε', norm_neg]
    have hb2 : 0 < b^2 := by positivity
    have hbdd' : ∀ v : ℝ, v ∈ Set.Ioi 0 →
        ‖Complex.exp (A * (v:ℂ)) * ((2*ε/(ε^2 + (b+v)^2) : ℝ) : ℂ)‖
          ≤ (2*ε/b^2) * Real.exp (A.re * v) := by
      intro v hv
      have hv0 : 0 < v := hv
      rw [norm_mul, Complex.norm_exp,
        Complex.norm_of_nonneg (by positivity : (0:ℝ) ≤ 2*ε/(ε^2+(b+v)^2)),
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      have hden : b^2 ≤ (b+v)^2 := by nlinarith [hb, hv0]
      have hfrac : (2*ε)/(ε^2+(b+v)^2) ≤ 2*ε/b^2 := by
        rw [div_le_div_iff₀ (by positivity) hb2]; nlinarith [hden, hε'.le]
      rw [mul_comm (2*ε/b^2)]
      exact mul_le_mul_of_nonneg_left hfrac (Real.exp_nonneg _)
    calc ‖∫ v : ℝ in Set.Ioi 0, Complex.exp (A*(v:ℂ)) * ((2*ε/(ε^2+(b+v)^2):ℝ):ℂ)‖
        ≤ ∫ v : ℝ in Set.Ioi 0, ‖Complex.exp (A*(v:ℂ)) * ((2*ε/(ε^2+(b+v)^2):ℝ):ℂ)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ v : ℝ in Set.Ioi 0, (2*ε/b^2) * Real.exp (A.re*v) := by
          refine integral_mono_of_nonneg (Eventually.of_forall (fun v => norm_nonneg _))
            (hf2.const_mul (2*ε/b^2)) ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
          exact hbdd' v hv
      _ = (2*ε/b^2) * ∫ v in Set.Ioi 0, Real.exp (A.re*v) := by rw [MeasureTheory.integral_const_mul]
      _ = C * ε := by
          have hv : (∫ v in Set.Ioi 0, Real.exp (A.re*v)) = -(Real.exp (A.re*0))/A.re :=
            integral_exp_mul_Ioi hA 0
          rw [hv, mul_zero, Real.exp_zero, hCdef]
          field_simp
  have hg : Tendsto (fun ε : ℝ => C * ε) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    have hc : Tendsto (fun _ : ℝ => C) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 C) := tendsto_const_nhds
    have hid : Tendsto (fun ε : ℝ => ε) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) :=
      tendsto_id.mono_right (nhdsWithin_le_nhds : nhdsWithin (0:ℝ) (Set.Ioi 0) ≤ 𝓝 (0:ℝ))
    have h1 := hc.mul hid
    simpa using h1
  exact squeeze_zero'
    (f := fun ε : ℝ => ‖∫ τ : ℝ, Complex.exp (-(ε * |τ|)) * Complex.exp (-(((τ * b : ℝ) : ℂ) * Complex.I)) / (A - (τ : ℂ) * Complex.I)‖)
    (g := fun ε : ℝ => C * ε)
    (Eventually.of_forall (fun ε => norm_nonneg _)) hbdd hg

private lemma integral_exp_mul_lin {x₀ : ℝ} (hx₀ : 0 < x₀) {z : ℂ} (hz : z ≠ 0) :
    ∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t:ℂ))) * ((1 - (t:ℝ)/x₀ : ℝ) : ℂ)
      = 1/z + (Complex.exp (-(z * (x₀:ℂ))) - 1) / ((x₀:ℂ) * z^2) := by
  have hx₀ne : (x₀:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hx₀
  set G : ℝ → ℂ := fun t => Complex.exp (-(z*(t:ℂ))) *
      (-1/z + (t:ℂ)/((x₀:ℂ)*z) + 1/((x₀:ℂ)*z^2)) with hG
  have hderiv : ∀ t : ℝ, HasDerivAt G (Complex.exp (-(z*(t:ℂ))) * ((1 - (t:ℝ)/x₀ : ℝ) : ℂ)) t := by
    intro t
    have hE : HasDerivAt (fun s : ℝ => Complex.exp (-(z*(s:ℂ)))) (-z * Complex.exp (-(z*(t:ℂ)))) t := by
      have h1 : HasDerivAt (fun s : ℝ => (s:ℂ)) 1 t := by simpa using (hasDerivAt_id t).ofReal_comp
      have h2 : HasDerivAt (fun s : ℝ => z * (s:ℂ)) (z * 1) t := h1.const_mul z
      have h3 : HasDerivAt (fun s : ℝ => -(z*(s:ℂ))) (-(z*1)) t := h2.neg
      have h3' : HasDerivAt (fun s : ℝ => -(z*(s:ℂ))) (-z) t := by simpa using h3
      have h4 := h3'.cexp
      simpa [mul_comm] using h4
    have hA : HasDerivAt (fun s : ℝ => (-1/z + (s:ℂ)/((x₀:ℂ)*z) + 1/((x₀:ℂ)*z^2)))
        (1/((x₀:ℂ)*z)) t := by
      have h1 : HasDerivAt (fun s : ℝ => (s:ℂ)) 1 t := by simpa using (hasDerivAt_id t).ofReal_comp
      have h2 : HasDerivAt (fun s : ℝ => (s:ℂ)/((x₀:ℂ)*z)) (1/((x₀:ℂ)*z)) t := h1.div_const _
      have h3 := h2.const_add (-1/z)
      have h4 := h3.add_const (1/((x₀:ℂ)*z^2))
      simpa [add_assoc] using h4
    have hG' : HasDerivAt G ((-z * Complex.exp (-(z*(t:ℂ)))) *
        (-1/z + (t:ℂ)/((x₀:ℂ)*z) + 1/((x₀:ℂ)*z^2))
        + Complex.exp (-(z*(t:ℂ))) * (1/((x₀:ℂ)*z))) t := by
      rw [hG]; exact hE.mul hA
    refine hG'.congr_deriv ?_
    push_cast
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
      ((by fun_prop : Continuous (fun t : ℝ => Complex.exp (-(z*(t:ℂ))) * ((1 - (t:ℝ)/x₀ : ℝ) : ℂ))).intervalIntegrable _ _)]
  rw [hG]
  simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero]
  field_simp
  ring_nf


private lemma iteratedDeriv_two_affine (a b : ℂ) (t : ℝ) :
    iteratedDeriv 2 (fun s : ℝ => a * (s:ℂ) + b) t = 0 := by
  have h2 : iteratedDeriv 2 (fun s : ℝ => a * (s:ℂ) + b)
      = deriv (deriv (fun s : ℝ => a * (s:ℂ) + b)) := by
    rw [show (2:ℕ) = 1+1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2]
  have hd : deriv (fun s : ℝ => a * (s:ℂ) + b) = fun _ => a := by
    funext s
    have h1 : HasDerivAt (fun y : ℝ => (y:ℂ)) 1 s := (hasDerivAt_id s).ofReal_comp
    have h2' : HasDerivAt (fun y : ℝ => a*(y:ℂ) + b) (a*1) s := (h1.const_mul a).add_const b
    have h3 := h2'.deriv
    simpa using h3
  rw [hd]
  simp [deriv_const]

private lemma laplace_regularized_bound {x₀ B : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B) {f : ℝ → ℂ}
    (hcont : ContinuousOn f (Set.Icc 0 x₀)) (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0) {z : ℂ} (hz : z.re < 0) :
    ‖(∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t:ℂ))) * f t) - f 0 / z‖
      ≤ (3 * B * x₀ * Real.exp (-z.re * x₀)
          + ‖f 0‖ * (Real.exp (-z.re * x₀) + 1) / x₀) / ‖z‖^2 := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have hx₀ne : x₀ ≠ 0 := ne_of_gt hx₀
  have hfx₀ : f x₀ = 0 := hvan x₀ le_rfl
  have hχcont : Continuous (fun t : ℝ => ((1 - (t:ℝ)/x₀ : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_const.sub (continuous_id.div_const x₀))
  have hχcd : ContDiff ℝ 2 (fun t : ℝ => ((1 - (t:ℝ)/x₀ : ℝ) : ℂ)) := by
    have h1 : ContDiff ℝ 2 (fun t : ℝ => (1 - t/x₀ : ℝ)) :=
      contDiff_const.sub (contDiff_id.div_const x₀)
    exact Complex.ofRealCLM.contDiff.comp h1
  set h : ℝ → ℂ := fun t => f t - f 0 * ((1 - (t:ℝ)/x₀ : ℝ) : ℂ) with hh
  have hh0 : h 0 = 0 := by rw [hh]; simp only [zero_div, sub_zero, Complex.ofReal_one, mul_one, sub_self]
  have hhx₀ : h x₀ = 0 := by
    simp only [hh]
    rw [hfx₀, div_self hx₀ne]
    simp
  have hhcont : ContinuousOn h (Set.Icc 0 x₀) := by
    rw [hh]; exact hcont.sub (continuous_const.mul hχcont).continuousOn
  have hhf2 : ContDiffOn ℝ 2 h (Set.Ioo 0 x₀) := by
    rw [hh]; exact hf2.sub (contDiffOn_const.mul hχcd.contDiffOn)
  have hhBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 h t‖ ≤ B := by
    intro t ht
    have heq : iteratedDeriv 2 h t = iteratedDeriv 2 f t := by
      have hcd1 : ContDiffAt ℝ 2 f t := hf2.contDiffAt (Ioo_mem_nhds ht.1 ht.2)
      have hcd2 : ContDiffAt ℝ 2 (fun s : ℝ => f 0 * ((1 - (s:ℝ)/x₀ : ℝ):ℂ)) t :=
        (contDiffAt_const.mul hχcd.contDiffAt)
      have hsub : iteratedDeriv 2 (f - (fun s : ℝ => f 0 * ((1 - (s:ℝ)/x₀ : ℝ):ℂ))) t
          = iteratedDeriv 2 f t
            - iteratedDeriv 2 (fun s : ℝ => f 0 * ((1 - (s:ℝ)/x₀ : ℝ):ℂ)) t :=
        iteratedDeriv_sub hcd1 hcd2
      have hg0 : iteratedDeriv 2 (fun s : ℝ => f 0 * ((1 - (s:ℝ)/x₀ : ℝ):ℂ)) t = 0 := by
        have he : (fun s : ℝ => f 0 * ((1 - (s:ℝ)/x₀ : ℝ):ℂ))
            = (fun s : ℝ => (-(f 0/x₀)) * (s:ℂ) + f 0) := by
          funext s; push_cast; ring
        rw [he, iteratedDeriv_two_affine]
      rw [hh]
      change iteratedDeriv 2 (f - (fun s : ℝ => f 0 * ((1 - (s:ℝ)/x₀ : ℝ):ℂ))) t = iteratedDeriv 2 f t
      rw [hsub, hg0, sub_zero]
    rw [heq]; exact hBnd t ht
  have hbnd_h := laplace_bound_C2_neg hx₀ hB hhcont hhf2 hhBnd hh0 hhx₀ hz
  have hlin := integral_exp_mul_lin hx₀ hz0
  have hexpcont : Continuous (fun t : ℝ => Complex.exp (-(z*(t:ℂ)))) :=
    Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).neg)
  have hintf : IntervalIntegrable (fun t : ℝ => Complex.exp (-(z*(t:ℂ))) * f t) volume 0 x₀ :=
    (hexpcont.continuousOn.mul hcont).intervalIntegrable_of_Icc hx₀.le
  have hintg : IntervalIntegrable (fun t : ℝ => f 0 * (Complex.exp (-(z*(t:ℂ))) * ((1 - (t:ℝ)/x₀ : ℝ):ℂ))) volume 0 x₀ :=
    (continuous_const.continuousOn.mul (hexpcont.continuousOn.mul hχcont.continuousOn)).intervalIntegrable_of_Icc hx₀.le
  have hsplit : ∫ t in (0:ℝ)..x₀, Complex.exp (-(z*(t:ℂ))) * h t
      = (∫ t in (0:ℝ)..x₀, Complex.exp (-(z*(t:ℂ))) * f t)
        - f 0 * (∫ t in (0:ℝ)..x₀, Complex.exp (-(z*(t:ℂ))) * ((1 - (t:ℝ)/x₀ : ℝ):ℂ)) := by
    rw [show (fun t : ℝ => Complex.exp (-(z*(t:ℂ))) * h t)
        = (fun t : ℝ => Complex.exp (-(z*(t:ℂ))) * f t
            - f 0 * (Complex.exp (-(z*(t:ℂ))) * ((1 - (t:ℝ)/x₀ : ℝ):ℂ))) by
      funext t; rw [hh]; ring]
    rw [intervalIntegral.integral_sub hintf hintg, intervalIntegral.integral_const_mul]
  have hid : (∫ t in (0:ℝ)..x₀, Complex.exp (-(z*(t:ℂ))) * f t) - f 0 / z
      = (∫ t in (0:ℝ)..x₀, Complex.exp (-(z*(t:ℂ))) * h t)
        + f 0 * (Complex.exp (-(z * (x₀:ℂ))) - 1) / ((x₀:ℂ) * z^2) := by
    rw [hsplit, hlin]
    field_simp
    ring
  rw [hid]
  have hbnd2 : ‖f 0 * (Complex.exp (-(z*(x₀:ℂ))) - 1) / ((x₀:ℂ)*z^2)‖
      ≤ ‖f 0‖ * (Real.exp (-z.re * x₀) + 1) / (x₀ * ‖z‖^2) := by
    rw [norm_div, norm_mul, norm_mul, show ‖z^2‖ = ‖z‖^2 from norm_pow _ _,
      Complex.norm_of_nonneg hx₀.le]
    have h1 : ‖Complex.exp (-(z*(x₀:ℂ))) - 1‖ ≤ Real.exp (-z.re * x₀) + 1 := by
      calc ‖Complex.exp (-(z*(x₀:ℂ))) - 1‖ ≤ ‖Complex.exp (-(z*(x₀:ℂ)))‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
        _ = Real.exp (-z.re * x₀) + 1 := by
            rw [Complex.norm_exp, norm_one]
            congr 1
            simp [Complex.mul_re, Complex.neg_re]
    have hx₀n : (0:ℝ) < x₀ * ‖z‖^2 := by positivity
    rw [div_le_div_iff₀ hx₀n hx₀n]
    calc ‖f 0‖ * ‖Complex.exp (-(z*(x₀:ℂ))) - 1‖ * (x₀ * ‖z‖^2)
        ≤ ‖f 0‖ * (Real.exp (-z.re * x₀) + 1) * (x₀ * ‖z‖^2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)) (by positivity)
      _ = ‖f 0‖ * (Real.exp (-z.re * x₀) + 1) * (x₀ * ‖z‖^2) := rfl
  calc ‖(∫ t in (0:ℝ)..x₀, Complex.exp (-(z*(t:ℂ))) * h t)
          + f 0 * (Complex.exp (-(z*(x₀:ℂ))) - 1) / ((x₀:ℂ) * z^2)‖
      ≤ ‖∫ t in (0:ℝ)..x₀, Complex.exp (-(z*(t:ℂ))) * h t‖
          + ‖f 0 * (Complex.exp (-(z*(x₀:ℂ))) - 1) / ((x₀:ℂ) * z^2)‖ := norm_add_le _ _
    _ ≤ 3 * B * x₀ * Real.exp (-z.re * x₀) / ‖z‖^2
          + ‖f 0‖ * (Real.exp (-z.re * x₀) + 1) / (x₀ * ‖z‖^2) := add_le_add hbnd_h hbnd2
    _ = (3 * B * x₀ * Real.exp (-z.re * x₀)
          + ‖f 0‖ * (Real.exp (-z.re * x₀) + 1) / x₀) / ‖z‖^2 := by ring

/-- Twisted Laplace inversion with the `f(0)`-regularized kernel: for `s.re < α`, ... -/
theorem twisted_inversion_regularized {x₀ B : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B)
    {f : ℝ → ℂ} (hcont : ContinuousOn f (Set.Icc 0 x₀)) (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0)
    {L : ℝ} (hL : 1 < L) {s : ℂ} {α : ℝ} (hα : s.re < α)
    {m : ℕ} (hm : 2 ≤ m) :
    (∫ τ : ℝ, (m : ℂ) ^ (-(α : ℂ) - (τ : ℂ) * Complex.I) *
        ((∫ t in (0:ℝ)..x₀,
          Complex.exp (-(((s - ((α : ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ)) * (t : ℂ))) * f t)
          - f 0 / ((s - ((α : ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ))))
      = (2 * (Real.pi : ℂ) / (L : ℂ)) * (m : ℂ) ^ (-s) * f (Real.log m / L) := by
  have hLpos : 0 < L := by linarith
  have hm1 : 1 < m := by omega
  have hmpos : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hmne : (m:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hmpos)
  have hlogpos : 0 < Real.log m := Real.log_pos (by exact_mod_cast hm1)
  set σ : ℝ := s.re - α with hσdef
  have hσ : σ < 0 := by rw [hσdef]; linarith
  have hσne : σ ≠ 0 := ne_of_lt hσ
  set b : ℝ := Real.log m with hbdef
  have hb : 0 < b := by rw [hbdef]; exact hlogpos
  set tL : ℝ := b / L with htLdef
  set F : ℝ → ℂ := (fun τ : ℝ => (m:ℂ)^(-(α:ℂ)-(τ:ℂ)*Complex.I) *
      ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - ((α:ℂ)+(τ:ℂ)*Complex.I)) * (L:ℂ)) * (t:ℂ))) * f t)
        - f 0 / ((s - ((α:ℂ)+(τ:ℂ)*Complex.I)) * (L:ℂ)))) with hF
  have hnorm_e : ∀ τ : ℝ, ‖(m:ℂ)^(-(α:ℂ)-(τ:ℂ)*Complex.I)‖ = (m:ℝ)^(-α) := by
    intro τ
    rw [Complex.cpow_def_of_ne_zero hmne, Complex.norm_exp]
    have hlogre : (Complex.log ((m:ℂ))).re = Real.log m := by
      rw [Complex.log_re, show ‖((m:ℂ))‖ = (m:ℝ) from Complex.norm_of_nonneg hmpos.le]
    have hlogim : (Complex.log ((m:ℂ))).im = 0 := by
      rw [Complex.log_im, ← Complex.ofReal_natCast m, Complex.arg_ofReal_of_nonneg hmpos.le]
    rw [show (Complex.log ((m:ℂ)) * (-(α:ℂ)-(τ:ℂ)*Complex.I)).re = Real.log m * (-α) from by
      rw [Complex.mul_re, hlogre, hlogim]
      simp only [zero_mul, sub_zero]
      rw [show (-(α:ℂ)-(τ:ℂ)*Complex.I).re = -α from by
        simp [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
          Complex.I_im]]]
    rw [← Real.rpow_def_of_pos hmpos]

  -- bound on the regularized transform
  have hkey_bound : ∀ τ : ℝ, ‖F τ‖ ≤
      ((m:ℝ)^(-α) * (3*B*x₀*Real.exp (-(L*σ*x₀))
        + ‖f 0‖*(Real.exp (-(L*σ*x₀))+1)/x₀)) * (L^2 * (σ^2 + (s.im-τ)^2))⁻¹ := by
    intro τ
    set z : ℂ := (s - ((α:ℂ)+(τ:ℂ)*Complex.I)) * (L:ℂ) with hzdef
    have hzre : z.re = L*σ := by
      rw [hzdef, hσdef]
      simp only [Complex.mul_re, Complex.sub_re, Complex.add_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    have hzre' : z.re < 0 := by rw [hzre]; exact mul_neg_of_pos_of_neg hLpos hσ
    have hznorm : ‖z‖^2 = L^2 * (σ^2 + (s.im-τ)^2) := by
      rw [hzdef, norm_mul, mul_pow, Complex.norm_of_nonneg hLpos.le, Complex.sq_norm,
        Complex.normSq_apply]
      rw [show (s - ((α:ℂ)+(τ:ℂ)*Complex.I)).re = σ from by
        rw [hσdef]
        simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im]]
      rw [show (s - ((α:ℂ)+(τ:ℂ)*Complex.I)).im = s.im - τ from by
        simp [Complex.sub_im, Complex.add_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im]]
      ring
    have hbnd := laplace_regularized_bound hx₀ hB hcont hf2 hBnd hvan hzre'
    rw [hznorm] at hbnd
    have hFτ : F τ = (m:ℂ)^(-(α:ℂ)-(τ:ℂ)*Complex.I) *
        ((∫ t in (0:ℝ)..x₀, Complex.exp (-(z*(t:ℂ))) * f t) - f 0 / z) := by
      rw [hF, hzdef]
    rw [hFτ, norm_mul, hnorm_e τ]
    calc (m:ℝ)^(-α) * ‖(∫ t in (0:ℝ)..x₀, Complex.exp (-(z*(t:ℂ))) * f t) - f 0 / z‖
        ≤ (m:ℝ)^(-α) * ((3*B*x₀*Real.exp (-z.re*x₀)
            + ‖f 0‖*(Real.exp (-z.re*x₀)+1)/x₀) / (L^2 * (σ^2 + (s.im-τ)^2))) :=
          mul_le_mul_of_nonneg_left hbnd (Real.rpow_nonneg hmpos.le _)
      _ = (m:ℝ)^(-α) * (3*B*x₀*Real.exp (-(L*σ*x₀))
            + ‖f 0‖*(Real.exp (-(L*σ*x₀))+1)/x₀) * (L^2 * (σ^2 + (s.im-τ)^2))⁻¹ := by
          rw [hzre, div_eq_mul_inv]; ring

  -- the dominating function
  set Kc : ℝ := (m:ℝ)^(-α) * (3*B*x₀*Real.exp (-(L*σ*x₀))
      + ‖f 0‖*(Real.exp (-(L*σ*x₀))+1)/x₀) with hKcdef
  set g : ℝ → ℝ := fun τ => Kc * (L^2 * (σ^2 + (s.im-τ)^2))⁻¹ with hgdef
  have hg_int : Integrable g volume := by
    have hh : Integrable (fun τ : ℝ => (1 + ((τ - s.im)/σ)^2)⁻¹) volume := by
      have h1 : Integrable (fun u : ℝ => (1 + u^2)⁻¹) volume := integrable_inv_one_add_sq
      have h2 : Integrable (fun u : ℝ => (1 + (u - s.im/σ)^2)⁻¹) volume := h1.comp_sub_right (s.im/σ)
      have h3 : Integrable (fun τ : ℝ => (1 + (τ/σ - s.im/σ)^2)⁻¹) volume :=
        h2.comp_mul_right' (inv_ne_zero hσne)
      refine h3.congr ?_
      filter_upwards with τ
      congr 2
      rw [sub_div]
    rw [show g = fun τ : ℝ => (Kc/(L^2*σ^2)) * (1 + ((τ - s.im)/σ)^2)⁻¹ from by
      funext τ; rw [hgdef]; field_simp; ring]
    exact hh.const_mul _
  have hFbound : ∀ τ : ℝ, ‖F τ‖ ≤ g τ := by
    intro τ
    have h := hkey_bound τ
    rw [hgdef]
    exact h
  -- F is continuous (hence a.e. strongly measurable)
  have hfEcont : Continuous (fun t : ℝ => f (max 0 (min t x₀))) :=
    hcont.comp_continuous (continuous_const.max (continuous_id.min continuous_const))
      (fun t => ⟨le_max_left _ _, max_le hx₀.le (min_le_right _ _)⟩)
  have hIcont : Continuous (fun τ : ℝ => ∫ t in (0:ℝ)..x₀,
      Complex.exp (-(((s - ((α:ℂ)+(τ:ℂ)*Complex.I)) * (L:ℂ)) * (t:ℂ))) * f t) := by
    have heq : (fun τ : ℝ => ∫ t in (0:ℝ)..x₀,
        Complex.exp (-(((s - ((α:ℂ)+(τ:ℂ)*Complex.I)) * (L:ℂ)) * (t:ℂ))) * f t)
        = (fun τ : ℝ => ∫ t in (0:ℝ)..x₀,
        Complex.exp (-(((s - ((α:ℂ)+(τ:ℂ)*Complex.I)) * (L:ℂ)) * (t:ℂ))) * f (max 0 (min t x₀))) := by
      funext τ
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hx₀.le] at ht
      simp only [min_eq_left ht.2, max_eq_right ht.1]
    rw [heq]
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (τ : ℝ) (t : ℝ) => Complex.exp (-(((s - ((α:ℂ)+(τ:ℂ)*Complex.I)) * (L:ℂ)) * (t:ℂ)))
        * f (max 0 (min t x₀)))
      (by
        unfold Function.uncurry
        show Continuous (fun a : ℝ × ℝ =>
          Complex.exp (-(((s - ((α:ℂ)+(a.1:ℂ)*Complex.I)) * (L:ℂ)) * (a.2:ℂ)))
            * f (max 0 (min a.2 x₀)))
        have hg1 : Continuous (fun p : ℝ × ℝ =>
            -(((s - ((α:ℂ)+(p.1:ℂ)*Complex.I)) * (L:ℂ)) * (p.2:ℂ))) := by fun_prop
        exact (Complex.continuous_exp.comp hg1).mul (hfEcont.comp continuous_snd)) 0 x₀
  have hβcL_ne : ∀ τ : ℝ, (s - ((α:ℂ)+(τ:ℂ)*Complex.I)) * (L:ℂ) ≠ 0 := by
    intro τ
    apply mul_ne_zero _ (Complex.ofReal_ne_zero.mpr hLpos.ne')
    intro hh
    have hre : (s - ((α:ℂ)+(τ:ℂ)*Complex.I)).re = 0 := by rw [hh]; simp
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, add_zero] at hre
    linarith [hα, hre]
  have h3cont : Continuous (fun τ : ℝ => f 0 / ((s - ((α:ℂ)+(τ:ℂ)*Complex.I)) * (L:ℂ))) :=
    continuous_const.div ((by fun_prop : Continuous (fun τ : ℝ => s - ((α:ℂ)+(τ:ℂ)*Complex.I))).mul continuous_const)
      hβcL_ne
  have h1cont : Continuous (fun τ : ℝ => (m:ℂ)^(-(α:ℂ)-(τ:ℂ)*Complex.I)) := by
    have hrw : (fun τ : ℝ => (m:ℂ)^(-(α:ℂ)-(τ:ℂ)*Complex.I))
        = fun τ : ℝ => Complex.exp ((Real.log m : ℂ) * (-(α:ℂ)-(τ:ℂ)*Complex.I)) := by
      funext τ
      have hlog : Complex.log ((m:ℂ)) = (Real.log m : ℂ) := by
        rw [← Complex.ofReal_natCast m]
        exact (Complex.ofReal_log hmpos.le).symm
      rw [Complex.cpow_def_of_ne_zero hmne, hlog]
    rw [hrw]; fun_prop
  have hF_aes : AEStronglyMeasurable F volume := by
    rw [show F = fun τ : ℝ => (m:ℂ)^(-(α:ℂ)-(τ:ℂ)*Complex.I) *
        ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - ((α:ℂ)+(τ:ℂ)*Complex.I)) * (L:ℂ)) * (t:ℂ))) * f t)
          - f 0 / ((s - ((α:ℂ)+(τ:ℂ)*Complex.I)) * (L:ℂ))) from by rw [hF]]
    exact h1cont.aestronglyMeasurable.mul
      (hIcont.aestronglyMeasurable.sub h3cont.aestronglyMeasurable)

  have hdconv : Tendsto (fun ε : ℝ => ∫ τ, (Real.exp (-(ε*|τ|)) : ℂ) * F τ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ τ, F τ)) := by
    apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence g
    · filter_upwards with ε
      exact (by fun_prop : Continuous (fun τ : ℝ => (Real.exp (-(ε*|τ|)) : ℂ))).aestronglyMeasurable.mul hF_aes
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      filter_upwards with τ
      rw [norm_mul]
      have h1 : ‖(Real.exp (-(ε*|τ|)) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_of_nonneg (Real.exp_nonneg _), Real.exp_le_one_iff]
        exact neg_nonpos.mpr (mul_nonneg hε.le (abs_nonneg τ))
      calc ‖(Real.exp (-(ε*|τ|)) : ℂ)‖ * ‖F τ‖ ≤ 1 * ‖F τ‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = ‖F τ‖ := one_mul _
        _ ≤ g τ := hFbound τ
    · exact hg_int
    · filter_upwards with τ
      have h1 : Tendsto (fun ε : ℝ => -(ε*|τ|)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        have h2 : Tendsto (fun ε : ℝ => ε) (nhdsWithin 0 (Set.Ioi 0)) (nhds (0:ℝ)) :=
          tendsto_id.mono_right (nhdsWithin_le_nhds : nhdsWithin (0:ℝ) (Set.Ioi 0) ≤ 𝓝 (0:ℝ))
        simpa using (h2.mul_const (|τ|)).neg
      have h3 : Tendsto (fun ε : ℝ => (Real.exp (-(ε*|τ|)) : ℂ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
        have h4 : Tendsto (fun ε : ℝ => Real.exp (-(ε*|τ|))) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
          simpa [Function.comp_def, Real.exp_zero] using
            (Real.continuous_exp.continuousAt.tendsto.comp h1)
        exact Complex.continuous_ofReal.continuousAt.tendsto.comp h4
      have h6 := h3.mul (tendsto_const_nhds : Tendsto (fun _ : ℝ => F τ)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (F τ)))
      simpa only [one_mul] using h6

  have hinner : ∀ ε t : ℝ, 0 < ε →
      (∫ τ : ℝ, (Real.exp (-(ε*|τ|)) : ℂ) * (m:ℂ)^(-(α:ℂ)-(τ:ℂ)*Complex.I) *
        Complex.exp (-(((s - ((α:ℂ)+(τ:ℂ)*Complex.I)) * (L:ℂ)) * (t:ℂ))))
      = (((m:ℝ)^(-α) : ℝ) : ℂ) * Complex.exp (-((s - (α:ℂ)) * (L:ℂ) * (t:ℂ)))
          * ((2*ε/(ε^2 + (Real.log m - L*t)^2) : ℝ) : ℂ) := by
    intro ε t hε
    have hlog : Complex.log ((m:ℂ)) = (Real.log m : ℂ) := by
      rw [← Complex.ofReal_natCast m]
      exact (Complex.ofReal_log hmpos.le).symm
    set X : ℝ → ℂ := fun τ => (-(↑ε*↑|τ|))
        + (Real.log m : ℂ) * (-(α:ℂ)-(τ:ℂ)*Complex.I)
        + (-(((s - ((α:ℂ)+(τ:ℂ)*Complex.I)) * (L:ℂ)) * (t:ℂ))) with hX
    have hL : ∀ τ : ℝ, (Real.exp (-(ε*|τ|)) : ℂ) * (m:ℂ)^(-(α:ℂ)-(τ:ℂ)*Complex.I) *
        Complex.exp (-(((s - ((α:ℂ)+(τ:ℂ)*Complex.I)) * (L:ℂ)) * (t:ℂ))) = Complex.exp (X τ) := by
      intro τ
      rw [Complex.cpow_def_of_ne_zero hmne, hlog,
        show (Real.exp (-(ε*|τ|)) : ℂ) = Complex.exp (-(↑ε*↑|τ|)) from by
          rw [Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul],
        ← Complex.exp_add, ← Complex.exp_add]
    have hR : ∀ τ : ℝ, ((((m:ℝ)^(-α) : ℝ) : ℂ) * Complex.exp (-((s - (α:ℂ)) * (L:ℂ) * (t:ℂ))))
          * (Complex.exp (-(↑ε*↑|τ|)) * Complex.exp (-(((τ*(Real.log m - L*t):ℝ):ℂ)*Complex.I)))
        = Complex.exp (X τ) := by
      intro τ
      rw [Real.rpow_def_of_pos hmpos, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add,
        ← Complex.exp_add]
      congr 1
      simp only [hX]
      push_cast
      ring
    have hexp : ∀ τ : ℝ, (Real.exp (-(ε*|τ|)) : ℂ) * (m:ℂ)^(-(α:ℂ)-(τ:ℂ)*Complex.I) *
        Complex.exp (-(((s - ((α:ℂ)+(τ:ℂ)*Complex.I)) * (L:ℂ)) * (t:ℂ)))
        = ((((m:ℝ)^(-α) : ℝ) : ℂ) * Complex.exp (-((s - (α:ℂ)) * (L:ℂ) * (t:ℂ)))) *
            (Complex.exp (-(↑ε*↑|τ|)) * Complex.exp (-(((τ*(Real.log m - L*t):ℝ):ℂ)*Complex.I))) :=
      fun τ => (hL τ).trans (hR τ).symm
    simp_rw [hexp]
    rw [MeasureTheory.integral_const_mul]
    rw [Commons.Analysis.Fourier.exp_neg_abs_fourier hε (ω := Real.log m - L*t)]

  obtain ⟨Mf, hMf⟩ := (isCompact_Icc (a := (0:ℝ)) (b := x₀)).exists_bound_of_continuousOn hcont
  have hMfnn : 0 ≤ Mf := le_trans (norm_nonneg _) (hMf 0 ⟨le_refl 0, hx₀.le⟩)
  -- the continuous version of `f` agrees with `f` on `[0,x₀]`
  have hfEeq : ∀ t ∈ Set.Icc (0:ℝ) x₀, f (max 0 (min t x₀)) = f t := by
    intro t ht
    rw [min_eq_left ht.2, max_eq_right ht.1]
  have hint_eq : ∀ (z : ℂ) (τ : ℝ), (∫ t in (0:ℝ)..x₀, Complex.exp (-(z*(t:ℂ))) * f t)
      = ∫ t in (0:ℝ)..x₀, Complex.exp (-(z*(t:ℂ))) * f (max 0 (min t x₀)) := by
    intro z τ
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hx₀.le] at ht
    dsimp only
    rw [show f (max 0 (min t x₀)) = f t from hfEeq t ht]
  have hFub : ∀ ε : ℝ, 0 < ε →
      (∫ τ : ℝ, (Real.exp (-(ε*|τ|)) : ℂ) * (m:ℂ)^(-(α:ℂ)-(τ:ℂ)*Complex.I) *
        (∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - ((α:ℂ)+(τ:ℂ)*Complex.I)) * (L:ℂ)) * (t:ℂ))) * f t))
      = ∫ t in (0:ℝ)..x₀, ((((m:ℝ)^(-α) : ℝ) : ℂ) * Complex.exp (-((s - (α:ℂ)) * (L:ℂ) * (t:ℂ)))
          * ((2*ε/(ε^2 + (Real.log m - L*t)^2) : ℝ) : ℂ)) * f t := by
    intro ε hε
    set G : ℝ → ℝ → ℂ := fun τ t => (Real.exp (-(ε*|τ|)) : ℂ) * (m:ℂ)^(-(α:ℂ)-(τ:ℂ)*Complex.I) *
      Complex.exp (-(((s - ((α:ℂ)+(τ:ℂ)*Complex.I)) * (L:ℂ)) * (t:ℂ))) * f (max 0 (min t x₀)) with hG
    have hGcont : Continuous (fun p : ℝ × ℝ => (Real.exp (-(ε*|p.1|)) : ℂ) *
        (m:ℂ)^(-(α:ℂ)-(p.1:ℂ)*Complex.I) *
        Complex.exp (-(((s - ((α:ℂ)+(p.1:ℂ)*Complex.I)) * (L:ℂ)) * (p.2:ℂ))) * f (max 0 (min p.2 x₀))) := by
      have h1 : Continuous (fun p : ℝ × ℝ => (Real.exp (-(ε*|p.1|)) : ℂ)) :=
        Complex.continuous_ofReal.comp (Real.continuous_exp.comp
          ((continuous_const.mul (continuous_abs.comp continuous_fst)).neg))
      have h2 : Continuous (fun p : ℝ × ℝ => (m:ℂ)^(-(α:ℂ)-(p.1:ℂ)*Complex.I)) :=
        h1cont.comp continuous_fst
      have h3 : Continuous (fun p : ℝ × ℝ => Complex.exp (-(((s - ((α:ℂ)+(p.1:ℂ)*Complex.I)) * (L:ℂ)) * (p.2:ℂ)))) :=
        Complex.continuous_exp.comp (by fun_prop)
      exact ((h1.mul h2).mul h3).mul (hfEcont.comp (by fun_prop))
    have huncurry : Function.uncurry G = (fun p : ℝ × ℝ => (Real.exp (-(ε*|p.1|)) : ℂ) *
        (m:ℂ)^(-(α:ℂ)-(p.1:ℂ)*Complex.I) *
        Complex.exp (-(((s - ((α:ℂ)+(p.1:ℂ)*Complex.I)) * (L:ℂ)) * (p.2:ℂ))) * f (max 0 (min p.2 x₀))) := by
      funext p; simp only [Function.uncurry, hG]
    have hCc : 0 ≤ ((m:ℝ)^(-α) * Real.exp ((α - s.re)*L*x₀) * Mf) := by positivity
    have hGbdd : ∀ τ t : ℝ, t ∈ Set.Ioc (0:ℝ) x₀ → ‖G τ t‖ ≤ ((m:ℝ)^(-α) * Real.exp ((α - s.re)*L*x₀) * Mf) * Real.exp (-(ε*|τ|)) := by
      intro τ t ht
      have hft : ‖f (max 0 (min t x₀))‖ ≤ Mf := hMf _ ⟨le_max_left _ _, max_le hx₀.le (min_le_right _ _)⟩
      have hnorme : ‖(m:ℂ)^(-(α:ℂ)-(τ:ℂ)*Complex.I)‖ = (m:ℝ)^(-α) := hnorm_e τ
      have hz : ‖Complex.exp (-(((s - ((α:ℂ)+(τ:ℂ)*Complex.I)) * (L:ℂ)) * (t:ℂ)))‖
          = Real.exp ((α - s.re)*L*t) := by
        rw [Complex.norm_exp]
        congr 1
        simp only [Complex.neg_re, Complex.mul_re, Complex.sub_re, Complex.add_re, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, add_zero,
          sub_zero]
        ring
      rw [hG]
      simp only
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_of_nonneg (Real.exp_nonneg _), hnorme, hz]
      have h3 : Real.exp ((α - s.re)*L*t) ≤ Real.exp ((α - s.re)*L*x₀) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left ht.2 (by positivity)
      calc Real.exp (-(ε*|τ|)) * (m:ℝ)^(-α) * Real.exp ((α - s.re)*L*t) * ‖f (max 0 (min t x₀))‖
          ≤ Real.exp (-(ε*|τ|)) * (m:ℝ)^(-α) * Real.exp ((α - s.re)*L*x₀) * Mf := by gcongr
        _ = ((m:ℝ)^(-α) * Real.exp ((α - s.re)*L*x₀) * Mf) * Real.exp (-(ε*|τ|)) := by ring
    have hGi : Integrable (Function.uncurry G) (volume.prod (volume.restrict (Set.Ioc (0:ℝ) x₀))) := by
      have hf1 : Integrable (fun τ : ℝ => ((m:ℝ)^(-α) * Real.exp ((α - s.re)*L*x₀) * Mf) * Real.exp (-(ε*|τ|))) volume :=
        (integrable_exp_neg_abs hε).const_mul _
      have hf2 : Integrable (fun _ : ℝ => (1:ℝ)) (volume.restrict (Set.Ioc (0:ℝ) x₀)) :=
        integrable_const (1:ℝ)
      refine Integrable.mono' (Integrable.mul_prod hf1 hf2) ?_ ?_
      · rw [huncurry]; exact hGcont.aestronglyMeasurable
      · have hae : ∀ᵐ p : ℝ × ℝ ∂(volume.prod (volume.restrict (Set.Ioc (0:ℝ) x₀))), p.2 ∈ Set.Ioc (0:ℝ) x₀ := by
          rw [Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_snd)]
          filter_upwards with x
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with y hy
          exact hy
        filter_upwards [hae] with p hp
        obtain ⟨τ, t⟩ := p
        rw [Function.uncurry_apply_pair]
        simp only [mul_one]
        exact hGbdd τ t hp
    have hswap := MeasureTheory.integral_integral_swap hGi
    rw [show (∫ τ : ℝ, (Real.exp (-(ε*|τ|)) : ℂ) * (m:ℂ)^(-(α:ℂ)-(τ:ℂ)*Complex.I) *
        (∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - ((α:ℂ)+(τ:ℂ)*Complex.I)) * (L:ℂ)) * (t:ℂ))) * f t))
        = ∫ τ : ℝ, ∫ t : ℝ, G τ t ∂(volume.restrict (Set.Ioc (0:ℝ) x₀)) from by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with τ
      have haux : (∫ t : ℝ, G τ t ∂(volume.restrict (Set.Ioc (0:ℝ) x₀)))
          = (Real.exp (-(ε*|τ|)) : ℂ) * (m:ℂ)^(-(α:ℂ)-(τ:ℂ)*Complex.I) *
              (∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - ((α:ℂ)+(τ:ℂ)*Complex.I)) * (L:ℂ)) * (t:ℂ))) * f t) := by
        rw [show (∫ t : ℝ, G τ t ∂(volume.restrict (Set.Ioc (0:ℝ) x₀)))
            = ∫ t in Set.Ioc (0:ℝ) x₀, ((Real.exp (-(ε*|τ|)) : ℂ) * (m:ℂ)^(-(α:ℂ)-(τ:ℂ)*Complex.I)) *
                (Complex.exp (-(((s - ((α:ℂ)+(τ:ℂ)*Complex.I)) * (L:ℂ)) * (t:ℂ))) * f (max 0 (min t x₀))) from by
          apply setIntegral_congr_fun measurableSet_Ioc
          intro t ht; simp only [hG]; ring]
        rw [MeasureTheory.integral_const_mul, ← intervalIntegral.integral_of_le hx₀.le,
          ← hint_eq ((s - ((α:ℂ)+(τ:ℂ)*Complex.I)) * (L:ℂ)) τ]
      exact haux.symm]
    rw [hswap]
    rw [intervalIntegral.integral_of_le hx₀.le]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    have hInn : (∫ τ : ℝ, G τ t)
        = ((((m:ℝ)^(-α) : ℝ) : ℂ) * Complex.exp (-((s - (α:ℂ)) * (L:ℂ) * (t:ℂ)))
          * ((2*ε/(ε^2 + (Real.log m - L*t)^2) : ℝ) : ℂ)) * f (max 0 (min t x₀)) := by
      rw [show (∫ τ : ℝ, G τ t) = (∫ τ : ℝ, (Real.exp (-(ε*|τ|)) : ℂ) *
          (m:ℂ)^(-(α:ℂ)-(τ:ℂ)*Complex.I) *
          Complex.exp (-(((s - ((α:ℂ)+(τ:ℂ)*Complex.I)) * (L:ℂ)) * (t:ℂ)))) * f (max 0 (min t x₀)) from by
        rw [hG, MeasureTheory.integral_mul_const]]
      rw [hinner ε t hε]
    rw [hInn, hfEeq t ⟨le_of_lt ht.1, ht.2⟩]

  have hAre : (s - (α:ℂ)).re < 0 := by
    rw [show (s - (α:ℂ)).re = s.re - α by simp]; linarith
  have hreg : Tendsto (fun ε : ℝ => ∫ τ : ℝ, (Real.exp (-(ε*|τ|)) : ℂ) *
      (m:ℂ)^(-(α:ℂ)-(τ:ℂ)*Complex.I) / ((s - ((α:ℂ)+(τ:ℂ)*Complex.I)) * (L:ℂ)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h := integral_exp_neg_abs_div_neg_re_tendsto_zero (A := s - (α:ℂ)) (b := Real.log m) hAre hlogpos
    have hfac : ∀ ε : ℝ, (∫ τ : ℝ, (Real.exp (-(ε*|τ|)) : ℂ) *
        (m:ℂ)^(-(α:ℂ)-(τ:ℂ)*Complex.I) / ((s - ((α:ℂ)+(τ:ℂ)*Complex.I)) * (L:ℂ)))
        = ((((m:ℝ)^(-α) : ℝ) : ℂ) * (L:ℂ)⁻¹) * (∫ τ : ℝ, Complex.exp (-(ε*|τ|)) *
            Complex.exp (-(((τ*Real.log m : ℝ) : ℂ) * Complex.I))
              / ((s - (α:ℂ)) - (τ:ℂ) * Complex.I)) := by
      intro ε
      rw [show (∫ τ : ℝ, (Real.exp (-(ε*|τ|)) : ℂ) * (m:ℂ)^(-(α:ℂ)-(τ:ℂ)*Complex.I)
              / ((s - ((α:ℂ)+(τ:ℂ)*Complex.I)) * (L:ℂ)))
          = ∫ τ : ℝ, ((((m:ℝ)^(-α) : ℝ) : ℂ) * (L:ℂ)⁻¹) * (Complex.exp (-(ε*|τ|)) *
              Complex.exp (-(((τ*Real.log m : ℝ) : ℂ) * Complex.I))
                / ((s - (α:ℂ)) - (τ:ℂ) * Complex.I)) from by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with τ
        have hlog : Complex.log ((m:ℂ)) = (Real.log m : ℂ) := by
          rw [← Complex.ofReal_natCast m]; exact (Complex.ofReal_log hmpos.le).symm
        have hcp : (m:ℂ)^(-(α:ℂ)-(τ:ℂ)*Complex.I)
            = (((m:ℝ)^(-α) : ℝ) : ℂ) * Complex.exp (-(((τ*Real.log m : ℝ) : ℂ) * Complex.I)) := by
          rw [Complex.cpow_def_of_ne_zero hmne, hlog,
            show (Real.log m : ℂ) * (-(α:ℂ)-(τ:ℂ)*Complex.I)
              = (Real.log m : ℂ) * (-(α:ℂ)) + (Real.log m : ℂ) * (-((τ:ℂ)*Complex.I)) by ring,
            Complex.exp_add]
          have h1 : Complex.exp ((Real.log m : ℂ) * (-(α:ℂ))) = (((m:ℝ)^(-α) : ℝ) : ℂ) := by
            rw [show (Real.log m : ℂ) * (-(α:ℂ)) = ↑(Real.log m * (-α)) by push_cast; ring,
              ← Complex.ofReal_exp, ← Real.rpow_def_of_pos hmpos]
          have h2 : Complex.exp ((Real.log m : ℂ) * (-((τ:ℂ)*Complex.I)))
              = Complex.exp (-(((τ*Real.log m : ℝ) : ℂ) * Complex.I)) := by
            congr 1; rw [show (Real.log m : ℂ) * (-((τ:ℂ)*Complex.I))
              = -(((τ*Real.log m : ℝ) : ℂ)*Complex.I) by push_cast; ring]
          rw [h1, h2]
        rw [hcp]
        have hb2 : (s - ((α:ℂ)+(τ:ℂ)*Complex.I)) * (L:ℂ) = ((s - (α:ℂ)) - (τ:ℂ)*Complex.I) * (L:ℂ) := by ring
        rw [hb2]
        field_simp
        rw [show (↑(Real.exp (-(ε*|τ|))) : ℂ) = Complex.exp (-(↑ε*↑|τ|)) from by
          rw [Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul]]
        ring]
      rw [MeasureTheory.integral_const_mul]
    rw [show (fun ε : ℝ => ∫ τ : ℝ, (Real.exp (-(ε*|τ|)) : ℂ) *
        (m:ℂ)^(-(α:ℂ)-(τ:ℂ)*Complex.I) / ((s - ((α:ℂ)+(τ:ℂ)*Complex.I)) * (L:ℂ)))
        = fun ε : ℝ => ((((m:ℝ)^(-α) : ℝ) : ℂ) * (L:ℂ)⁻¹) *
          (∫ τ : ℝ, Complex.exp (-(ε*|τ|)) * Complex.exp (-(((τ*Real.log m : ℝ) : ℂ) * Complex.I))
            / ((s - (α:ℂ)) - (τ:ℂ) * Complex.I)) from funext hfac]
    have h2 := h.const_mul ((((m:ℝ)^(-α) : ℝ) : ℂ) * (L:ℂ)⁻¹)
    simpa only [Complex.ofReal_log hmpos.le, Complex.ofReal_natCast, mul_zero] using h2


  -- ============================ MAIN-PART LIMIT ============================
  have hfEeq' : f (Real.log m / L) = f (max 0 (min (Real.log m / L) x₀)) := by
    rcases lt_or_ge (Real.log m / L) x₀ with h | h
    · rw [min_eq_left h.le, max_eq_right (by positivity : (0:ℝ) ≤ Real.log m / L)]
    · rw [min_eq_right h, max_eq_right hx₀.le, hvan x₀ le_rfl, hvan _ h]

  set a2 : ℝ := -Real.log m with ha2def
  set b2 : ℝ := L * x₀ - Real.log m with hb2def
  have ha2b2 : a2 ≤ b2 := by rw [ha2def, hb2def]; nlinarith [hLpos, hx₀]
  have ha2neg : a2 < 0 := by rw [ha2def]; linarith [hlogpos]
  set g' : ℝ → ℂ := fun u => (((m:ℝ)^(-α) : ℝ) : ℂ) *
      Complex.exp (-((s - (α:ℂ)) * ((u + Real.log m : ℝ) : ℂ))) *
        f (max 0 (min ((u + Real.log m) / L) x₀)) with hg'def
  set φ : ℝ → ℂ := fun u => if a2 < u ∧ u ≤ b2 then g' u else 0 with hφdef

  have hg'cont : Continuous g' := by
    rw [hg'def]
    refine (continuous_const.mul ?_).mul (hfEcont.comp (by fun_prop))
    exact Complex.continuous_exp.comp (by fun_prop)

  have hg'zero : g' b2 = 0 := by
    simp only [hg'def, hb2def]
    rw [show (L * x₀ - Real.log m) + Real.log m = L * x₀ from by ring,
      show L * x₀ / L = x₀ from mul_div_cancel_left₀ x₀ (ne_of_gt hLpos)]
    rw [min_self, max_eq_right hx₀.le, hvan x₀ le_rfl, mul_zero]

  set ψ : ℝ → ℂ := fun u => if u ≤ b2 then g' u else 0 with hψdef
  have hψcont : Continuous ψ := by
    have h1 : ContinuousOn ψ (Set.Iic b2) := by
      refine ContinuousOn.congr hg'cont.continuousOn (fun u hu => ?_)
      simp only [hψdef]
      rw [if_pos (show u ≤ b2 from hu)]
    have h2 : ContinuousOn ψ (Set.Ici b2) := by
      refine ContinuousOn.congr (continuousOn_const : ContinuousOn (fun _ : ℝ => (0:ℂ)) (Set.Ici b2)) (fun u hu => ?_)
      simp only [hψdef]
      by_cases h : u ≤ b2
      · rw [if_pos h, le_antisymm h hu, hg'zero]
      · rw [if_neg h]
    have h3 := h1.union_of_isClosed h2 isClosed_Iic isClosed_Ici
    rwa [Set.Iic_union_Ici, continuousOn_univ] at h3

  have hφcont : ContinuousOn φ (Set.Icc (-(Real.log m / 2)) (Real.log m / 2)) := by
    refine hψcont.continuousOn.congr (fun u hu => ?_)
    simp only [hφdef, hψdef]
    have ha2u : a2 < u := by rw [ha2def]; linarith [hu.1, hlogpos]
    by_cases h : u ≤ b2
    · rw [if_pos ⟨ha2u, h⟩, if_pos h]
    · rw [if_neg (fun hc => h hc.2), if_neg h]

  have hφbnd : ∀ u : ℝ, ‖φ u‖ ≤ (m:ℝ)^(-α) * Real.exp ((α - s.re) * L * x₀) * Mf := by
    intro u
    have hCnn : 0 ≤ (m:ℝ)^(-α) * Real.exp ((α - s.re) * L * x₀) * Mf := by positivity
    simp only [hφdef]
    by_cases h : a2 < u ∧ u ≤ b2
    · rw [if_pos h]
      simp only [hg'def]
      have hexpb : ‖Complex.exp (-((s - (α:ℂ)) * ((u + Real.log m : ℝ) : ℂ)))‖
          = Real.exp ((α - s.re) * (u + Real.log m)) := by
        rw [Complex.norm_exp]; congr 1
        rw [Complex.neg_re, Complex.mul_re]
        simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
        ring
      have hnormm : ‖(((m:ℝ)^(-α) : ℝ) : ℂ)‖ = (m:ℝ)^(-α) := Complex.norm_of_nonneg (by positivity)
      rw [norm_mul, norm_mul, hnormm, hexpb]
      have hfarg : ‖f (max 0 (min ((u + Real.log m) / L) x₀))‖ ≤ Mf :=
        hMf _ ⟨le_max_left _ _, max_le hx₀.le (min_le_right _ _)⟩
      have hleexp : Real.exp ((α - s.re) * (u + Real.log m)) ≤ Real.exp ((α - s.re) * L * x₀) := by
        rw [Real.exp_le_exp]
        have h1 : u + Real.log m ≤ L * x₀ := by rw [hb2def] at h; linarith [h.2]
        nlinarith [hLpos, h.1, ha2def, hlogpos, h1, sub_neg.mpr hα]
      calc (m:ℝ)^(-α) * Real.exp ((α - s.re) * (u + Real.log m))
              * ‖f (max 0 (min ((u + Real.log m) / L) x₀))‖
          ≤ (m:ℝ)^(-α) * Real.exp ((α - s.re) * L * x₀)
              * ‖f (max 0 (min ((u + Real.log m) / L) x₀))‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hleexp (by positivity)) (norm_nonneg _)
        _ ≤ (m:ℝ)^(-α) * Real.exp ((α - s.re) * L * x₀) * Mf :=
            mul_le_mul_of_nonneg_left hfarg (by positivity)
    · rw [if_neg h]
      simp only [norm_zero]
      exact hCnn

  have hφaes : AEStronglyMeasurable φ volume := by
    have h : AEStronglyMeasurable ((Set.Ioc a2 b2).indicator g') volume :=
      (hg'cont.aestronglyMeasurable).indicator measurableSet_Ioc
    convert h using 1
    ext u
    simp only [hφdef, Set.indicator_apply, Set.mem_Ioc]

  have hMφnn : 0 ≤ (m:ℝ)^(-α) * Real.exp ((α - s.re) * L * x₀) * Mf := by positivity

  have hexp_id' : ((((m:ℝ)^(-α) : ℝ)) : ℂ) *
      Complex.exp (-((s - (α:ℂ)) * ((Real.log m : ℝ) : ℂ))) = (m:ℂ)^(-s) := by
    have hlogm : Complex.log ((m:ℂ)) = (Real.log m : ℂ) := by
      rw [← Complex.ofReal_natCast m]; exact (Complex.ofReal_log hmpos.le).symm
    rw [show ((((m:ℝ)^(-α) : ℝ)) : ℂ) = (m:ℂ)^(-(α:ℂ)) from by
      rw [Complex.ofReal_cpow hmpos.le (-α), Complex.ofReal_neg, Complex.ofReal_natCast]]
    rw [show -((s - (α:ℂ)) * ((Real.log m : ℝ):ℂ)) = Complex.log (m:ℂ) * (-(s - (α:ℂ))) by
      rw [hlogm]; ring]
    rw [← Complex.cpow_def_of_ne_zero hmne]
    rw [← Complex.cpow_add (-(α:ℂ)) (-(s - (α:ℂ))) hmne]
    congr 1
    ring

  have hφ0 : φ 0 = (m:ℂ)^(-s) * f (Real.log m / L) := by
    simp only [hφdef]
    by_cases hb2nn : 0 ≤ b2
    · rw [if_pos ⟨ha2neg, hb2nn⟩]
      simp only [hg'def, zero_add]
      rw [hfEeq', hexp_id']
    · rw [if_neg (fun hc => hb2nn hc.2)]
      have hxlt : x₀ < Real.log m / L := by
        rw [lt_div_iff₀ hLpos]
        rw [hb2def] at hb2nn; push_neg at hb2nn; linarith
      rw [hvan _ hxlt.le, mul_zero]

  -- the substitution step
  have hK : ∀ ε : ℝ, (∫ t in (0:ℝ)..x₀, ((((m:ℝ)^(-α) : ℝ) : ℂ) *
      Complex.exp (-((s - (α:ℂ)) * (L:ℂ) * (t:ℂ))) * ((2*ε/(ε^2 + (Real.log m - L*t)^2) : ℝ) : ℂ)) * f t)
      = (L:ℂ)⁻¹ * ∫ u : ℝ, ((2*ε/(u^2+ε^2) : ℝ) : ℂ) * φ u := by
    intro ε
    set Kb : ℝ → ℂ := fun u => ((2*ε/(u^2+ε^2) : ℝ) : ℂ) * φ u with hKb
    have hKb_eq : (∫ u : ℝ, Kb u) = ∫ u : ℝ, ((2*ε/(u^2+ε^2) : ℝ) : ℂ) * φ u := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with u
      simp only [hKb]
    rw [← hKb_eq]
    have hcongr : (∫ t in (0:ℝ)..x₀, ((((m:ℝ)^(-α) : ℝ) : ℂ) *
        Complex.exp (-((s - (α:ℂ)) * (L:ℂ) * (t:ℂ))) * ((2*ε/(ε^2 + (Real.log m - L*t)^2) : ℝ) : ℂ)) * f t)
        = ∫ t in (0:ℝ)..x₀, Kb (L*t + (-(Real.log m))) := by
      apply intervalIntegral.integral_congr_ae
      refine Filter.Eventually.of_forall (fun t ht => ?_)
      rw [Set.uIoc_of_le hx₀.le] at ht
      have htIcc : t ∈ Set.Icc (0:ℝ) x₀ := ⟨le_of_lt ht.1, ht.2⟩
      have hgt : a2 < L*t - Real.log m := by rw [ha2def]; nlinarith [ht.1, hLpos]
      have hle : L*t - Real.log m ≤ b2 := by rw [hb2def]; nlinarith [ht.2, hLpos]
      simp only [hKb]
      simp only [hφdef]
      rw [if_pos ⟨hgt, hle⟩]
      simp only [hg'def]
      rw [show (L*t + (-(Real.log m))) + Real.log m = L*t from by ring]
      rw [show (L*t)/L = t from mul_div_cancel_left₀ t (ne_of_gt hLpos)]
      rw [hfEeq t htIcc, Complex.ofReal_mul]
      rw [show ε^2 + (Real.log m - L*t)^2 = ((L*t - Real.log m)^2 + ε^2) from by ring]
      ring
    rw [hcongr]
    rw [intervalIntegral.integral_comp_mul_add Kb (ne_of_gt hLpos) (-(Real.log m))]
    rw [show L * (0:ℝ) + -(Real.log m) = a2 from by rw [ha2def, mul_zero, zero_add]]
    rw [show L * x₀ + -(Real.log m) = b2 from by rw [hb2def]; ring]
    rw [Complex.real_smul, Complex.ofReal_inv]
    rw [intervalIntegral.integral_of_le ha2b2]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Ioc a2 b2)
      (f := Kb) (by
        intro u hu
        simp only [hKb, hφdef]
        rw [if_neg (by simpa only [Set.mem_Ioc] using hu), mul_zero])]

  have hmainlim : Tendsto (fun ε : ℝ => ∫ t in (0:ℝ)..x₀, ((((m:ℝ)^(-α) : ℝ) : ℂ) *
      Complex.exp (-((s - (α:ℂ)) * (L:ℂ) * (t:ℂ))) * ((2*ε/(ε^2 + (Real.log m - L*t)^2) : ℝ) : ℂ)) * f t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((2*(Real.pi:ℂ)/(L:ℂ)) * (m:ℂ)^(-s) * f (Real.log m / L))) := by
    rw [show (fun ε : ℝ => ∫ t in (0:ℝ)..x₀, ((((m:ℝ)^(-α) : ℝ) : ℂ) *
        Complex.exp (-((s - (α:ℂ)) * (L:ℂ) * (t:ℂ))) * ((2*ε/(ε^2 + (Real.log m - L*t)^2) : ℝ) : ℂ)) * f t)
        = fun ε : ℝ => (L:ℂ)⁻¹ * ∫ u : ℝ, ((2*ε/(u^2+ε^2) : ℝ) : ℂ) * φ u from funext hK]
    have hδ : 0 < Real.log m / 2 := by positivity
    have hpois := tendsto_integral_poisson_kernel_line hδ hφcont hφaes hMφnn hφbnd
    have hpois2 : Tendsto (fun ε : ℝ => ∫ u : ℝ, ((2*ε/(u^2+ε^2) : ℝ) : ℂ) * φ u)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds ((2*Real.pi : ℂ) * φ 0)) := by
      simpa only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat] using hpois
    rw [hφ0] at hpois2
    have h3 := hpois2.const_mul ((L:ℂ)⁻¹)
    rw [show (2*(Real.pi:ℂ)/(L:ℂ)) * (m:ℂ)^(-s) * f (Real.log m / L)
        = (L:ℂ)⁻¹ * ((2*Real.pi:ℂ) * ((m:ℂ)^(-s) * f (Real.log m / L))) from by ring]
    exact h3

  -- ======================= ASSEMBLY =======================
  have hInn_bound : ∀ τ : ℝ, ‖(∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - ((α:ℂ)+(τ:ℂ)*Complex.I)) * (L:ℂ)) * (t:ℂ))) * f t)‖
      ≤ Mf * Real.exp ((α - s.re) * L * x₀) * x₀ := by
    intro τ
    have hpt : ∀ t ∈ Set.uIoc (0:ℝ) x₀,
        ‖Complex.exp (-(((s - ((α:ℂ)+(τ:ℂ)*Complex.I)) * (L:ℂ)) * (t:ℂ))) * f t‖
          ≤ Mf * Real.exp ((α - s.re) * L * x₀) := by
      intro t ht
      rw [Set.uIoc_of_le hx₀.le] at ht
      have htIcc : t ∈ Set.Icc (0:ℝ) x₀ := ⟨le_of_lt ht.1, ht.2⟩
      rw [norm_mul, Complex.norm_exp]
      have hre : (-(((s - ((α:ℂ)+(τ:ℂ)*Complex.I)) * (L:ℂ)) * (t:ℂ))).re = -((s.re - α) * L * t) := by
        simp [Complex.neg_re, Complex.mul_re, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im]
      rw [hre]
      have hft : ‖f t‖ ≤ Mf := hMf t htIcc
      have hexp : Real.exp (-((s.re - α) * L * t)) ≤ Real.exp ((α - s.re) * L * x₀) := by
        rw [Real.exp_le_exp,
          show -((s.re - α) * L * t) = (α - s.re) * (L * t) from by ring,
          show (α - s.re) * L * x₀ = (α - s.re) * (L * x₀) from by ring]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht.2 hLpos.le)
          (by linarith [hα])
      calc Real.exp (-((s.re - α) * L * t)) * ‖f t‖
          ≤ Real.exp ((α - s.re) * L * x₀) * Mf := by gcongr
        _ = Mf * Real.exp ((α - s.re) * L * x₀) := by ring
    calc ‖∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - ((α:ℂ)+(τ:ℂ)*Complex.I)) * (L:ℂ)) * (t:ℂ))) * f t‖
        ≤ (Mf * Real.exp ((α - s.re) * L * x₀)) * |x₀ - 0| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hpt
      _ = Mf * Real.exp ((α - s.re) * L * x₀) * x₀ := by rw [sub_zero, abs_of_pos hx₀]

  have hP1int : ∀ ε : ℝ, 0 < ε → Integrable (fun τ : ℝ =>
      (Real.exp (-(ε*|τ|)) : ℂ) * (m:ℂ)^(-(α:ℂ)-(τ:ℂ)*Complex.I) *
        (∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - ((α:ℂ)+(τ:ℂ)*Complex.I)) * (L:ℂ)) * (t:ℂ))) * f t)) volume := by
    intro ε hε
    set C1 : ℝ := (m:ℝ)^(-α) * (Mf * Real.exp ((α - s.re) * L * x₀) * x₀) with hC1def
    have hC1nn : 0 ≤ C1 := by rw [hC1def]; positivity
    refine Integrable.mono' ((integrable_exp_neg_abs hε).const_mul C1) ?_ ?_
    · exact (((Complex.continuous_ofReal.comp (Real.continuous_exp.comp
        ((continuous_const.mul continuous_abs).neg))).mul h1cont).mul hIcont).aestronglyMeasurable
    · filter_upwards with τ
      rw [norm_mul, norm_mul, Complex.norm_of_nonneg (Real.exp_nonneg _), hnorm_e τ]
      calc Real.exp (-(ε*|τ|)) * (m:ℝ)^(-α) * ‖(∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - ((α:ℂ)+(τ:ℂ)*Complex.I)) * (L:ℂ)) * (t:ℂ))) * f t)‖
          ≤ Real.exp (-(ε*|τ|)) * (m:ℝ)^(-α) * (Mf * Real.exp ((α - s.re) * L * x₀) * x₀) := by
            exact mul_le_mul_of_nonneg_left (hInn_bound τ) (by positivity)
        _ = C1 * Real.exp (-(ε*|τ|)) := by rw [hC1def]; ring

  have hP2int : ∀ ε : ℝ, 0 < ε → Integrable (fun τ : ℝ =>
      (Real.exp (-(ε*|τ|)) : ℂ) * (m:ℂ)^(-(α:ℂ)-(τ:ℂ)*Complex.I) / ((s - ((α:ℂ)+(τ:ℂ)*Complex.I)) * (L:ℂ))) volume := by
    intro ε hε
    set C2 : ℝ := (m:ℝ)^(-α) / ((α - s.re) * L) with hC2def
    have hC2nn : 0 ≤ C2 := by rw [hC2def]; positivity
    refine Integrable.mono' ((integrable_exp_neg_abs hε).const_mul C2) ?_ ?_
    · apply Continuous.aestronglyMeasurable
      have hnum : Continuous (fun τ : ℝ => (Real.exp (-(ε*|τ|)) : ℂ) * (m:ℂ)^(-(α:ℂ)-(τ:ℂ)*Complex.I)) :=
        (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
          ((continuous_const.mul continuous_abs).neg))).mul h1cont
      have hden : Continuous (fun τ : ℝ => (s - ((α:ℂ)+(τ:ℂ)*Complex.I)) * (L:ℂ)) :=
        ((by fun_prop : Continuous (fun τ : ℝ => s - ((α:ℂ)+(τ:ℂ)*Complex.I))).mul continuous_const)
      exact hnum.div hden (fun τ => hβcL_ne τ)
    · filter_upwards with τ
      rw [norm_div, norm_mul, Complex.norm_of_nonneg (Real.exp_nonneg _), hnorm_e τ]
      have hnormβ : (α - s.re) * L ≤ ‖(s - ((α:ℂ)+(τ:ℂ)*Complex.I)) * (L:ℂ)‖ := by
        rw [norm_mul, Complex.norm_of_nonneg hLpos.le]
        have h1 := Complex.abs_re_le_norm (s - ((α:ℂ)+(τ:ℂ)*Complex.I))
        have h2 : (s - ((α:ℂ)+(τ:ℂ)*Complex.I)).re = s.re - α := by
          simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im]
        rw [h2, abs_of_neg (by linarith [hα] : s.re - α < 0), neg_sub] at h1
        exact mul_le_mul_of_nonneg_right h1 hLpos.le
      have hC2' : Real.exp (-(ε*|τ|)) * (m:ℝ)^(-α) / ((α - s.re) * L) = C2 * Real.exp (-(ε*|τ|)) := by
        rw [hC2def]; ring
      rw [← hC2']
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hnormβ

  have hsplit : ∀ ε : ℝ, 0 < ε →
      (∫ τ : ℝ, (Real.exp (-(ε*|τ|)) : ℂ) * F τ)
      = (∫ t in (0:ℝ)..x₀, ((((m:ℝ)^(-α) : ℝ) : ℂ) * Complex.exp (-((s - (α:ℂ)) * (L:ℂ) * (t:ℂ)))
          * ((2*ε/(ε^2 + (Real.log m - L*t)^2) : ℝ) : ℂ)) * f t)
        - f 0 * (∫ τ : ℝ, (Real.exp (-(ε*|τ|)) : ℂ) * (m:ℂ)^(-(α:ℂ)-(τ:ℂ)*Complex.I) / ((s - ((α:ℂ)+(τ:ℂ)*Complex.I)) * (L:ℂ))) := by
    intro ε hε
    rw [← hFub ε hε]
    rw [show (∫ τ : ℝ, (Real.exp (-(ε*|τ|)) : ℂ) * F τ)
        = ∫ τ : ℝ, ((Real.exp (-(ε*|τ|)) : ℂ) * (m:ℂ)^(-(α:ℂ)-(τ:ℂ)*Complex.I) *
              (∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - ((α:ℂ)+(τ:ℂ)*Complex.I)) * (L:ℂ)) * (t:ℂ))) * f t))
            - f 0 * ((Real.exp (-(ε*|τ|)) : ℂ) * (m:ℂ)^(-(α:ℂ)-(τ:ℂ)*Complex.I) / ((s - ((α:ℂ)+(τ:ℂ)*Complex.I)) * (L:ℂ))) from by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with τ
      simp only [hF]
      ring]
    rw [MeasureTheory.integral_sub (hP1int ε hε) ((hP2int ε hε).const_mul (f 0))]
    rw [MeasureTheory.integral_const_mul]

  have hRlim : Tendsto (fun ε : ℝ => f 0 * (∫ τ : ℝ, (Real.exp (-(ε*|τ|)) : ℂ) *
      (m:ℂ)^(-(α:ℂ)-(τ:ℂ)*Complex.I) / ((s - ((α:ℂ)+(τ:ℂ)*Complex.I)) * (L:ℂ))))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f 0 * 0)) := hreg.const_mul (f 0)

  have hconv2 : Tendsto (fun ε : ℝ => (∫ t in (0:ℝ)..x₀, ((((m:ℝ)^(-α) : ℝ) : ℂ) *
        Complex.exp (-((s - (α:ℂ)) * (L:ℂ) * (t:ℂ))) * ((2*ε/(ε^2 + (Real.log m - L*t)^2) : ℝ) : ℂ)) * f t)
        - f 0 * (∫ τ : ℝ, (Real.exp (-(ε*|τ|)) : ℂ) * (m:ℂ)^(-(α:ℂ)-(τ:ℂ)*Complex.I) / ((s - ((α:ℂ)+(τ:ℂ)*Complex.I)) * (L:ℂ))))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((2*(Real.pi:ℂ)/(L:ℂ)) * (m:ℂ)^(-s) * f (Real.log m / L))) := by
    have h := hmainlim.sub hRlim
    simpa using h

  have hfin : Tendsto (fun ε : ℝ => ∫ τ : ℝ, (Real.exp (-(ε*|τ|)) : ℂ) * F τ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((2*(Real.pi:ℂ)/(L:ℂ)) * (m:ℂ)^(-s) * f (Real.log m / L))) :=
    hconv2.congr' (by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (hsplit ε hε).symm)

  exact tendsto_nhds_unique hdconv hfin

end Commons.Analysis.Complex