import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Submission.Commons.Analysis.Fourier.dirichlet_integral

namespace Commons.Analysis.Complex

open MeasureTheory intervalIntegral Filter
open scoped Topology

noncomputable section

/-! ## The vertical integral of the exponential kernel -/

/-- The vertical integral of `exp(-(I*s*γ))` over `γ ∈ [-R, R]` equals `2*R*sinc(R*s)`. -/
lemma integral_exp_neg_I_mul (R s : ℝ) :
    (∫ γ in (-R)..R, Complex.exp (-(Complex.I * (s : ℂ) * (γ : ℂ))))
      = ((2 * R * Real.sinc (R * s) : ℝ) : ℂ) := by
  rcases eq_or_ne R 0 with hR | hR
  · subst hR; simp
  rcases eq_or_ne s 0 with hs | hs
  · subst hs; simp [Real.sinc_zero]; ring
  have hc : (-(Complex.I * (s : ℂ))) ≠ 0 := by
    simp [hs]
  have hcongr : (∫ γ in (-R)..R, Complex.exp (-(Complex.I * (s : ℂ) * (γ : ℂ))))
      = ∫ γ in (-R)..R, Complex.exp ((-(Complex.I * (s : ℂ))) * (γ : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro γ _

    ring
  rw [hcongr, integral_exp_mul_complex (a := -R) (b := R) (c := -(Complex.I * (s : ℂ))) hc]
  rw [div_eq_iff hc]
  have hcR : (-(Complex.I * (s : ℂ))) * (R : ℂ) = -(↑(R*s) : ℂ) * Complex.I := by push_cast; ring
  have hcR' : (-(Complex.I * (s : ℂ))) * ((-R : ℝ) : ℂ) = (↑(R*s) : ℂ) * Complex.I := by push_cast; ring
  rw [hcR, hcR']
  rw [Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  rw [← Complex.ofReal_cos (R*s), ← Complex.ofReal_sin (R*s)]
  rw [Real.sinc_of_ne_zero (mul_ne_zero hR hs)]
  have hRc : (R:ℂ) ≠ 0 := by exact_mod_cast hR
  have hsc : (s:ℂ) ≠ 0 := by exact_mod_cast hs
  push_cast
  field_simp
  ring

/-- The inner `γ`-integral of the Laplace kernel vs the parameter `s`. -/
lemma integral_exp_neg_rho_add_I_mul (ρ R s : ℝ) :
    (∫ γ in (-R)..R, Complex.exp (-(((ρ : ℂ) + (γ : ℂ) * Complex.I) * (s : ℂ))))
      = Complex.exp (-(ρ * s)) * ((2 * R * Real.sinc (R * s) : ℝ) : ℂ) := by
  have hfac : ∀ γ : ℝ, Complex.exp (-(((ρ : ℂ) + (γ : ℂ) * Complex.I) * (s : ℂ)))
      = Complex.exp (-(↑(ρ * s) : ℂ)) * Complex.exp (-(Complex.I * (s : ℂ) * (γ : ℂ))) := by
    intro γ
    rw [← Complex.exp_add]

    push_cast
    ring
  simp_rw [hfac]
  rw [intervalIntegral.integral_const_mul, integral_exp_neg_I_mul, Complex.ofReal_mul]

/-- The inner `γ`-integral of the theorem's integrand. -/
lemma inner_integral (ρ R : ℝ) (f : ℝ → ℂ) (s : ℝ) :
    (∫ γ in (-R)..R, Complex.exp (-(((ρ : ℂ) + (γ : ℂ) * Complex.I) * (s : ℂ))) * f s)
      = f s * (Complex.exp (-(ρ * s)) * ((2 * R * Real.sinc (R * s) : ℝ) : ℂ)) := by
  rw [intervalIntegral.integral_mul_const, integral_exp_neg_rho_add_I_mul, mul_comm]

/-! ## The sine integral `Si` -/

/-- The sine integral. -/
def Si (T : ℝ) : ℝ := ∫ x in (0:ℝ)..T, Real.sinc x

lemma Si_zero : Si 0 = 0 := by simp [Si]

lemma hasDerivAt_Si (x : ℝ) : HasDerivAt Si (Real.sinc x) x :=
  integral_hasDerivAt_right (Real.continuous_sinc.intervalIntegrable 0 x)
    (Real.continuous_sinc.stronglyMeasurableAtFilter volume (𝓝 x))
    Real.continuous_sinc.continuousAt

lemma continuous_Si : Continuous Si :=
  continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_Si x).continuousAt)

lemma Si_eq_sin_div (T : ℝ) : Si T = ∫ x in (0:ℝ)..T, Real.sin x / x := by
  have hfull : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by
    rw [MeasureTheory.ae_iff]; simp
  rw [Si]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hfull] with x hx _
  exact Real.sinc_of_ne_zero hx

lemma Si_tendsto : Tendsto Si atTop (𝓝 (Real.pi / 2)) := by
  have h : Si =ᶠ[atTop] (fun T : ℝ => ∫ x in (0:ℝ)..T, Real.sin x / x) :=
    Eventually.of_forall Si_eq_sin_div
  exact Tendsto.congr' h.symm Commons.Analysis.Fourier.dirichlet_integral

lemma Si_bounded : ∃ M : ℝ, 0 ≤ M ∧ ∀ T : ℝ, 0 ≤ T → |Si T| ≤ M := by
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (Metric.tendsto_nhds.mp Si_tendsto 1 one_pos)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := max T₀ 0)).exists_bound_of_continuousOn
    continuous_Si.continuousOn
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 ⟨le_refl 0, le_max_right _ _⟩)
  refine ⟨max C (Real.pi / 2 + 1), le_trans hC0 (le_max_left _ _), ?_⟩
  intro T hT
  simp only [Real.norm_eq_abs] at hC
  have hpi2 : |Real.pi / 2| = Real.pi / 2 := abs_of_pos (by linarith [Real.pi_pos])
  by_cases hle : T ≤ max T₀ 0
  · exact le_trans (hC T ⟨hT, hle⟩) (le_max_left _ _)
  · have hgt : max T₀ 0 < T := lt_of_not_ge hle
    have hTT : T₀ ≤ T := le_trans (le_max_left _ _) hgt.le
    have hd : |Si T - Real.pi / 2| < 1 := by
      have := hT₀ T hTT
      rwa [Real.dist_eq] at this
    calc |Si T| ≤ |Si T - Real.pi / 2| + |Real.pi / 2| := by
          have := abs_add_le (Si T - Real.pi / 2) (Real.pi / 2)
          rwa [sub_add_cancel] at this
      _ ≤ 1 + Real.pi / 2 := by rw [hpi2]; linarith
      _ ≤ max C (Real.pi / 2 + 1) := by
          have hh : (1:ℝ) + Real.pi / 2 = Real.pi / 2 + 1 := by ring
          rw [hh]; exact le_max_right _ _

/-! ## A boundedness-to-integrability helper -/

lemma intervalIntegrable_of_bound {F : ℝ → ℂ} {x₀ C : ℝ} (hx₀ : 0 < x₀)
    (hF : AEStronglyMeasurable F (volume.restrict (Set.Ioo (0:ℝ) x₀)))
    (hb : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖F t‖ ≤ C) :
    IntervalIntegrable F volume (0:ℝ) x₀ := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hx₀.le]
  refine IntegrableOn.of_bound ?_ hF C ?_
  · rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hb t ht

/-! ## Bounding the derivative -/

/-- A `C²` function with bounded second derivative on `(0, x₀)` has bounded derivative. -/
lemma exists_norm_deriv_le {f : ℝ → ℂ} {x₀ B : ℝ} (hx₀ : 0 < x₀)
    (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hbound : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B) :
    ∃ M : ℝ, ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖deriv f t‖ ≤ M := by
  refine ⟨‖deriv f (x₀/2)‖ + B * x₀, ?_⟩
  intro t ht
  have hthalf : x₀/2 ∈ Set.Ioo (0:ℝ) x₀ := ⟨by linarith, by linarith⟩
  have hcont' : ∀ s ∈ Set.Ioo (0:ℝ) x₀, HasDerivWithinAt (deriv f) (iteratedDeriv 2 f s)
      (Set.Ioo 0 x₀) s := by
    intro s hs
    have hdiff : DifferentiableOn ℝ (deriv f) (Set.Ioo (0:ℝ) x₀) := by
      have h := hf2.differentiableOn_iteratedDerivWithin (m := 1) (by norm_num)
        (uniqueDiffOn_Ioo 0 x₀)
      refine h.congr ?_
      intro y hy
      rw [iteratedDerivWithin_one, derivWithin_of_isOpen isOpen_Ioo hy]
    have hd := hdiff.hasDerivAt (Ioo_mem_nhds hs.1 hs.2)
    have heq : deriv (deriv f) s = iteratedDeriv 2 f s := by
      rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_one]
    rw [← heq]
    exact hd.hasDerivWithinAt
  have hlip := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hcont' hbound
    (convex_Ioo 0 x₀) ht hthalf
  have hlip' : ‖deriv f t - deriv f (x₀/2)‖ ≤ B * ‖t - x₀/2‖ := by
    simpa only [norm_sub_rev] using hlip
  have hdist : ‖t - x₀/2‖ ≤ x₀ := by
    rw [Real.norm_eq_abs, abs_le]; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hbound (x₀/2) hthalf)
  calc ‖deriv f t‖ ≤ ‖deriv f t - deriv f (x₀/2)‖ + ‖deriv f (x₀/2)‖ := by
        have := norm_add_le (deriv f t - deriv f (x₀/2)) (deriv f (x₀/2))
        rwa [sub_add_cancel] at this
    _ ≤ B * x₀ + ‖deriv f (x₀/2)‖ := by
        exact add_le_add (le_trans hlip' (mul_le_mul_of_nonneg_left hdist hB0)) le_rfl
    _ = ‖deriv f (x₀/2)‖ + B * x₀ := by ring

/-! ## The endpoint approximate identity -/

/-- The endpoint approximate identity: `2*R ∫_0^{x₀} g(s) sinc(R*s) ds → π * g(0)`. -/
theorem tendsto_two_mul_sinc_integral {g : ℝ → ℂ} {x₀ M : ℝ} (hx₀ : 0 < x₀)
    (hgc : ContinuousOn g (Set.Icc 0 x₀))
    (hgd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, HasDerivAt g (deriv g t) t)
    (hgb : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖deriv g t‖ ≤ M)
    (hgx : g x₀ = 0) :
    Tendsto (fun R : ℝ => 2 * R * ∫ s in (0:ℝ)..x₀, g s * (Real.sinc (R * s) : ℂ))
      atTop (𝓝 (Real.pi * g 0)) := by
  obtain ⟨MS, hMSnn, hMS⟩ := Si_bounded
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hgb (x₀/2) ⟨by linarith, by linarith⟩)
  have htend_g0 : Tendsto g (𝓝[>] (0:ℝ)) (𝓝 (g 0)) := by
    have h := hgc.continuousWithinAt ⟨le_refl 0, hx₀.le⟩
    refine h.mono_left ?_
    rw [nhdsWithin_Icc_eq_nhdsGE hx₀]
    exact nhdsWithin_mono _ Set.Ioi_subset_Ici_self
  have htend_gx : Tendsto g (𝓝[<] x₀) (𝓝 (g x₀)) := by
    have h := hgc.continuousWithinAt ⟨hx₀.le, le_refl x₀⟩
    refine h.mono_left ?_
    rw [nhdsWithin_Icc_eq_nhdsLE hx₀]
    exact nhdsWithin_mono _ Set.Iio_subset_Iic_self
  have hderivg_int : IntervalIntegrable (deriv g) volume (0:ℝ) x₀ :=
    intervalIntegrable_of_bound (C := M) hx₀ (measurable_deriv g).aestronglyMeasurable hgb
  have hFTCg : (∫ s in (0:ℝ)..x₀, deriv g s) = g x₀ - g 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hx₀ hgd hderivg_int htend_g0 htend_gx
  -- Dominated convergence
  have hxne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ x₀ := by
    rw [MeasureTheory.ae_iff]; simp
  have hDCT : Tendsto (fun R : ℝ => ∫ s in (0:ℝ)..x₀, deriv g s * ((Si (R * s) : ℝ) : ℂ))
      atTop (𝓝 (∫ s in (0:ℝ)..x₀, deriv g s * ((Real.pi / 2 : ℝ) : ℂ))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (μ := volume)
      (a := (0:ℝ)) (b := x₀) (l := atTop)
      (F := fun R s => deriv g s * ((Si (R * s) : ℝ) : ℂ))
      (f := fun s => deriv g s * ((Real.pi / 2 : ℝ) : ℂ)) (fun _ => M * MS) ?_ ?_ ?_ ?_
    · refine Filter.Eventually.of_forall (fun R => ?_)
      exact ((measurable_deriv g).mul (Complex.continuous_ofReal.measurable.comp
        (continuous_Si.comp (continuous_const.mul continuous_id)).measurable)).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop (0:ℝ)] with R hR
      filter_upwards [hxne] with s hne hs
      rw [Set.uIoc_of_le hx₀.le] at hs
      have hsI : s ∈ Set.Ioo (0:ℝ) x₀ := ⟨hs.1, lt_of_le_of_ne hs.2 hne⟩
      calc ‖deriv g s * ((Si (R * s) : ℝ) : ℂ)‖
          = ‖deriv g s‖ * |Si (R * s)| := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ M * MS := mul_le_mul (hgb s hsI) (hMS (R * s) (mul_nonneg hR hs.1.le)) (abs_nonneg _) hM0
    · exact intervalIntegrable_const
    · refine Filter.Eventually.of_forall (fun s hs => ?_)
      rw [Set.uIoc_of_le hx₀.le] at hs
      have hs0 : 0 < s := hs.1
      have hRR : Tendsto (fun R : ℝ => R * s) atTop atTop :=
        Filter.Tendsto.atTop_mul_const hs0 tendsto_id
      have hSi : Tendsto (fun R : ℝ => Si (R * s)) atTop (𝓝 (Real.pi / 2)) := Si_tendsto.comp hRR
      have hSi' : Tendsto (fun R : ℝ => ((Si (R * s) : ℝ) : ℂ)) atTop
          (𝓝 (((Real.pi / 2 : ℝ)) : ℂ)) :=
        Complex.continuous_ofReal.continuousAt.tendsto.comp hSi
      exact hSi'.const_mul (deriv g s)
  have hval : (∫ s in (0:ℝ)..x₀, deriv g s * ((Real.pi / 2 : ℝ) : ℂ))
      = ((Real.pi / 2 : ℝ) : ℂ) * (g x₀ - g 0) := by
    rw [intervalIntegral.integral_mul_const, hFTCg]
    ring
  rw [hval] at hDCT
  have hfin : Tendsto (fun R : ℝ => -2 * ∫ s in (0:ℝ)..x₀, deriv g s * ((Si (R * s) : ℝ) : ℂ))
      atTop (𝓝 (Real.pi * g 0)) := by
    have h := hDCT.const_mul (-2)
    rw [hgx] at h
    have hsimp : (-2 : ℂ) * (((Real.pi / 2 : ℝ) : ℂ) * (0 - g 0)) = Real.pi * g 0 := by
      push_cast; ring
    rwa [hsimp] at h
  have hEq : ∀ R : ℝ, 0 ≤ R → 2 * R * (∫ s in (0:ℝ)..x₀, g s * (Real.sinc (R * s) : ℂ))
      = -2 * ∫ s in (0:ℝ)..x₀, deriv g s * ((Si (R * s) : ℝ) : ℂ) := by
    intro R hR0
    obtain ⟨Cg, hCg⟩ := (isCompact_Icc (a := (0:ℝ)) (b := x₀)).exists_bound_of_continuousOn hgc
    have hCg0 : 0 ≤ Cg := le_trans (norm_nonneg _) (hCg 0 ⟨le_refl 0, hx₀.le⟩)
    have hGderiv : ∀ s ∈ Set.Ioo (0:ℝ) x₀,
        HasDerivAt (fun u : ℝ => g u * ((Si (R * u) : ℝ) : ℂ))
          (deriv g s * ((Si (R * s) : ℝ) : ℂ) + g s * ((R * Real.sinc (R * s) : ℝ) : ℂ)) s := by
      intro s hs
      have h1 : HasDerivAt g (deriv g s) s := hgd s hs
      have hlin : HasDerivAt (fun u : ℝ => R * u) R s := by
        simpa using (hasDerivAt_id s).const_mul R
      have h2 : HasDerivAt (fun u : ℝ => Si (R * u)) (Real.sinc (R * s) * R) s := by
        have hcomp := (hasDerivAt_Si (R * s)).comp s hlin
        simpa [Function.comp_def, mul_comm] using hcomp
      have h3 : HasDerivAt (fun u : ℝ => ((Si (R * u) : ℝ) : ℂ))
          (((Real.sinc (R * s) * R : ℝ)) : ℂ) s := h2.ofReal_comp
      have h4 := h1.mul h3
      have key : ((Real.sinc (R * s) * R : ℝ) : ℂ) = ((R * Real.sinc (R * s) : ℝ) : ℂ) := by
        push_cast; ring
      rwa [key] at h4
    have hcontG : ContinuousOn (fun u : ℝ => g u * ((Si (R * u) : ℝ) : ℂ)) (Set.Icc 0 x₀) :=
      hgc.mul (Complex.continuous_ofReal.comp
        (continuous_Si.comp (continuous_const.mul continuous_id))).continuousOn
    have hA : IntervalIntegrable (fun s : ℝ => deriv g s * ((Si (R * s) : ℝ) : ℂ))
        volume (0:ℝ) x₀ := by
      refine intervalIntegrable_of_bound (C := M * MS) hx₀ ?_ ?_
      · exact ((measurable_deriv g).mul (Complex.continuous_ofReal.measurable.comp
          (continuous_Si.comp (continuous_const.mul continuous_id)).measurable)).aestronglyMeasurable
      · intro s hs
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul (hgb s hs) (hMS (R * s) (mul_nonneg hR0 hs.1.le)) (abs_nonneg _) hM0
    have hB : IntervalIntegrable (fun s : ℝ => g s * ((R * Real.sinc (R * s) : ℝ) : ℂ))
        volume (0:ℝ) x₀ := by
      refine intervalIntegrable_of_bound (C := Cg * |R|) hx₀ ?_ ?_
      · exact ((hgc.mono (fun x hx => ⟨hx.1.le, hx.2.le⟩)).aestronglyMeasurable measurableSet_Ioo).mul
          ((Complex.continuous_ofReal.measurable.comp
            ((continuous_const.mul Real.continuous_sinc).comp
              (continuous_const.mul continuous_id)).measurable)).aestronglyMeasurable
      · intro s hs
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        calc ‖g s‖ * |R * Real.sinc (R * s)| ≤ Cg * (|R| * 1) := by
              refine mul_le_mul (hCg s ⟨hs.1.le, hs.2.le⟩) ?_ (abs_nonneg _) hCg0
              rw [abs_mul]
              exact mul_le_mul_of_nonneg_left (Real.abs_sinc_le_one _) (abs_nonneg _)
            _ = Cg * |R| := by ring
    have hInt := hA.add hB
    have ht0 : Tendsto (fun u : ℝ => g u * ((Si (R * u) : ℝ) : ℂ)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have h2 : 𝓝[>] (0:ℝ) ≤ 𝓝[Set.Icc (0:ℝ) x₀] 0 := by
        rw [nhdsWithin_Icc_eq_nhdsGE hx₀]
        exact nhdsWithin_mono _ Set.Ioi_subset_Ici_self
      have h := (hcontG.continuousWithinAt ⟨le_refl 0, hx₀.le⟩).mono_left h2
      simpa [Si_zero] using h
    have htx : Tendsto (fun u : ℝ => g u * ((Si (R * u) : ℝ) : ℂ)) (𝓝[<] x₀) (𝓝 0) := by
      have h2 : 𝓝[<] x₀ ≤ 𝓝[Set.Icc (0:ℝ) x₀] x₀ := by
        rw [nhdsWithin_Icc_eq_nhdsLE hx₀]
        exact nhdsWithin_mono _ Set.Iio_subset_Iic_self
      have h := (hcontG.continuousWithinAt ⟨hx₀.le, le_refl x₀⟩).mono_left h2
      simpa [hgx] using h
    have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hx₀ hGderiv hInt ht0 htx
    rw [sub_self, intervalIntegral.integral_add hA hB] at hmain
    have hBrewrite : (∫ s in (0:ℝ)..x₀, g s * ((R * Real.sinc (R * s) : ℝ) : ℂ))
        = (R : ℂ) * ∫ s in (0:ℝ)..x₀, g s * (Real.sinc (R * s) : ℂ) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro s _
      push_cast; ring
    rw [hBrewrite] at hmain
    push_cast
    linear_combination 2 * hmain
  exact hfin.congr' (by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with R hR
    exact (hEq R hR).symm)

/-! ## The main endpoint theorem -/

theorem laplace_vertical_endpoint_tendsto {f : ℝ → ℂ} {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hcont : ContinuousOn f (Set.Icc 0 x₀))
    (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hbound : ∃ B : ℝ, ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hvanish : ∀ t : ℝ, x₀ ≤ t → f t = 0) {ρ : ℝ} (hρ : 0 < ρ) :
    Filter.Tendsto
      (fun R : ℝ => ∫ γ in (-R)..R, ∫ s in (0:ℝ)..x₀,
        Complex.exp (-(((ρ : ℂ) + γ * Complex.I) * (s : ℂ))) * f s)
      Filter.atTop (nhds (Real.pi * f 0)) := by
  obtain ⟨B, hB⟩ := hbound
  obtain ⟨Mf, hMf⟩ := exists_norm_deriv_le hx₀ hf2 hB
  set g : ℝ → ℂ := fun s => f s * Complex.exp (-(ρ * s)) with hgdef
  have hg0 : g 0 = f 0 := by simp [hgdef]
  have hgx : g x₀ = 0 := by
    rw [hgdef]; simp [hvanish x₀ le_rfl]
  have hexpcont : Continuous (fun s : ℝ => Complex.exp (-(ρ * s))) := by fun_prop
  have hgcont : ContinuousOn g (Set.Icc 0 x₀) := by
    rw [hgdef]; exact hcont.mul hexpcont.continuousOn
  have hgderiv : ∀ t ∈ Set.Ioo (0:ℝ) x₀, HasDerivAt g (deriv g t) t := by
    intro t ht
    rw [hgdef]
    have hft : DifferentiableAt ℝ f t :=
      (hf2.differentiableOn (by norm_num)).differentiableAt (Ioo_mem_nhds ht.1 ht.2)
    have hgt : DifferentiableAt ℝ (fun s : ℝ => Complex.exp (-(ρ * s))) t := by fun_prop
    exact (hft.mul hgt).hasDerivAt
  have hgbound : ∃ M : ℝ, ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖deriv g t‖ ≤ M := by
    obtain ⟨Mf0, hMf0⟩ := (isCompact_Icc (a := (0:ℝ)) (b := x₀)).exists_bound_of_continuousOn hcont
    refine ⟨Mf + Mf0 * ρ, ?_⟩
    intro t ht
    have hft : DifferentiableAt ℝ f t :=
      (hf2.differentiableOn (by norm_num)).differentiableAt (Ioo_mem_nhds ht.1 ht.2)
    have hu : HasDerivAt (fun s : ℝ => (-(ρ : ℂ)) * (s : ℂ)) (-(ρ : ℂ)) t := by
      have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
      simpa using h1.const_mul (-(ρ : ℂ))
    have hcomp : HasDerivAt (fun s : ℝ => Complex.exp (-(ρ * s)))
        (Complex.exp (-(ρ * t)) * (-(ρ : ℂ))) t := by
      have h2 := (Complex.hasDerivAt_exp ((-(ρ : ℂ)) * (t : ℂ))).comp t hu
      rw [show (Complex.exp ∘ fun s : ℝ => (-(ρ : ℂ)) * (s : ℂ))
            = fun s : ℝ => Complex.exp (-(ρ * s)) from by
            funext s; simp only [Function.comp_apply]; congr 1; push_cast; ring] at h2
      have hv : Complex.exp ((-(ρ : ℂ)) * (t : ℂ)) * (-(ρ : ℂ))
          = Complex.exp (-(ρ * t)) * (-(ρ : ℂ)) := by
        rw [show ((-(ρ : ℂ)) * (t : ℂ)) = -(↑ρ * ↑t) by ring]
      rwa [hv] at h2
    have hgt : DifferentiableAt ℝ (fun s : ℝ => Complex.exp (-(ρ * s))) t := hcomp.differentiableAt
    have hgd2 : HasDerivAt g
        (deriv f t * Complex.exp (-(ρ * t)) + f t * (Complex.exp (-(ρ * t)) * (-(ρ : ℂ)))) t := by
      rw [hgdef]
      exact hft.hasDerivAt.mul hcomp
    have hnorm_exp : ‖Complex.exp (-(ρ * t))‖ ≤ 1 := by
      rw [Complex.norm_exp]
      have hre : (-(ρ * t) : ℂ).re = -(ρ * t) := by simp
      rw [hre, Real.exp_le_one_iff]; nlinarith [ht.1]
    have hMf0' : 0 ≤ Mf := le_trans (norm_nonneg _) (hMf (x₀/2) ⟨by linarith, by linarith⟩)
    have hMf0'' : 0 ≤ Mf0 := le_trans (norm_nonneg _) (hMf0 0 ⟨le_refl 0, hx₀.le⟩)
    have hnorm_rho : ‖(ρ : ℂ)‖ = ρ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
    rw [hgd2.deriv]
    calc ‖deriv f t * Complex.exp (-(ρ * t)) + f t * (Complex.exp (-(ρ * t)) * (-(ρ : ℂ)))‖
        ≤ ‖deriv f t * Complex.exp (-(ρ * t))‖
            + ‖f t * (Complex.exp (-(ρ * t)) * (-(ρ : ℂ)))‖ := norm_add_le _ _
      _ = ‖deriv f t‖ * ‖Complex.exp (-(ρ * t))‖
            + ‖f t‖ * (‖Complex.exp (-(ρ * t))‖ * ‖(ρ : ℂ)‖) := by
          rw [norm_mul, norm_mul, norm_mul, norm_neg]
      _ ≤ Mf * 1 + Mf0 * (1 * ρ) := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul (hMf t ht) hnorm_exp (norm_nonneg _) hMf0'
          · refine mul_le_mul (hMf0 t ⟨ht.1.le, ht.2.le⟩) ?_ (by positivity) hMf0''
            exact mul_le_mul hnorm_exp (le_of_eq hnorm_rho) (norm_nonneg _) (by norm_num)
      _ = Mf + Mf0 * ρ := by ring
  obtain ⟨M, hMg⟩ := hgbound
  have hcore := tendsto_two_mul_sinc_integral (g := g) (x₀ := x₀) (M := M)
    hx₀ hgcont hgderiv hMg hgx
  rw [hg0] at hcore
  -- Fubini
  have hFubini : ∀ R : ℝ, (∫ γ in (-R)..R, ∫ s in (0:ℝ)..x₀,
        Complex.exp (-(((ρ : ℂ) + γ * Complex.I) * (s : ℂ))) * f s)
      = ∫ s in (0:ℝ)..x₀, ∫ γ in (-R)..R,
        Complex.exp (-(((ρ : ℂ) + γ * Complex.I) * (s : ℂ))) * f s := by
    intro R
    refine MeasureTheory.intervalIntegral_intervalIntegral_swap ?_
    have hcontbox : ContinuousOn (fun p : ℝ × ℝ =>
        Complex.exp (-(((ρ : ℂ) + (p.1 : ℂ) * Complex.I) * (p.2 : ℂ))) * f p.2)
        (Set.uIcc (-R) R ×ˢ Set.uIcc (0:ℝ) x₀) := by
      have hexp : Continuous (fun p : ℝ × ℝ =>
          Complex.exp (-(((ρ : ℂ) + (p.1 : ℂ) * Complex.I) * (p.2 : ℂ)))) := by fun_prop
      have hf' : ContinuousOn (fun p : ℝ × ℝ => f p.2)
          (Set.uIcc (-R) R ×ˢ Set.uIcc (0:ℝ) x₀) := by
        refine hcont.comp continuous_snd.continuousOn ?_
        intro p hp
        rw [Set.uIcc_of_le hx₀.le] at hp
        exact hp.2
      exact hexp.continuousOn.mul hf'
    have hInt : IntegrableOn (fun p : ℝ × ℝ =>
        Complex.exp (-(((ρ : ℂ) + (p.1 : ℂ) * Complex.I) * (p.2 : ℂ))) * f p.2)
        (Set.uIcc (-R) R ×ˢ Set.uIcc (0:ℝ) x₀) volume :=
      hcontbox.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)
    exact hInt.mono_set (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)
  have hkey : ∀ R : ℝ, (∫ γ in (-R)..R, ∫ s in (0:ℝ)..x₀,
        Complex.exp (-(((ρ : ℂ) + γ * Complex.I) * (s : ℂ))) * f s)
      = 2 * R * ∫ s in (0:ℝ)..x₀, g s * (Real.sinc (R * s) : ℂ) := by
    intro R
    rw [hFubini R]
    have h1 : (∫ s in (0:ℝ)..x₀, ∫ γ in (-R)..R,
          Complex.exp (-(((ρ : ℂ) + γ * Complex.I) * (s : ℂ))) * f s)
        = ∫ s in (0:ℝ)..x₀, f s * (Complex.exp (-(ρ * s)) * ((2 * R * Real.sinc (R * s) : ℝ) : ℂ)) := by
      apply intervalIntegral.integral_congr
      intro s _
      exact inner_integral ρ R f s
    rw [h1]
    have h2 : (∫ s in (0:ℝ)..x₀, f s * (Complex.exp (-(ρ * s)) * ((2 * R * Real.sinc (R * s) : ℝ) : ℂ)))
        = ((2 * R : ℝ) : ℂ) * ∫ s in (0:ℝ)..x₀, g s * (Real.sinc (R * s) : ℂ) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro s _
      rw [hgdef]
      push_cast
      ring
    rw [h2]
    push_cast
    ring
  exact hcore.congr' (Filter.Eventually.of_forall (fun R => (hkey R).symm))

end

end Commons.Analysis.Complex