import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.cutoff
import Submission.Work.BourgainPlan.IonescuWainger.lintegral_le_of_tendsto_le
import Submission.Work.BourgainPlan.IonescuWainger.sum_intervalIntegral_eq_fourierInv
import Submission.Work.BourgainPlan.IonescuWainger.tendsto_fourierInv_plateau
import Submission.Work.Analysis.Fourier.bandlimited_weighted_reproduction
import Submission.Commons.Analysis.Fourier.band_limited_reproducing_kernel

namespace Work.BourgainPlan.IonescuWainger

open MeasureTheory
open scoped ENNReal FourierTransform BigOperators Interval

noncomputable section

/-- **The fixed reproducing kernel of the Nyquist band.**  There is an integrable kernel `w`
decaying like `(1+z²)⁻¹` whose Fourier transform is identically `1` on `[-1/2,1/2]`.  It is the
inverse Fourier transform of a Schwartz bump equal to `1` on the band. -/
lemma exists_band_decay_kernel :
    ∃ (w : ℝ → ℂ) (B : ℝ), Integrable w ∧ 0 < B ∧ (∀ z : ℝ, ‖w z‖ ≤ B / (1 + z ^ 2)) ∧
      (∀ ξ : ℝ, ξ ∈ Set.Icc (-(1/2):ℝ) (1/2) → FourierTransform.fourier w ξ = 1) := by
  obtain ⟨χ, hχ⟩ := Commons.Analysis.Fourier.exists_schwartzMap_eq_one_Icc (1/2) (by norm_num)
  obtain ⟨B, hBpos, hBdec⟩ :=
    Commons.Analysis.Fourier.schwartzMap_decay_one_add_sq (FourierTransformInv.fourierInv χ)
  refine ⟨⇑(FourierTransformInv.fourierInv χ), B,
    SchwartzMap.integrable (μ := volume) (FourierTransformInv.fourierInv χ), hBpos, hBdec, ?_⟩
  have hfourier : FourierTransform.fourier (⇑(FourierTransformInv.fourierInv χ)) = ⇑χ := by
    rw [← SchwartzMap.fourier_coe (FourierTransformInv.fourierInv χ)]
    exact congrArg DFunLike.coe (FourierTransform.fourier_fourierInv_eq χ)
  intro ξ hξ
  rw [hfourier]
  exact hχ ξ hξ

theorem msw_of_cutoff_extension (p : ℝ) (hp : 1 < p)
    (hβ : ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ), 0 < ε → ε ≤ 1/2 → ∀ (s : Finset ℤ) (a : ℤ → ℂ),
      (∀ k, k ∉ s → a k = 0) →
      ∫⁻ x : ℝ, ‖FourierTransformInv.fourierInv
          (fun ξ : ℝ => (∑ k ∈ s, a k * Complex.exp (-(2 * Real.pi * Complex.I * (k : ℂ) * (ξ : ℂ))))
            * ((plateau ε ξ : ℝ) : ℂ)) x‖ₑ ^ p
        ≤ ENNReal.ofReal (C ^ p) * ∑ k ∈ s, ENNReal.ofReal ‖a k‖ ^ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℝ → ℂ) (hmi : Integrable m)
      (hmsupp : ∀ ξ : ℝ, ξ ∉ Set.Icc (-(1/2):ℝ) (1/2) → m ξ = 0)
      (A : ℝ) (hA : 0 ≤ A)
      (hOp : ∀ g : ℝ → ℂ, Integrable g →
        (∀ ξ : ℝ, ξ ∉ Set.Icc (-(1/2):ℝ) (1/2) → FourierTransform.fourier g ξ = 0) →
        ∫⁻ x : ℝ, ‖FourierTransformInv.fourierInv (fun ξ => m ξ * FourierTransform.fourier g ξ) x‖ₑ ^ p ∂volume
          ≤ ENNReal.ofReal (A ^ p) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ p ∂volume)
      (s : Finset ℤ) (a : ℤ → ℂ) (ha : ∀ n, n ∉ s → a n = 0),
      ∫⁻ n : ℤ, ‖∑ k ∈ s, (∫ ξ in (-(1/2):ℝ)..(1/2),
          m ξ * Complex.exp (2 * Real.pi * Complex.I * ((n - k : ℤ) : ℂ) * (ξ : ℂ))) * a k‖ₑ ^ p
        ∂Measure.count
        ≤ ENNReal.ofReal ((C * A) ^ p) * ∫⁻ n : ℤ, ‖a n‖ₑ ^ p ∂Measure.count := by
  obtain ⟨Cβ, hCβpos, hCβ⟩ := hβ
  obtain ⟨w, B, hw_int, hBpos, hw_dec, hw_four⟩ := exists_band_decay_kernel
  obtain ⟨C₁, hC₁pos, hC₁⟩ :=
    Commons.Analysis.Fourier.lattice_sup_le_integral_sup_band_limited_fourierInv_rpow (p := p) hp
  refine ⟨(C₁ * B ^ p) ^ (1 / p) * Cβ, ?_, ?_⟩
  · exact mul_pos (Real.rpow_pos_of_pos (mul_pos hC₁pos (Real.rpow_pos_of_pos hBpos p)) _) hCβpos
  intro m hmi hmsupp A hA hOp s a ha
  classical
  set trig : ℝ → ℂ :=
    fun ξ => ∑ k ∈ s, a k * Complex.exp (-(2 * Real.pi * Complex.I * (k : ℂ) * (ξ : ℂ))) with htrig
  set F : ℝ → ℂ := FourierTransformInv.fourierInv (fun ξ => m ξ * trig ξ) with hF
  set c : ℝ := ∑ k ∈ s, ‖a k‖ with hc
  set Sp : ENNReal := ∑ k ∈ s, ENNReal.ofReal ‖a k‖ ^ p with hSp
  -- basic facts on `trig`
  have htrig_diff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) trig := by
    rw [htrig]
    refine ContDiff.sum (fun k hk => ?_)
    refine contDiff_const.mul ?_
    refine Complex.contDiff_exp.comp ?_
    have hlin : (fun ξ : ℝ => -(2 * Real.pi * Complex.I * (k : ℂ) * (ξ : ℂ)))
        = fun ξ : ℝ => (-(2 * Real.pi * Complex.I * (k : ℂ))) * (ξ : ℂ) := by
      funext ξ; ring
    rw [hlin]
    exact contDiff_const.mul Complex.ofRealCLM.contDiff
  have htrig_cont : Continuous trig := htrig_diff.continuous
  have htrig_meas : AEStronglyMeasurable trig volume := htrig_cont.aestronglyMeasurable
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have htrig_bound : ∀ ξ : ℝ, ‖trig ξ‖ ≤ c := by
    intro ξ
    rw [htrig, hc]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun k hk => ?_))
    have h1 : -(2 * Real.pi * Complex.I * (k : ℂ) * (ξ : ℂ))
        = ((-(2 * Real.pi * ((k : ℝ) * ξ)) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [norm_mul, h1, Complex.norm_exp_ofReal_mul_I, mul_one]
  -- the family of smooth cut-off amplitudes
  set U : ℕ → ℝ → ℂ := fun j ξ => m ξ * trig ξ * ((plateau (1/((j:ℝ)+2)) ξ : ℝ) : ℂ) with hU
  have hεpos : ∀ j : ℕ, (0:ℝ) < 1/((j:ℝ)+2) := by
    intro j; positivity
  have hεle : ∀ j : ℕ, (1:ℝ)/((j:ℝ)+2) ≤ 1/2 := by
    intro j
    rw [div_le_iff₀ (by positivity)]
    have h : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
    push_cast
    linarith
  have hU_int : ∀ j : ℕ, Integrable (U j) := by
    intro j
    have hbdd : ∀ ξ : ℝ, ‖trig ξ * ((plateau (1/((j:ℝ)+2)) ξ : ℝ) : ℂ)‖ ≤ c := by
      intro ξ
      have hpn : ‖((plateau (1/((j:ℝ)+2)) ξ : ℝ) : ℂ)‖ = plateau (1/((j:ℝ)+2)) ξ := by
        rw [← Complex.ofRealLI_apply (plateau (1/((j:ℝ)+2)) ξ), Complex.ofRealLI.norm_map,
          Real.norm_eq_abs, abs_of_nonneg (plateau_nonneg _ _)]
      rw [norm_mul, hpn]
      calc ‖trig ξ‖ * plateau (1/((j:ℝ)+2)) ξ
          ≤ c * 1 := mul_le_mul (htrig_bound ξ) (plateau_le_one _ (hεpos j) ξ)
              (plateau_nonneg _ _) hc0
        _ = c := mul_one c
    have hcont : Continuous (fun ξ : ℝ => trig ξ * ((plateau (1/((j:ℝ)+2)) ξ : ℝ) : ℂ)) :=
      htrig_cont.mul ((Complex.continuous_ofReal.comp (plateau_continuous _)))
    have hmm := hmi.bdd_mul hcont.aestronglyMeasurable (Filter.Eventually.of_forall hbdd)
    refine hmm.congr (Filter.Eventually.of_forall (fun ξ => ?_))
    rw [hU]; ring
  have hU_meas : ∀ j : ℕ, AEStronglyMeasurable (U j) volume := by
    intro j
    rw [hU]
    have h1 : AEStronglyMeasurable
        (fun ξ : ℝ => m ξ * (trig ξ * ((plateau (1/((j:ℝ)+2)) ξ : ℝ) : ℂ))) volume :=
      hmi.aestronglyMeasurable.mul
        ((htrig_cont.mul (Complex.continuous_ofReal.comp (plateau_continuous _))).aestronglyMeasurable)
    simpa only [mul_assoc] using h1
  have hU_cont_fi : ∀ j : ℕ, Continuous (FourierTransformInv.fourierInv (U j)) := by
    intro j
    have h1 : (⇑(Real.Lp.fourierTransformInv
          (MemLp.toLp (U j) (memLp_one_iff_integrable.mpr (hU_int j)))) : ℝ → ℂ)
        = FourierTransformInv.fourierInv (U j) := Real.Lp.fourierTransformInv_toLp _
    rw [← h1]
    exact (Real.Lp.fourierTransformInv _).continuous
  -- per-scale bound: the continuous operator bound composed with the smooth extension bound
  have key : ∀ j : ℕ, ∫⁻ x : ℝ, ‖FourierTransformInv.fourierInv (U j) x‖ₑ ^ p ∂volume
      ≤ ENNReal.ofReal ((A * Cβ) ^ p) * Sp := by
    intro j
    set ε : ℝ := 1/((j:ℝ)+2) with hεdef
    have hεpos' : (0:ℝ) < ε := by rw [hεdef]; exact hεpos j
    have hεle' : ε ≤ 1/2 := by rw [hεdef]; exact hεle j
    set amp : ℝ → ℂ := fun ξ => trig ξ * ((plateau ε ξ : ℝ) : ℂ) with hamp
    have hpl : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun ξ : ℝ => ((plateau ε ξ : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (plateau_contDiff ε)
    have hamp_diff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) amp := by
      rw [hamp]
      exact htrig_diff.mul hpl
    have hplateau_cs : HasCompactSupport (fun ξ : ℝ => ((plateau ε ξ : ℝ) : ℂ)) := by
      refine HasCompactSupport.of_support_subset_isCompact
        (K := Set.Icc (-(1/2):ℝ) (1/2)) isCompact_Icc ?_
      intro ξ hξ
      by_contra hmem
      have h0 : plateau ε ξ = 0 := by
        by_contra hne
        exact hmem (plateau_support ε hεpos' (Function.mem_support.mpr hne))
      exact hξ (by simp [h0])
    have hamp_cs : HasCompactSupport amp := by
      rw [hamp]
      exact HasCompactSupport.mul_left hplateau_cs
    let χ : SchwartzMap ℝ ℂ := hamp_cs.toSchwartzMap hamp_diff
    have hχ_coe : ⇑χ = amp := funext (HasCompactSupport.toSchwartzMap_toFun hamp_cs hamp_diff)
    set g : ℝ → ℂ := ⇑(FourierTransformInv.fourierInv χ) with hg
    have hg_int : Integrable g :=
      SchwartzMap.integrable (μ := volume) (FourierTransformInv.fourierInv χ)
    have hFg : ∀ ξ : ℝ, FourierTransform.fourier g ξ = amp ξ := by
      intro ξ
      have h1 : FourierTransform.fourier g = ⇑χ := by
        show FourierTransform.fourier (⇑(FourierTransformInv.fourierInv χ)) = ⇑χ
        rw [← SchwartzMap.fourier_coe (FourierTransformInv.fourierInv χ)]
        exact congrArg DFunLike.coe (FourierTransform.fourier_fourierInv_eq χ)
      rw [h1, hχ_coe]
    have hg_band : ∀ ξ : ℝ, ξ ∉ Set.Icc (-(1/2):ℝ) (1/2) → FourierTransform.fourier g ξ = 0 := by
      intro ξ hξ
      rw [hFg ξ]
      have h0 : plateau ε ξ = 0 := by
        rcases lt_or_ge ξ (-(1/2)) with h | h
        · exact plateau_eq_zero_of_le ε hεpos' (le_of_lt h)
        · exact plateau_eq_zero_of_ge ε hεpos' (le_of_not_gt (fun hlt => hξ ⟨h, le_of_lt hlt⟩))
      show trig ξ * ((plateau ε ξ : ℝ) : ℂ) = 0
      rw [h0]; simp
    have hop := hOp g hg_int hg_band
    have hg_eq : g = FourierTransformInv.fourierInv
        (fun ξ : ℝ => trig ξ * ((plateau ε ξ : ℝ) : ℂ)) := by
      show ⇑(FourierTransformInv.fourierInv χ) = _
      rw [SchwartzMap.fourierInv_coe, hχ_coe]
    have hβj : ∫⁻ x : ℝ, ‖g x‖ₑ ^ p ∂volume ≤ ENNReal.ofReal (Cβ ^ p) * Sp := by
      have h := hCβ ε hεpos' hεle' s a ha
      rw [hg_eq, hSp, htrig]
      exact h
    have hamp_eq : (fun ξ : ℝ => m ξ * FourierTransform.fourier g ξ) = U j := by
      funext ξ
      rw [hFg ξ, hU]
      show m ξ * (trig ξ * ((plateau ε ξ : ℝ) : ℂ)) = m ξ * trig ξ * ((plateau ε ξ : ℝ) : ℂ)
      ring
    have hop' : ∫⁻ x : ℝ, ‖FourierTransformInv.fourierInv (U j) x‖ₑ ^ p ∂volume
        ≤ ENNReal.ofReal (A ^ p) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ p ∂volume := by
      rw [← hamp_eq]
      exact hop
    calc ∫⁻ x : ℝ, ‖FourierTransformInv.fourierInv (U j) x‖ₑ ^ p ∂volume
        ≤ ENNReal.ofReal (A ^ p) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ p ∂volume := hop'
      _ ≤ ENNReal.ofReal (A ^ p) * (ENNReal.ofReal (Cβ ^ p) * Sp) :=
          mul_le_mul_right hβj _
      _ = ENNReal.ofReal ((A * Cβ) ^ p) * Sp := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hA p),
            Real.mul_rpow hA hCβpos.le]
  -- the limit as the cut-off opens up
  have hlim : ∀ x : ℝ, Filter.Tendsto (fun j : ℕ =>
      ‖FourierTransformInv.fourierInv (U j) x‖ₑ ^ p) Filter.atTop (nhds (‖F x‖ₑ ^ p)) := by
    intro x
    have h1 : Filter.Tendsto (fun j : ℕ => FourierTransformInv.fourierInv (U j) x)
        Filter.atTop (nhds (F x)) := by
      have h := tendsto_fourierInv_plateau m hmi hmsupp htrig_meas htrig_bound hc0 x
      simpa only [hU, hF] using h
    have h2 : Filter.Tendsto (fun j : ℕ => ENNReal.ofReal ‖FourierTransformInv.fourierInv (U j) x‖)
        Filter.atTop (nhds (ENNReal.ofReal ‖F x‖)) := ENNReal.tendsto_ofReal h1.norm
    have h2' : Filter.Tendsto (fun j : ℕ => ‖FourierTransformInv.fourierInv (U j) x‖ₑ)
        Filter.atTop (nhds ‖F x‖ₑ) := by
      simp only [ofReal_norm] at h2
      exact h2
    exact (ENNReal.continuous_rpow_const.tendsto _).comp h2'
  have hcont : ∫⁻ x : ℝ, ‖F x‖ₑ ^ p ∂volume ≤ ENNReal.ofReal ((A * Cβ) ^ p) * Sp := by
    refine lintegral_le_of_tendsto_le volume
      (f := fun j (x : ℝ) => ‖FourierTransformInv.fourierInv (U j) x‖ₑ ^ p)
      (g := fun x : ℝ => ‖F x‖ₑ ^ p)
      (K := ENNReal.ofReal ((A * Cβ) ^ p) * Sp) (fun j => ?_) hlim key
    exact ((hU_cont_fi j).aemeasurable.enorm).pow_const p
  -- the lattice sampling bound
  have hsamp : ∫⁻ n : ℤ, ‖F (n : ℝ)‖ₑ ^ p ∂Measure.count
      ≤ ENNReal.ofReal (C₁ * B ^ p) * ∫⁻ x : ℝ, ‖F x‖ₑ ^ p ∂volume := by
    have hInt : Integrable (fun ξ : ℝ => m ξ * trig ξ) := by
      have hmul : Integrable (fun ξ : ℝ => trig ξ * m ξ) :=
        hmi.bdd_mul htrig_meas (Filter.Eventually.of_forall htrig_bound)
      refine hmul.congr (Filter.Eventually.of_forall (fun ξ => ?_))
      ring
    have hkernel : ∀ (j : ℕ) (β : ℝ), (fun ξ : ℝ => m ξ * trig ξ) β ≠ 0 →
        FourierTransform.fourier w β = 1 := by
      intro j β hβ
      have h1 : m β ≠ 0 := fun h0 => hβ (by show m β * trig β = 0; rw [h0, zero_mul])
      exact hw_four β (by by_contra hcon; exact h1 (hmsupp β hcon))
    have hS := hC₁ (fun _ : ℕ => fun ξ : ℝ => m ξ * trig ξ) w B (fun _ => hInt) hw_int hBpos
      hw_dec hkernel
    simp only [iSup_const] at hS
    simpa only [hF] using hS
  -- identification of the discrete convolution with the inverse Fourier transform
  have hId : ∀ n : ℤ, (∑ k ∈ s, (∫ ξ in (-(1/2):ℝ)..(1/2),
      m ξ * Complex.exp (2 * Real.pi * Complex.I * ((n - k : ℤ) : ℂ) * (ξ : ℂ))) * a k)
      = F (n : ℝ) := by
    intro n
    have h1 : (∑ k ∈ s, (∫ ξ in (-(1/2):ℝ)..(1/2),
        m ξ * Complex.exp (2 * Real.pi * Complex.I * ((n - k : ℤ) : ℂ) * (ξ : ℂ))) * a k)
        = ∑ k ∈ s, (∫ ξ in Set.Ioc (-(1/2):ℝ) (1/2),
          m ξ * Complex.exp (2 * Real.pi * Complex.I * ((n - k : ℤ) : ℂ) * (ξ : ℂ))) * a k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [intervalIntegral.integral_of_le (by norm_num : (-(1/2):ℝ) ≤ 1/2)]
    rw [h1, hF, htrig]
    exact sum_intervalIntegral_eq_fourierInv m hmi hmsupp s a n
  -- the right-hand side
  have hRHS : ∫⁻ n : ℤ, ‖a n‖ₑ ^ p ∂Measure.count = Sp := by
    rw [hSp, lintegral_count]
    rw [tsum_eq_sum (s := s) (fun n hn => by
      rw [ha n hn]
      rw [show ‖(0 : ℂ)‖ₑ = 0 by simp, ENNReal.zero_rpow_of_pos (lt_trans zero_lt_one hp)])]
    apply Finset.sum_congr rfl
    intro k hk
    simp
  have hconst : (((C₁ * B ^ p) ^ (1 / p) * Cβ) * A) ^ p = C₁ * B ^ p * (A * Cβ) ^ p := by
    have h1 : 0 < C₁ * B ^ p := mul_pos hC₁pos (Real.rpow_pos_of_pos hBpos p)
    rw [show (C₁ * B ^ p) ^ (1 / p) * Cβ * A = ((C₁ * B ^ p) ^ (1 / p)) * (A * Cβ) by ring]
    rw [Real.mul_rpow (Real.rpow_nonneg h1.le _) (mul_nonneg hA hCβpos.le)]
    rw [← Real.rpow_mul h1.le, show (1 / p) * p = 1 by field_simp, Real.rpow_one]
  calc ∫⁻ n : ℤ, ‖∑ k ∈ s, (∫ ξ in (-(1/2):ℝ)..(1/2),
        m ξ * Complex.exp (2 * Real.pi * Complex.I * ((n - k : ℤ) : ℂ) * (ξ : ℂ))) * a k‖ₑ ^ p
        ∂Measure.count
      = ∫⁻ n : ℤ, ‖F (n : ℝ)‖ₑ ^ p ∂Measure.count := by
        apply lintegral_congr; intro n; rw [hId n]
    _ ≤ ENNReal.ofReal (C₁ * B ^ p) * ∫⁻ x : ℝ, ‖F x‖ₑ ^ p ∂volume := hsamp
    _ ≤ ENNReal.ofReal (C₁ * B ^ p) * (ENNReal.ofReal ((A * Cβ) ^ p) * Sp) :=
        mul_le_mul_right hcont _
    _ = ENNReal.ofReal ((((C₁ * B ^ p) ^ (1 / p) * Cβ) * A) ^ p) * Sp := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ C₁ * B ^ p), ← hconst]
    _ = ENNReal.ofReal ((((C₁ * B ^ p) ^ (1 / p) * Cβ) * A) ^ p)
          * ∫⁻ n : ℤ, ‖a n‖ₑ ^ p ∂Measure.count := by rw [hRHS]

end

end Work.BourgainPlan.IonescuWainger
