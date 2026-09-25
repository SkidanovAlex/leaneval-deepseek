import Mathlib
import Submission.Work.Analysis.Fourier.band_projection_schwartz_lp

namespace Work.BourgainPlan.Maximal

open MeasureTheory Filter
open scoped ENNReal FourierTransform Topology
open Commons.Analysis.CalderonZygmund
open Work.Analysis.Fourier

noncomputable section

/-- Reduction of an arbitrary interval multiplier `1_{(a,b)}` to the shifted sign multipliers:
`1_{(a,b)}(ξ) = (1/2)(sgn(ξ - a) - sgn(ξ - b))` for `ξ ≠ a, b`. -/
lemma interval_indicator_eq_half_sign_diff {a b : ℝ} (hab : a < b) :
    ∀ ξ : ℝ, ξ ≠ a → ξ ≠ b →
      (if ξ ∈ Set.Ioo a b then (1:ℂ) else 0)
        = (1/2) * (sgnC (ξ + (-a)) - sgnC (ξ + (-b))) := by
  intro ξ ha hb
  rcases lt_trichotomy ξ a with h | h | h
  · have hnot : ¬ (ξ ∈ Set.Ioo a b) := fun hx => absurd hx.1 (not_lt.mpr h.le)
    rw [if_neg hnot]
    have hp1 : sgnC (ξ + (-a)) = -1 := by
      rw [sgnC, Real.sign_of_neg (by linarith)]; norm_num
    have hp2 : sgnC (ξ + (-b)) = -1 := by
      rw [sgnC, Real.sign_of_neg (by linarith)]; norm_num
    rw [hp1, hp2]; norm_num
  · exact absurd h ha
  · rcases lt_trichotomy ξ b with h' | h' | h'
    · have hmem : ξ ∈ Set.Ioo a b := ⟨h, h'⟩
      rw [if_pos hmem]
      have hp1 : sgnC (ξ + (-a)) = 1 := by
        rw [sgnC, Real.sign_of_pos (by linarith)]; norm_num
      have hp2 : sgnC (ξ + (-b)) = -1 := by
        rw [sgnC, Real.sign_of_neg (by linarith)]; norm_num
      rw [hp1, hp2]; norm_num
    · exact absurd h' hb
    · have hnot : ¬ (ξ ∈ Set.Ioo a b) := fun hx => absurd hx.2 (not_lt.mpr h'.le)
      rw [if_neg hnot]
      have hp1 : sgnC (ξ + (-a)) = 1 := by
        rw [sgnC, Real.sign_of_pos (by linarith)]; norm_num
      have hp2 : sgnC (ξ + (-b)) = 1 := by
        rw [sgnC, Real.sign_of_pos (by linarith)]; norm_num
      rw [hp1, hp2]; norm_num

theorem interval_projection_schwartz_lp (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a b : ℝ), a < b → ∀ (G : SchwartzMap ℝ ℂ),
      MeasureTheory.lintegral (MeasureTheory.volume : MeasureTheory.Measure ℝ)
          (fun x : ℝ => ENNReal.rpow (enorm (FourierTransformInv.fourierInv
            (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then (1:ℂ) else 0)
              * FourierTransform.fourier (G : ℝ → ℂ) ξ) x)) p)
        ≤ ENNReal.ofReal (C ^ p) * MeasureTheory.lintegral (MeasureTheory.volume : MeasureTheory.Measure ℝ)
            (fun x : ℝ => ENNReal.rpow (enorm ((G : ℝ → ℂ) x)) p) := by
  obtain ⟨C, hCpos, hC⟩ := sign_shift_bound p hp
  refine ⟨C, hCpos, fun a b hab G => ?_⟩
  set ΨA : ℝ → ℂ := fun x => FourierTransformInv.fourierInv
      (fun ξ : ℝ => sgnC (ξ + (-a)) * FourierTransform.fourier (G : ℝ → ℂ) ξ) x with hΨA
  set ΨB : ℝ → ℂ := fun x => FourierTransformInv.fourierInv
      (fun ξ : ℝ => sgnC (ξ + (-b)) * FourierTransform.fourier (G : ℝ → ℂ) ξ) x with hΨB
  have hA_bound : eLpNorm ΨA (ENNReal.ofReal p) (volume : Measure ℝ)
      ≤ ENNReal.ofReal C * eLpNorm (fun x : ℝ => (G : ℝ → ℂ) x) (ENNReal.ofReal p)
          (volume : Measure ℝ) := by
    rw [hΨA]; exact hC (-a) G
  have hB_bound : eLpNorm ΨB (ENNReal.ofReal p) (volume : Measure ℝ)
      ≤ ENNReal.ofReal C * eLpNorm (fun x : ℝ => (G : ℝ → ℂ) x) (ENNReal.ofReal p)
          (volume : Measure ℝ) := by
    rw [hΨB]; exact hC (-b) G
  have hA_sm : AEStronglyMeasurable ΨA volume := by
    rw [hΨA]; exact (continuous_fourierInv_sign_shift (-a) G).aestronglyMeasurable
  have hB_sm : AEStronglyMeasurable ΨB volume := by
    rw [hΨB]; exact (continuous_fourierInv_sign_shift (-b) G).aestronglyMeasurable
  have h1r : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [ENNReal.one_le_ofReal]; linarith
  have hnorm_half : ‖(1/2 : ℂ)‖ₑ = ENNReal.ofReal (1/2) := by
    rw [enorm_eq_ofReal_norm']
    congr 1
    rw [show (1/2 : ℂ) = (1:ℂ)/2 from rfl, norm_div, norm_one, Complex.norm_ofNat]
  -- the a.e. identity of the multipliers
  have hmem_ae : ∀ᵐ ξ : ℝ, (if ξ ∈ Set.Ioo a b then (1:ℂ) else 0)
      = (1/2) * (sgnC (ξ + (-a)) - sgnC (ξ + (-b))) := by
    have hnull : volume ({ξ : ℝ | ξ = a ∨ ξ = b} : Set ℝ) = 0 := by
      have hfin : ({ξ : ℝ | ξ = a ∨ ξ = b} : Set ℝ).Finite :=
        ((Set.finite_singleton a).union (Set.finite_singleton b)).subset (by
          intro ξ hξ
          simp only [Set.mem_setOf_eq] at hξ
          simpa only [Set.mem_union, Set.mem_singleton_iff] using hξ)
      exact hfin.measure_zero volume
    have hae : ∀ᵐ ξ : ℝ, ξ ≠ a ∧ ξ ≠ b := by
      rw [MeasureTheory.ae_iff]
      refine measure_mono_null ?_ hnull
      intro ξ hξ
      simp only [Set.mem_setOf_eq] at hξ ⊢
      by_cases h1 : ξ = a
      · exact Or.inl h1
      · refine Or.inr ?_
        by_contra h2
        exact hξ ⟨h1, h2⟩
    filter_upwards [hae] with ξ hξ
    exact interval_indicator_eq_half_sign_diff hab ξ hξ.1 hξ.2
  -- the pointwise identity `Φ = (1/2)(ΨA - ΨB)`
  have hPhi_eq : ∀ x : ℝ, FourierTransformInv.fourierInv
      (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then (1:ℂ) else 0)
        * FourierTransform.fourier (G : ℝ → ℂ) ξ) x = (1/2) * (ΨA x - ΨB x) := by
    intro x
    have hI : FourierTransformInv.fourierInv
        (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then (1:ℂ) else 0)
          * FourierTransform.fourier (G : ℝ → ℂ) ξ) x
        = ∫ ξ : ℝ, ((if ξ ∈ Set.Ioo a b then (1:ℂ) else 0) * czE x ξ)
            * FourierTransform.fourier (G : ℝ → ℂ) ξ := by
      rw [fourierInv_czE]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
      simp only [smul_eq_mul]; ring
    have hP : ΨA x = ∫ ξ : ℝ, (sgnC (ξ + (-a)) * czE x ξ)
        * FourierTransform.fourier (G : ℝ → ℂ) ξ := by
      rw [hΨA]
      dsimp only
      rw [fourierInv_czE]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
      simp only [smul_eq_mul]; ring
    have hM : ΨB x = ∫ ξ : ℝ, (sgnC (ξ + (-b)) * czE x ξ)
        * FourierTransform.fourier (G : ℝ → ℂ) ξ := by
      rw [hΨB]
      dsimp only
      rw [fourierInv_czE]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
      simp only [smul_eq_mul]; ring
    rw [hI, hP, hM]
    have h1 : (∫ ξ : ℝ, ((if ξ ∈ Set.Ioo a b then (1:ℂ) else 0) * czE x ξ)
          * FourierTransform.fourier (G : ℝ → ℂ) ξ)
        = ∫ ξ : ℝ, ((1/2) * (sgnC (ξ + (-a)) - sgnC (ξ + (-b))) * czE x ξ)
          * FourierTransform.fourier (G : ℝ → ℂ) ξ := by
      refine integral_congr_ae ?_
      filter_upwards [hmem_ae] with ξ hξ
      rw [hξ]
    rw [h1]
    have h3 : (∫ ξ : ℝ, ((1/2) * (sgnC (ξ + (-a)) - sgnC (ξ + (-b))) * czE x ξ)
          * FourierTransform.fourier (G : ℝ → ℂ) ξ)
        = ∫ ξ : ℝ, ((1/2) * ((sgnC (ξ + (-a)) * czE x ξ)
              * FourierTransform.fourier (G : ℝ → ℂ) ξ)
            - (1/2) * ((sgnC (ξ + (-b)) * czE x ξ)
              * FourierTransform.fourier (G : ℝ → ℂ) ξ)) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
      ring
    rw [h3]
    have hsplit : (∫ ξ : ℝ, ((1/2) * ((sgnC (ξ + (-a)) * czE x ξ)
              * FourierTransform.fourier (G : ℝ → ℂ) ξ)
            - (1/2) * ((sgnC (ξ + (-b)) * czE x ξ)
              * FourierTransform.fourier (G : ℝ → ℂ) ξ)))
        = (∫ ξ : ℝ, (1/2) * ((sgnC (ξ + (-a)) * czE x ξ)
              * FourierTransform.fourier (G : ℝ → ℂ) ξ))
          - (∫ ξ : ℝ, (1/2) * ((sgnC (ξ + (-b)) * czE x ξ)
              * FourierTransform.fourier (G : ℝ → ℂ) ξ)) :=
      integral_sub ((integrable_sgnC_shift_mul (-a) x G).const_mul (1/2))
        ((integrable_sgnC_shift_mul (-b) x G).const_mul (1/2))
    rw [hsplit, integral_const_mul, integral_const_mul]
    ring
  -- the `L^p` bound
  have hbound : eLpNorm (fun x : ℝ => FourierTransformInv.fourierInv
        (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then (1:ℂ) else 0)
          * FourierTransform.fourier (G : ℝ → ℂ) ξ) x) (ENNReal.ofReal p)
        (volume : Measure ℝ)
      ≤ ENNReal.ofReal C * eLpNorm (fun x : ℝ => (G : ℝ → ℂ) x) (ENNReal.ofReal p)
          (volume : Measure ℝ) := by
    have hsub : (fun x : ℝ => (1/2) * (ΨA x - ΨB x))
        = (1/2 : ℂ) • (fun x : ℝ => ΨA x - ΨB x) := by
      funext x; rw [Pi.smul_apply, smul_eq_mul]
    calc eLpNorm (fun x : ℝ => FourierTransformInv.fourierInv
            (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then (1:ℂ) else 0)
              * FourierTransform.fourier (G : ℝ → ℂ) ξ) x) (ENNReal.ofReal p)
            (volume : Measure ℝ)
        = eLpNorm (fun x : ℝ => (1/2) * (ΨA x - ΨB x)) (ENNReal.ofReal p)
            (volume : Measure ℝ) :=
          eLpNorm_congr_ae (Filter.Eventually.of_forall hPhi_eq)
      _ = ‖(1/2 : ℂ)‖ₑ * eLpNorm (fun x : ℝ => ΨA x - ΨB x) (ENNReal.ofReal p)
              (volume : Measure ℝ) := by
          rw [hsub, eLpNorm_const_smul]
      _ = ENNReal.ofReal (1/2) * eLpNorm (fun x : ℝ => ΨA x - ΨB x)
              (ENNReal.ofReal p) (volume : Measure ℝ) := by
          rw [hnorm_half]
      _ ≤ ENNReal.ofReal (1/2) * (eLpNorm ΨA (ENNReal.ofReal p) (volume : Measure ℝ)
            + eLpNorm ΨB (ENNReal.ofReal p) (volume : Measure ℝ)) := by
          gcongr
          exact eLpNorm_sub_le h1r
      _ ≤ ENNReal.ofReal (1/2) * (ENNReal.ofReal C * eLpNorm (fun x : ℝ => (G : ℝ → ℂ) x)
              (ENNReal.ofReal p) (volume : Measure ℝ)
            + ENNReal.ofReal C * eLpNorm (fun x : ℝ => (G : ℝ → ℂ) x)
              (ENNReal.ofReal p) (volume : Measure ℝ)) := by
          gcongr
      _ = ENNReal.ofReal C * eLpNorm (fun x : ℝ => (G : ℝ → ℂ) x) (ENNReal.ofReal p)
            (volume : Measure ℝ) := by
          rw [mul_add, ofReal_half_mul_add_self]
  exact eLpNorm_to_lintegral_local (by linarith : (0:ℝ) < p) hCpos hbound
    G.continuous.aestronglyMeasurable

end

end Work.BourgainPlan.Maximal
