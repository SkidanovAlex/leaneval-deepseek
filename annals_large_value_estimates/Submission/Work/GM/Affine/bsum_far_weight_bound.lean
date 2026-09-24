import Mathlib
import Submission.Work.GM.Affine.FarMass_defs
import Submission.Work.GM.Affine.region_II_vocab
import Submission.Work.GM.Affine.region_II_defs
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.psi1hat_decay
import Submission.Work.GM.Affine.farTauWin_aux
import Submission.Work.GM.Affine.WinMass_basic
import Submission.Work.GM.Affine.setIntegral_ghat_sq_le
import Submission.Work.GM.Affine.far_weight_uniform_bound

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.GM.Affine

noncomputable section

/-- Affine change of variables for the `ℝ≥0∞`-valued integral. -/
lemma lintegral_comp_affine {F : ℝ → ENNReal} (hF : Measurable F) {a b : ℝ} (ha : a ≠ 0) :
    ∫⁻ u, F (a * u + b) = ENNReal.ofReal |a⁻¹| * ∫⁻ u, F u := by
  have hmap : MeasureTheory.Measure.map (fun u : ℝ => a * u + b)
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)
      = ENNReal.ofReal |a⁻¹| • MeasureTheory.volume := by
    rw [show (fun u : ℝ => a * u + b) = (fun v : ℝ => v + b) ∘ (fun u : ℝ => a * u) from rfl,
      ← MeasureTheory.Measure.map_map (by fun_prop : Measurable (fun v : ℝ => v + b))
        (by fun_prop : Measurable (fun u : ℝ => a * u)),
      Real.map_volume_mul_left ha]
    rw [MeasureTheory.Measure.map_smul]
    congr 1
    exact MeasureTheory.map_add_right_eq_self MeasureTheory.volume b
    all_goals exact (by fun_prop : Measurable (fun v : ℝ => v + b)).aemeasurable
  rw [← MeasureTheory.lintegral_map hF (by fun_prop : Measurable (fun u : ℝ => a * u + b)), hmap]
  rw [MeasureTheory.lintegral_smul_measure]
  rfl

/-- `Bsum f M₂` is measurable for every `f : ℝ → ℝ`. -/
lemma measurable_Bsum (f : ℝ → ℝ) (M₂ : ℝ) : Measurable (Bsum f M₂) := by
  have h : Bsum f M₂ = fun u => ∑ m ∈ R2 M₂, ((m : ℝ) : ℂ) * Fhat f ((m : ℝ) * u) := rfl
  rw [h]
  exact Finset.measurable_sum _ (fun m _ => measurable_const.mul
    ((Fhat_measurable f).comp (measurable_const_mul ((m : ℝ)))))

/-- Membership in `(Ioi 2 ∪ Iio (-2))` is `2 < |τ|`. -/
lemma mem_far_iff (τ : ℝ) : τ ∈ (Set.Ioi (2:ℝ) ∪ Set.Iio (-2)) ↔ 2 < |τ| := by
  rw [Set.mem_union, Set.mem_Ioi, Set.mem_Iio, lt_abs]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by linarith)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by linarith)

/-- **Per-`ℓ` change of variables**. -/
lemma far_inner_eq {K M₂ M₃ : ℝ} (hM₃ : 0 < M₃) (f : ℝ → ℝ) (ℓ : ℤ) :
    ∫⁻ τ in (Set.Ioi (2:ℝ) ∪ Set.Iio (-2)),
        ENNReal.ofReal (‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 * ‖psi1hat K τ‖ ^ 2)
      = ENNReal.ofReal M₃ *
        ∫⁻ u, (if 2 / M₃ < |u - (ℓ : ℝ)| then
          ENNReal.ofReal (‖Bsum f M₂ u‖ ^ 2 * ‖psi1hat K (M₃ * (u - (ℓ : ℝ)))‖ ^ 2) else 0) := by
  have hM₃ne : M₃ ≠ 0 := ne_of_gt hM₃
  set G : ℝ → ENNReal := fun u =>
      if 2 / M₃ < |u - (ℓ : ℝ)| then
        ENNReal.ofReal (‖Bsum f M₂ u‖ ^ 2 * ‖psi1hat K (M₃ * (u - (ℓ : ℝ)))‖ ^ 2) else 0
    with hG
  have hGmeas : Measurable G := by
    rw [hG]
    refine Measurable.ite ?_ ?_ measurable_const
    · exact measurableSet_lt measurable_const
        ((measurable_id.sub measurable_const).abs)
    · refine ENNReal.measurable_ofReal.comp ?_
      refine Measurable.mul ?_ ?_
      · exact (measurable_Bsum f M₂).norm.pow_const 2
      · exact ((psi1hat_continuous K).measurable.comp (measurable_const.mul
          (measurable_id.sub measurable_const))).norm.pow_const 2
  have key : ∀ τ : ℝ, (Set.Ioi (2:ℝ) ∪ Set.Iio (-2)).indicator
        (fun τ => ENNReal.ofReal (‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 * ‖psi1hat K τ‖ ^ 2)) τ
      = G ((1 / M₃) * τ + (ℓ : ℝ)) := by
    intro τ
    have harg : (1 / M₃) * τ + (ℓ : ℝ) - (ℓ : ℝ) = τ / M₃ := by ring
    have hcond : (2 / M₃ < |(1 / M₃) * τ + (ℓ : ℝ) - (ℓ : ℝ)|) ↔ 2 < |τ| := by
      rw [harg, abs_div, abs_of_pos hM₃, div_lt_div_iff_of_pos_right hM₃]
    simp only [Set.indicator_apply, hG]
    by_cases hτ : 2 < |τ|
    · have hmem : τ ∈ (Set.Ioi (2:ℝ) ∪ Set.Iio (-2)) := (mem_far_iff τ).mpr hτ
      rw [if_pos hmem, if_pos (hcond.mpr hτ)]
      rw [show (1 / M₃) * τ + (ℓ : ℝ) = (ℓ : ℝ) + τ / M₃ by ring, Hfun_eq_Bsum]
      rw [show M₃ * ((ℓ : ℝ) + τ / M₃ - (ℓ : ℝ)) = τ by field_simp; ring]
    · have hmem : τ ∉ (Set.Ioi (2:ℝ) ∪ Set.Iio (-2)) := fun h => hτ ((mem_far_iff τ).mp h)
      rw [if_neg hmem, if_neg (fun h => hτ (hcond.mp h))]
  calc ∫⁻ τ in (Set.Ioi (2:ℝ) ∪ Set.Iio (-2)),
        ENNReal.ofReal (‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 * ‖psi1hat K τ‖ ^ 2)
      = ∫⁻ τ, (Set.Ioi (2:ℝ) ∪ Set.Iio (-2)).indicator
          (fun τ => ENNReal.ofReal (‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 * ‖psi1hat K τ‖ ^ 2)) τ :=
        (MeasureTheory.lintegral_indicator (measurableSet_Ioi.union measurableSet_Iio) _).symm
    _ = ∫⁻ τ, G ((1 / M₃) * τ + (ℓ : ℝ)) := MeasureTheory.lintegral_congr key
    _ = ENNReal.ofReal |(1 / M₃)⁻¹| * ∫⁻ u, G u :=
        lintegral_comp_affine hGmeas (by positivity)
    _ = ENNReal.ofReal M₃ *
        ∫⁻ u, (if 2 / M₃ < |u - (ℓ : ℝ)| then
          ENNReal.ofReal (‖Bsum f M₂ u‖ ^ 2 * ‖psi1hat K (M₃ * (u - (ℓ : ℝ)))‖ ^ 2) else 0) := by
        rw [hG]
        congr 2
        rw [inv_div, div_one, abs_of_pos hM₃]

/-- `ofReal` of a real `tsum` is at most the `ℝ≥0∞`-`tsum` of the `ofReal`s. -/
lemma ofReal_tsum_le_tsum {ι : Type*} {A : ι → ℝ} {X : ι → ENNReal}
    (hAnn : ∀ i, 0 ≤ A i) (h : ∀ i, ENNReal.ofReal (A i) ≤ X i) :
    ENNReal.ofReal (∑' i, A i) ≤ ∑' i, X i := by
  by_cases hsum : Summable A
  · rw [ENNReal.ofReal_tsum_of_nonneg hAnn hsum]
    exact ENNReal.tsum_le_tsum h
  · rw [tsum_eq_zero_of_not_summable hsum, ENNReal.ofReal_zero]
    positivity

theorem bsum_far_weight_bound {C₀ K : ℝ} (hC₀ : 1 ≤ C₀) (hK : 0 < K) :
    ∃ C : ℝ, 0 < C ∧ ∀ M₂ M₃ : ℝ, 0 < M₂ → 1 ≤ M₃ → ∀ f : ℝ → ℝ, Continuous f →
      (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
      FarMass K f M₂ M₃ ≤ C * M₃ * ∫ u, ‖Bsum f M₂ u‖ ^ 2 := by
  obtain ⟨Cw, hCwpos, hCw⟩ := far_weight_uniform_bound hK
  refine ⟨Cw, hCwpos, ?_⟩
  intro M₂ M₃ hM₂ hM₃ f hf hfnn hsup
  have hM₃pos : 0 < M₃ := lt_of_lt_of_le zero_lt_one hM₃
  set FR : ℤ → ℝ → ENNReal := fun ℓ u => if 2 / M₃ < |u - (ℓ:ℝ)| then
      ENNReal.ofReal (‖Bsum f M₂ u‖ ^ 2 * ‖psi1hat K (M₃ * (u - (ℓ:ℝ)))‖ ^ 2) else 0
    with hFR
  set Gd : ℝ → ENNReal := fun u => ENNReal.ofReal (‖Bsum f M₂ u‖ ^ 2) with hGd
  set WT : ℝ → ENNReal := fun u => ∑' ℓ : ℤ, (if 2 / M₃ < |u - (ℓ:ℝ)| then
      ENNReal.ofReal (‖psi1hat K (M₃ * (u - (ℓ:ℝ)))‖ ^ 2) else 0) with hWT
  set Y : ENNReal := ∫⁻ u, Gd u with hY
  have hBmeas : Measurable (fun u : ℝ => ‖Bsum f M₂ u‖ ^ 2) :=
    (measurable_Bsum f M₂).norm.pow_const 2
  have hGdmeas : Measurable Gd := by
    rw [hGd]; exact ENNReal.measurable_ofReal.comp hBmeas
  have hFRmeas : ∀ ℓ : ℤ, Measurable (FR ℓ) := by
    intro ℓ
    rw [hFR]
    refine Measurable.ite ?_ ?_ measurable_const
    · exact measurableSet_lt measurable_const (measurable_id.sub measurable_const).abs
    · refine ENNReal.measurable_ofReal.comp (Measurable.mul hBmeas ?_)
      exact (((psi1hat_continuous K).measurable.comp
        (measurable_const.mul (measurable_id.sub measurable_const))).norm.pow_const 2)
  have hHfunmeas : ∀ ℓ : ℤ, Measurable (fun τ : ℝ => Hfun f M₂ M₃ ℓ τ) := by
    intro ℓ
    have heq : (fun τ : ℝ => Hfun f M₂ M₃ ℓ τ)
        = fun τ : ℝ => Bsum f M₂ ((ℓ:ℝ) + τ / M₃) := by
      funext τ; rw [Hfun_eq_Bsum]
    rw [heq]
    exact (measurable_Bsum f M₂).comp (measurable_const.add (measurable_id.div_const M₃))
  have hper : ∀ ℓ : ℤ, (∫⁻ τ in (Set.Ioi (2:ℝ) ∪ Set.Iio (-2)),
        ENNReal.ofReal (‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 * ‖psi1hat K τ‖ ^ 2))
      = ENNReal.ofReal M₃ * ∫⁻ u, FR ℓ u := fun ℓ => far_inner_eq hM₃pos f ℓ
  have h2 : (∑' ℓ : ℤ, ∫⁻ τ in (Set.Ioi (2:ℝ) ∪ Set.Iio (-2)),
        ENNReal.ofReal (‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 * ‖psi1hat K τ‖ ^ 2))
      = ENNReal.ofReal M₃ * ∫⁻ u, (∑' ℓ : ℤ, FR ℓ u) := by
    rw [tsum_congr hper, ENNReal.tsum_mul_left]
    congr 1
    exact (MeasureTheory.lintegral_tsum (fun ℓ => (hFRmeas ℓ).aemeasurable)).symm
  have h3 : ∀ u : ℝ, (∑' ℓ : ℤ, FR ℓ u) = Gd u * WT u := by
    intro u
    have hpt : ∀ ℓ : ℤ, FR ℓ u = Gd u * (if 2 / M₃ < |u - (ℓ:ℝ)| then
        ENNReal.ofReal (‖psi1hat K (M₃ * (u - (ℓ:ℝ)))‖ ^ 2) else 0) := by
      intro ℓ
      simp only [hFR, hGd]
      by_cases hc : 2 / M₃ < |u - (ℓ:ℝ)|
      · simp only [hc, if_true]
        rw [ENNReal.ofReal_mul (sq_nonneg _)]
      · simp only [hc, if_false, mul_zero]
    rw [tsum_congr hpt, ENNReal.tsum_mul_left, hWT]
  have h4 : (∫⁻ u, Gd u * WT u) ≤ ENNReal.ofReal Cw * Y := by
    calc (∫⁻ u, Gd u * WT u) ≤ ∫⁻ u, Gd u * ENNReal.ofReal Cw :=
          MeasureTheory.lintegral_mono (fun u => mul_le_mul_right (hCw M₃ hM₃ u) (Gd u))
      _ = ∫⁻ u, ENNReal.ofReal Cw * Gd u := by simp only [mul_comm]
      _ = ENNReal.ofReal Cw * Y := by
          rw [hY]; exact MeasureTheory.lintegral_const_mul _ hGdmeas
  have h5 : (∑' ℓ : ℤ, ∫⁻ τ in (Set.Ioi (2:ℝ) ∪ Set.Iio (-2)),
        ENNReal.ofReal (‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 * ‖psi1hat K τ‖ ^ 2))
      ≤ ENNReal.ofReal M₃ * ENNReal.ofReal Cw * Y := by
    rw [h2, MeasureTheory.lintegral_congr h3]
    calc ENNReal.ofReal M₃ * ∫⁻ u, Gd u * WT u
        ≤ ENNReal.ofReal M₃ * (ENNReal.ofReal Cw * Y) := mul_le_mul_right h4 _
      _ = ENNReal.ofReal M₃ * ENNReal.ofReal Cw * Y := by rw [mul_assoc]
  have hA : ∀ ℓ : ℤ, (∫ τ in (Set.Ioi (2:ℝ) ∪ Set.Iio (-2)),
        ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 * ‖psi1hat K τ‖ ^ 2)
      = (∫⁻ τ in (Set.Ioi (2:ℝ) ∪ Set.Iio (-2)),
        ENNReal.ofReal (‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 * ‖psi1hat K τ‖ ^ 2)).toReal := by
    intro ℓ
    exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (μ := MeasureTheory.volume.restrict (Set.Ioi (2:ℝ) ∪ Set.Iio (-2)))
      (Filter.Eventually.of_forall (fun τ => by positivity))
      (((hHfunmeas ℓ).norm.pow_const 2).mul
        ((psi1hat_continuous K).measurable.norm.pow_const 2)).aestronglyMeasurable
  have hFMnn : 0 ≤ FarMass K f M₂ M₃ :=
    tsum_nonneg (fun ℓ => integral_nonneg (fun τ => by positivity))
  have h6 : ENNReal.ofReal (FarMass K f M₂ M₃) ≤
      ∑' ℓ : ℤ, ∫⁻ τ in (Set.Ioi (2:ℝ) ∪ Set.Iio (-2)),
        ENNReal.ofReal (‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 * ‖psi1hat K τ‖ ^ 2) := by
    rw [FarMass]
    refine ofReal_tsum_le_tsum (fun ℓ => integral_nonneg (fun τ => by positivity))
      (fun ℓ => ?_)
    rw [hA ℓ]
    exact ENNReal.ofReal_toReal_le
  have Yne : Y ≠ ⊤ := by
    have hgcont : Continuous (fun u : ℝ => ((Hprof f M₂ u : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (Hprof_continuous hf M₂)
    have hgcs : HasCompactSupport (fun u : ℝ => ((Hprof f M₂ u : ℝ) : ℂ)) :=
      (Hprof_hasCompactSupport hsup hC₀ hM₂.le).comp_left
        (g := fun z : ℝ => (z : ℂ)) (by simp)
    have hplan := lintegral_ofReal_fourier_sq_eq (fun u : ℝ => ((Hprof f M₂ u : ℝ) : ℂ))
      hgcont hgcs
    have hfin : (∫⁻ u, ENNReal.ofReal (‖Fhat (Hprof f M₂) u‖ ^ 2)) ≠ ⊤ := by
      rw [show (fun u : ℝ => ENNReal.ofReal (‖Fhat (Hprof f M₂) u‖ ^ 2))
            = (fun u : ℝ => ENNReal.ofReal
                (‖𝓕 (fun u : ℝ => ((Hprof f M₂ u : ℝ) : ℂ)) u‖ ^ 2)) from rfl, hplan]
      exact lintegral_ofReal_normSq_ne_top _ hgcont hgcs
    have hpt : ∀ u : ℝ, ENNReal.ofReal (‖Bsum f M₂ u‖ ^ 2)
        = ENNReal.ofReal (‖Fhat (Hprof f M₂) u‖ ^ 2) :=
      fun u => by rw [Bsum_eq_Fhat_Hprof hf hsup hC₀ hM₂ u]
    rw [hY, hGd, MeasureTheory.lintegral_congr hpt]
    exact hfin
  have hZne : ENNReal.ofReal M₃ * ENNReal.ofReal Cw * Y ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) Yne
  have hle : FarMass K f M₂ M₃
      ≤ (ENNReal.ofReal M₃ * ENNReal.ofReal Cw * Y).toReal := by
    have h1 := ENNReal.toReal_mono hZne (le_trans h6 h5)
    rwa [ENNReal.toReal_ofReal hFMnn] at h1
  have hYt : Y.toReal = ∫ u, ‖Bsum f M₂ u‖ ^ 2 := by
    rw [hY, hGd]
    exact (MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun u => sq_nonneg _)) hBmeas.aestronglyMeasurable).symm
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hM₃pos.le,
      ENNReal.toReal_ofReal hCwpos.le, hYt] at hle
  calc FarMass K f M₂ M₃ ≤ M₃ * Cw * (∫ u, ‖Bsum f M₂ u‖ ^ 2) := hle
    _ = Cw * M₃ * (∫ u, ‖Bsum f M₂ u‖ ^ 2) := by ring

end

end Work.GM.Affine
