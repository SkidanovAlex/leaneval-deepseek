import Mathlib
import Submission.Work.TMComp.LocCantor.C8_jump
import Submission.Work.TMComp.LocCantor.K2_integral_le
import Submission.Work.TMComp.LocCantor.K2_pointwise_eq
import Submission.Work.TMComp.LocCantor.K2_continuous_prod
import Submission.Work.TMComp.LocCantor.K2_excess_measurable
import Submission.Work.TMComp.LocCantor.K2_interval_le_excess

open MeasureTheory Filter Topology Set
open Work.TMComp.Kotani

/-- Alias for `Filter.atTop`, needed because the requested statement of
`K2_integral_of_excess` is written with `Filter.AtTop`. -/
abbrev Filter.AtTop {α : Type*} [Preorder α] : Filter α := Filter.atTop

noncomputable section

namespace Work.TMComp.LocCantor

/-- The two-dimensional `K2`-integrand along the horizontal line `Im = ε`, kept in the pair
form so that `K2` never has to be unfolded during unification. -/
private def K2slice (α lam : ℝ) (ε : ℝ) : ℝ × ℝ → ℝ :=
  fun p => K2 α lam ((p.1 : ℂ) + (ε : ℂ) * Complex.I) p.2

private theorem K2slice_apply' (α lam ε : ℝ) (p : ℝ × ℝ) :
    K2slice α lam ε p = K2 α lam ((p.1 : ℂ) + (ε : ℂ) * Complex.I) p.2 := rfl

private theorem K2slice_apply (α lam ε E y : ℝ) :
    K2slice α lam ε (E, y) = K2 α lam ((E : ℂ) + (ε : ℂ) * Complex.I) y := rfl

theorem K2_integral_of_excess (α lam : ℝ) {K : Set ℝ} (hK : MeasurableSet K) (hKfin : MeasureTheory.volume K < ⊤) (e : ℕ → ℝ) (he : ∀ j : ℕ, 0 < e j) {C : ℝ} (hbound : ∀ j : ℕ, ∀ E ∈ K, (Work.TMComp.Kotani.ell α lam ((E : ℂ) + (e j : ℂ) * Complex.I) / e j - ∫ y in (0 : ℝ)..1, (-1 / Work.TMComp.Kotani.defect α lam ((E : ℂ) + (e j : ℂ) * Complex.I) y).im) ≤ C) (hexc : Filter.Tendsto (fun j : ℕ => ∫ E in K, (Work.TMComp.Kotani.ell α lam ((E : ℂ) + (e j : ℂ) * Complex.I) / e j - ∫ y in (0 : ℝ)..1, (-1 / Work.TMComp.Kotani.defect α lam ((E : ℂ) + (e j : ℂ) * Complex.I) y).im)) Filter.atTop (nhds 0)) : (∀ j : ℕ, MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => Work.TMComp.LocCantor.K2 α lam ((p.1 : ℂ) + (e j : ℂ) * Complex.I) p.2) (K ×ˢ Set.Ioc (0 : ℝ) 1)) ∧ Filter.Tendsto (fun j : ℕ => ∫ p in K ×ˢ Set.Ioc (0 : ℝ) 1, Work.TMComp.LocCantor.K2 α lam ((p.1 : ℂ) + (e j : ℂ) * Complex.I) p.2) Filter.AtTop (nhds 0) := by
  have hnonneg_exc : ∀ (ε : ℝ), 0 < ε → ∀ E : ℝ,
      0 ≤ ell α lam ((E : ℂ) + (ε : ℂ) * Complex.I) / ε
          - ∫ y in (0 : ℝ)..1, (-1 / defect α lam ((E : ℂ) + (ε : ℂ) * Complex.I) y).im := by
    intro ε hε E
    have hEim : ((E : ℂ) + (ε : ℂ) * Complex.I).im = ε := by simp
    have h := ell_defect_le α lam ((E : ℂ) + (ε : ℂ) * Complex.I) (by rw [hEim]; exact hε)
    rw [hEim] at h
    linarith
  by_cases hC : 0 ≤ C
  · have key : ∀ j : ℕ,
        IntegrableOn (K2slice α lam (e j)) (K ×ˢ Set.Ioc (0:ℝ) 1)
        ∧ (∫ p in K ×ˢ Set.Ioc (0:ℝ) 1, K2slice α lam (e j) p)
            = ∫ E in K, ∫ y in (0:ℝ)..1, K2slice α lam (e j) (E, y)
        ∧ (∫ E in K, ∫ y in (0:ℝ)..1, K2slice α lam (e j) (E, y))
            ≤ 4 * ∫ E in K, (ell α lam ((E : ℂ) + (e j : ℂ) * Complex.I) / e j
                - ∫ y in (0:ℝ)..1, (-1 / defect α lam ((E : ℂ) + (e j : ℂ) * Complex.I) y).im) := by
      intro j
      have hε : 0 < e j := he j
      have hcont : Continuous (K2slice α lam (e j)) := by
        change Continuous (fun p : ℝ × ℝ => K2 α lam ((p.1 : ℂ) + (e j : ℂ) * Complex.I) p.2)
        exact K2_continuous_prod α lam hε
      have hnonneg : ∀ p : ℝ × ℝ, 0 ≤ K2slice α lam (e j) p := by
        intro p
        rw [K2slice_apply']
        exact K2_nonneg α lam (by simpa using hε) p.2
      have hGle : ∀ E : ℝ, (∫ y in (0:ℝ)..1, K2slice α lam (e j) (E, y))
            ≤ 4 * (ell α lam ((E : ℂ) + (e j : ℂ) * Complex.I) / e j
                - ∫ y in (0:ℝ)..1, (-1 / defect α lam ((E : ℂ) + (e j : ℂ) * Complex.I) y).im) := by
        intro E
        simpa only [K2slice_apply] using K2_interval_le_excess α lam hε E
      have hGnonneg : ∀ E : ℝ,
          0 ≤ ∫ y in (0:ℝ)..1, K2slice α lam (e j) (E, y) := by
        intro E
        apply intervalIntegral.integral_nonneg_of_forall (by norm_num)
        intro y
        exact hnonneg (E, y)
      have hexc_meas : Measurable (fun E : ℝ => ell α lam ((E : ℂ) + (e j : ℂ) * Complex.I) / e j
          - ∫ y in (0:ℝ)..1, (-1 / defect α lam ((E : ℂ) + (e j : ℂ) * Complex.I) y).im) :=
        K2_excess_measurable α lam hε
      haveI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr (ne_of_lt hKfin)
      have h4exc_int : Integrable (fun E : ℝ => 4 * (ell α lam ((E : ℂ) + (e j : ℂ) * Complex.I) / e j
          - ∫ y in (0:ℝ)..1, (-1 / defect α lam ((E : ℂ) + (e j : ℂ) * Complex.I) y).im))
          (volume.restrict K) := by
        refine Integrable.of_bound ((hexc_meas.const_mul 4).aemeasurable.aestronglyMeasurable)
          (4 * C) ?_
        rw [MeasureTheory.ae_restrict_iff' hK]
        filter_upwards with E hE
        have h1 : 0 ≤ ell α lam ((E : ℂ) + (e j : ℂ) * Complex.I) / e j
            - ∫ y in (0:ℝ)..1, (-1 / defect α lam ((E : ℂ) + (e j : ℂ) * Complex.I) y).im :=
          hnonneg_exc (e j) hε E
        have h2 : ell α lam ((E : ℂ) + (e j : ℂ) * Complex.I) / e j
            - ∫ y in (0:ℝ)..1, (-1 / defect α lam ((E : ℂ) + (e j : ℂ) * Complex.I) y).im
            ≤ C := hbound j E hE
        rw [Real.norm_of_nonneg (by linarith)]
        linarith
      have hvol : volume.restrict (K ×ˢ Set.Ioc (0:ℝ) 1)
          = (volume.restrict K).prod (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
        rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ,
          ← MeasureTheory.Measure.prod_restrict K (Set.Ioc (0:ℝ) 1)]
      have hinner : ∀ E : ℝ,
          ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (K2slice α lam (e j) (E, y))
            = ENNReal.ofReal (∫ y in (0:ℝ)..1, K2slice α lam (e j) (E, y)) := by
        intro E
        have hmap : Continuous (fun y : ℝ => ((E, y) : ℝ × ℝ)) :=
          continuous_const.prodMk continuous_id
        have hf_cont : Continuous (fun y : ℝ => K2slice α lam (e j) (E, y)) := hcont.comp hmap
        have hf_int : Integrable (fun y : ℝ => K2slice α lam (e j) (E, y))
            (volume.restrict (Set.Ioc (0:ℝ) 1)) := hf_cont.integrableOn_Ioc
        have hf_nonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc (0:ℝ) 1)]
            (fun y : ℝ => K2slice α lam (e j) (E, y)) :=
          Filter.Eventually.of_forall (fun y => hnonneg (E, y))
        have h := ofReal_integral_eq_lintegral_ofReal hf_int hf_nonneg
        rw [← h]
        congr 1
        exact (intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)).symm
      have hmono : ∫⁻ E in K, ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (K2slice α lam (e j) (E, y))
          ≤ ∫⁻ E in K, ENNReal.ofReal (4 * C) := by
        refine lintegral_mono_ae ?_
        rw [MeasureTheory.ae_restrict_iff' hK]
        filter_upwards with E hE
        rw [hinner E]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 := hGle E
        have h2 : ell α lam ((E : ℂ) + (e j : ℂ) * Complex.I) / e j
            - ∫ y in (0:ℝ)..1, (-1 / defect α lam ((E : ℂ) + (e j : ℂ) * Complex.I) y).im
            ≤ C := hbound j E hE
        linarith
      have hconst : ∫⁻ E in K, ENNReal.ofReal (4 * C) = ENNReal.ofReal (4 * C) * volume K := by
        rw [MeasureTheory.lintegral_const]
        congr 1
        rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
      have hlin1 : ∫⁻ p in K ×ˢ Set.Ioc (0:ℝ) 1, ENNReal.ofReal (K2slice α lam (e j) p)
          = ∫⁻ E in K, ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (K2slice α lam (e j) (E, y)) := by
        rw [hvol]
        exact MeasureTheory.lintegral_prod _
          ((ENNReal.continuous_ofReal.comp hcont).measurable.aemeasurable)
      have hfin : ∫⁻ p in K ×ˢ Set.Ioc (0:ℝ) 1, ENNReal.ofReal (K2slice α lam (e j) p) < ⊤ := by
        rw [hlin1]
        calc ∫⁻ E in K, ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (K2slice α lam (e j) (E, y))
            ≤ ∫⁻ E in K, ENNReal.ofReal (4 * C) := hmono
          _ = ENNReal.ofReal (4 * C) * volume K := hconst
          _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKfin
      refine ⟨?_, ?_, ?_⟩
      · refine ⟨hcont.aestronglyMeasurable, ?_⟩
        rw [MeasureTheory.hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnonneg)]
        exact hfin
      · have hint : Integrable (K2slice α lam (e j))
            ((volume.restrict K).prod (volume.restrict (Set.Ioc (0:ℝ) 1))) := by
          rw [← hvol]
          exact ⟨hcont.aestronglyMeasurable, by
            rw [MeasureTheory.hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnonneg)]
            exact hfin⟩
        rw [hvol, MeasureTheory.integral_prod _ hint]
        congr 1
        ext E
        exact (intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)).symm
      · have h := MeasureTheory.integral_mono_of_nonneg
          (μ := volume.restrict K)
          (f := fun E : ℝ => ∫ y in (0:ℝ)..1, K2slice α lam (e j) (E, y))
          (g := fun E : ℝ => 4 * (ell α lam ((E : ℂ) + (e j : ℂ) * Complex.I) / e j
              - ∫ y in (0:ℝ)..1, (-1 / defect α lam ((E : ℂ) + (e j : ℂ) * Complex.I) y).im))
          (Filter.Eventually.of_forall hGnonneg) h4exc_int
          (Filter.Eventually.of_forall (fun E => by
            have h1 := hGle E
            have h2 := hnonneg_exc (e j) hε E
            linarith))
        simpa [MeasureTheory.integral_const_mul] using h
    constructor
    · intro j
      show IntegrableOn (fun p : ℝ × ℝ => K2 α lam ((p.1 : ℂ) + (e j : ℂ) * Complex.I) p.2)
        (K ×ˢ Set.Ioc (0:ℝ) 1)
      exact (key j).1
    · have hnonneg_int : ∀ j : ℕ,
          0 ≤ (∫ p in K ×ˢ Set.Ioc (0:ℝ) 1,
              K2 α lam ((p.1 : ℂ) + (e j : ℂ) * Complex.I) p.2) := by
        intro j
        change 0 ≤ ∫ p in K ×ˢ Set.Ioc (0:ℝ) 1, K2slice α lam (e j) p
        exact MeasureTheory.integral_nonneg (fun p => by
          rw [K2slice_apply']
          exact K2_nonneg α lam (by simpa using he j) p.2)
      have hle : ∀ j : ℕ,
          (∫ p in K ×ˢ Set.Ioc (0:ℝ) 1, K2 α lam ((p.1 : ℂ) + (e j : ℂ) * Complex.I) p.2)
            ≤ 4 * ∫ E in K, (ell α lam ((E : ℂ) + (e j : ℂ) * Complex.I) / e j
                - ∫ y in (0:ℝ)..1, (-1 / defect α lam ((E : ℂ) + (e j : ℂ) * Complex.I) y).im) := by
        intro j
        change (∫ p in K ×ˢ Set.Ioc (0:ℝ) 1, K2slice α lam (e j) p) ≤ _
        rw [(key j).2.1]
        exact (key j).2.2
      have hlim : Filter.Tendsto (fun j : ℕ => 4 * ∫ E in K,
            (ell α lam ((E : ℂ) + (e j : ℂ) * Complex.I) / e j
              - ∫ y in (0:ℝ)..1, (-1 / defect α lam ((E : ℂ) + (e j : ℂ) * Complex.I) y).im))
          Filter.atTop (nhds 0) := by
        simpa using hexc.const_mul 4
      exact squeeze_zero hnonneg_int hle hlim
  · have hKempty : K = ∅ := by
      rw [← Set.not_nonempty_iff_eq_empty]
      rintro ⟨E, hE⟩
      have h1 := hbound 0 E hE
      have h2 := hnonneg_exc (e 0) (he 0) E
      linarith
    constructor
    · intro j
      rw [hKempty, Set.empty_prod]
      exact MeasureTheory.integrableOn_empty
    · rw [hKempty]
      simp only [Set.empty_prod, MeasureTheory.setIntegral_empty]
      exact tendsto_const_nhds

end Work.TMComp.LocCantor
