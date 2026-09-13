import Mathlib
import Submission.Commons.Measure.Distribution.exists_measure_of_positive_functional
import Submission.Commons.Measure.Integration.nonneg_integral_eq_lam
import Submission.Commons.Measure.Integration.integrable_nonneg_of_contDiff_tsupport_subset

namespace Commons.Measure.Distribution

open MeasureTheory Set Metric Filter Function
open scoped ContDiff ENNReal Topology CompactlySupported

noncomputable section

open MeasureTheory Set Metric in
open scoped ContDiff ENNReal Topology in
theorem exists_measure_of_positive_functional_compact {n : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin n))} (hs : IsOpen s)
    (Λ : (EuclideanSpace ℝ (Fin n) → ℝ) → ℝ)
    (hadd : ∀ φ ψ, ContDiff ℝ ∞ φ → tsupport φ ⊆ s → ContDiff ℝ ∞ ψ → tsupport ψ ⊆ s →
      Λ (φ + ψ) = Λ φ + Λ ψ)
    (hsmul : ∀ (a : ℝ) φ, ContDiff ℝ ∞ φ → tsupport φ ⊆ s → Λ (a • φ) = a * Λ φ)
    (hpos : ∀ φ, ContDiff ℝ ∞ φ → tsupport φ ⊆ s → 0 ≤ φ → 0 ≤ Λ φ) :
    ∃ μ : Measure (EuclideanSpace ℝ (Fin n)), μ sᶜ = 0 ∧
      (∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ s → μ K < ⊤) ∧
      (∀ φ, ContDiff ℝ ∞ φ → tsupport φ ⊆ s → ∫ x, φ x ∂μ = Λ φ) := by
  classical
  obtain ⟨g, hgeq, hgpos⟩ := riesz_extension (PointedCone.positive ℝ C_c(s, ℝ))
    (partialLM hadd hsmul)
    (fun x hx => by
      change 0 ≤ Λ (zext (x : C_c(s, ℝ)))
      exact hpos _ x.2 (tsupport_zext_subset _) (smoothSub_nonneg_mem hadd hsmul x hx))
    (fun y => smoothSub_dense hadd hsmul hs y)
  haveI hlc : LocallyCompactSpace s := hs.locallyCompactSpace
  let Gpos : C_c(s, ℝ) →ₚ[ℝ] ℝ :=
    { toLinearMap := g
      monotone' := fun a b hab => by
        have h1 : 0 ≤ b - a := sub_nonneg.mpr hab
        have h2 : 0 ≤ g b - g a := by rw [← map_sub]; exact hgpos (b - a) h1
        exact sub_nonneg.mp h2 }
  set ν : Measure s := RealRMK.rieszMeasure Gpos with hνdef
  set μ : Measure (EuclideanSpace ℝ (Fin n)) := Measure.map Subtype.val ν with hμdef
  haveI hνfc : IsFiniteMeasureOnCompacts ν :=
    (RealRMK.regular_rieszMeasure Gpos).toIsFiniteMeasureOnCompacts
  refine ⟨μ, ?_, ?_, ?_⟩
  · have hmeas : Measurable (Subtype.val : s → EuclideanSpace ℝ (Fin n)) := measurable_subtype_coe
    have hpre : (Subtype.val : s → EuclideanSpace ℝ (Fin n)) ⁻¹' (sᶜ) = ∅ := by
      ext z; simp
    rw [hμdef, Measure.map_apply hmeas hs.isClosed_compl.measurableSet, hpre, measure_empty]
  · intro K hK hKs
    have hmeas : Measurable (Subtype.val : s → EuclideanSpace ℝ (Fin n)) := measurable_subtype_coe
    have hcomp : IsCompact ((Subtype.val : s → EuclideanSpace ℝ (Fin n)) ⁻¹' K) :=
      Topology.IsInducing.subtypeVal.isCompact_preimage' hK
        (by simpa [Subtype.range_coe] using hKs)
    rw [hμdef, Measure.map_apply hmeas hK.isClosed.measurableSet]
    exact hνfc.lt_top_of_isCompact hcomp
  · intro φ hφ hφs
    refine (integral_eq_lam_general hs ?_ hadd hsmul hpos ?_ hφ hφs).2
    · intro f hf hfc hfs
      have hFint : Integrable (fun z : s => f (z : EuclideanSpace ℝ (Fin n))) ν :=
        Continuous.integrable_of_hasCompactSupport (hf.continuous.comp continuous_subtype_val)
          (by
            rw [hasCompactSupport_def]
            have hle : tsupport (fun z : s => f (z : EuclideanSpace ℝ (Fin n)))
                ⊆ Subtype.val ⁻¹' tsupport f :=
              closure_minimal (fun z hz => subset_tsupport f hz)
                ((isClosed_tsupport f).preimage continuous_subtype_val)
            exact (Topology.IsInducing.subtypeVal.isCompact_preimage' hfc.isCompact
              (by simpa [Subtype.range_coe] using hfs)).of_isClosed_subset
              (isClosed_tsupport (fun z : s => f (z : EuclideanSpace ℝ (Fin n)))) hle)
      have hfin : ∫⁻ x, ‖f x‖ₑ ∂μ < ⊤ := by
        rw [hμdef, lintegral_map (hf.continuous.measurable.enorm) measurable_subtype_coe]
        exact hFint.2
      exact ⟨hf.continuous.measurable.aestronglyMeasurable, hasFiniteIntegral_iff_enorm.mpr hfin⟩
    · intro f hf hfc hfs
      have hFmem : toCc f hf.continuous hfc hfs ∈ smoothSub s := by
        change ContDiff ℝ ∞ (zext (toCc f hf.continuous hfc hfs))
        rw [zext_toCc]; exact hf
      have h1 : ∫ x, f x ∂μ = ∫ z, (toCc f hf.continuous hfc hfs) z ∂ν := by
        rw [hμdef, (MeasurableEmbedding.subtype_coe hs.measurableSet).integral_map f]
        rfl
      rw [h1, hνdef]
      simp only [RealRMK.integral_rieszMeasure]
      change g (toCc f hf.continuous hfc hfs) = Λ f
      rw [hgeq ⟨toCc f hf.continuous hfc hfs, hFmem⟩]
      change Λ (zext (toCc f hf.continuous hfc hfs)) = Λ f
      rw [zext_toCc]

end

end Commons.Measure.Distribution
