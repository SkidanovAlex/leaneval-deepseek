import Mathlib
import Submission.Work.Mostow.visualDefs

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

/-- The unnormalised surface measure of the unit sphere of `E n`, pushed forward to `E n`.
This is the measure `m` out of which `sigma n` is built:
`sigma n = (sphM n Set.univ)⁻¹ • sphM n`. -/
def sphM (n : ℕ) : Measure (E n) := ((volume : Measure (E n)).toSphere).map Subtype.val

theorem sphM_apply (n : ℕ) {s : Set (E n)} (hs : MeasurableSet s) :
    sphM n s = volume.toSphere (Subtype.val ⁻¹' s) := by
  rw [sphM, Measure.map_apply continuous_subtype_val.measurable hs]

theorem sphM_univ (n : ℕ) :
    sphM n Set.univ = (Module.finrank ℝ (E n) : ℝ≥0∞) * volume (Metric.ball (0 : E n) 1) := by
  rw [sphM, Measure.map_apply continuous_subtype_val.measurable MeasurableSet.univ,
    Set.preimage_univ, Measure.toSphere_apply_univ]

theorem sphM_univ_ne_zero (n : ℕ) (hn : 1 ≤ n) : sphM n Set.univ ≠ 0 := by
  rw [sphM_univ, finrank_euclideanSpace_fin]
  exact mul_ne_zero (by exact_mod_cast (show n ≠ 0 by omega))
    (Metric.measure_ball_pos volume (0 : E n) one_pos).ne'

theorem sphM_univ_ne_top (n : ℕ) : sphM n Set.univ ≠ ⊤ := by
  rw [sphM_univ]
  exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) measure_ball_lt_top.ne

/-- `sphM n` is carried by the unit sphere. -/
theorem sphM_compl_sphere (n : ℕ) : sphM n (Sph n)ᶜ = 0 := by
  rw [sphM, show (Sph n : Set (E n)) = Metric.sphere (0 : E n) 1 from rfl]
  rw [Measure.map_apply continuous_subtype_val.measurable
    (Metric.isClosed_sphere.measurableSet.compl)]
  have hpre : (Subtype.val : Metric.sphere (0 : E n) 1 → E n) ⁻¹' (Metric.sphere 0 1)ᶜ = ∅ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_not]
    exact x.2
  rw [hpre, measure_empty]

/-- `sphM n` has no atoms in dimension `n ≥ 2` (the cone over a point is a segment, which is
contained in a strict vector subspace and hence is Lebesgue-null). -/
theorem sphM_singleton (n : ℕ) (hn : 2 ≤ n) (ξ : E n) : sphM n {ξ} = 0 := by
  rw [sphM, Measure.map_apply continuous_subtype_val.measurable (measurableSet_singleton ξ)]
  by_cases hξ : ξ ∈ Sph n
  · have hpre : (Subtype.val : Metric.sphere (0 : E n) 1 → E n) ⁻¹' ({ξ} : Set (E n))
        = {⟨ξ, hξ⟩} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h => Subtype.ext h, fun h => by rw [h]⟩
    rw [hpre, Measure.toSphere_apply' _ (measurableSet_singleton _)]
    have himg : (Subtype.val : Metric.sphere (0 : E n) 1 → E n) '' {⟨ξ, hξ⟩} = {ξ} := by
      rw [Set.image_singleton]
    rw [himg]
    have hsub : Set.Ioo (0 : ℝ) 1 • ({ξ} : Set (E n)) ⊆ (ℝ ∙ ξ : Set (E n)) := by
      rintro y ⟨t, _ht, z, hz, rfl⟩
      exact Submodule.smul_mem _ t (Submodule.subset_span hz)
    have hne : (ℝ ∙ ξ : Submodule ℝ (E n)) ≠ ⊤ := by
      intro htop
      have hξ0 : ξ ≠ 0 := by
        intro h; rw [h] at hξ; simp [Sph] at hξ
      have h2 : Module.finrank ℝ (ℝ ∙ ξ) = Module.finrank ℝ (E n) := by
        rw [htop, finrank_top]
      rw [finrank_span_singleton hξ0, finrank_euclideanSpace_fin] at h2
      omega
    have hnull : volume (Set.Ioo (0 : ℝ) 1 • ({ξ} : Set (E n))) = 0 := by
      have hle : volume (Set.Ioo (0 : ℝ) 1 • ({ξ} : Set (E n))) ≤ 0 := by
        calc volume (Set.Ioo (0 : ℝ) 1 • ({ξ} : Set (E n)))
            ≤ volume (ℝ ∙ ξ : Set (E n)) := measure_mono hsub
          _ = 0 := Measure.addHaar_submodule volume (ℝ ∙ ξ) hne
      exact le_antisymm hle bot_le
    rw [hnull, mul_zero]
  · have hpre : (Subtype.val : Metric.sphere (0 : E n) 1 → E n) ⁻¹' ({ξ} : Set (E n)) = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hξ (h ▸ x.2)
    rw [hpre, measure_empty]

/-- `sigma n = (sphM n Set.univ)⁻¹ • sphM n`, by definition. -/
theorem sigma_eq_smul_sphM (n : ℕ) : sigma n = (sphM n Set.univ)⁻¹ • sphM n := rfl

theorem sigma_isProbabilityMeasure (n : ℕ) (hn : 2 ≤ n) :
    IsProbabilityMeasure (sigma n) := by
  rw [sigma_eq_smul_sphM]
  refine ⟨?_⟩
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (sphM_univ_ne_zero n (by omega)) (sphM_univ_ne_top n)

theorem sigma_compl_sphere (n : ℕ) : sigma n (Sph n)ᶜ = 0 := by
  rw [sigma_eq_smul_sphM, Measure.smul_apply, smul_eq_mul, sphM_compl_sphere n, mul_zero]

theorem sigma_singleton (n : ℕ) (hn : 2 ≤ n) (ξ : E n) : sigma n {ξ} = 0 := by
  rw [sigma_eq_smul_sphM, Measure.smul_apply, smul_eq_mul, sphM_singleton n hn ξ, mul_zero]

theorem sigma_pos (n : ℕ) {U : Set (E n)} (hU : IsOpen U)
    (hne : (U ∩ Sph n).Nonempty) : 0 < sigma n U := by
  rw [sigma_eq_smul_sphM, Measure.smul_apply, smul_eq_mul]
  apply ENNReal.mul_pos
  · rw [ENNReal.inv_ne_zero]
    rw [sphM_univ]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) measure_ball_lt_top.ne
  · rw [sphM_apply n hU.measurableSet]
    obtain ⟨ξ, hξU, hξS⟩ := hne
    exact Measure.IsOpenPosMeasure.open_pos (Subtype.val ⁻¹' U)
      (hU.preimage continuous_subtype_val) ⟨⟨ξ, hξS⟩, hξU⟩

/-- The visual measure seen from the origin is the normalised surface measure
(the Poisson density is identically `1` at the origin). -/
theorem visual_at_zero (n : ℕ) : visual n (0 : E n) = sigma n := by
  simp [visual, busemann, tpart]

theorem visualBasic (n : ℕ) (hn : 2 ≤ n) :
    MeasureTheory.IsProbabilityMeasure (Submission.Mostow.sigma n) ∧
    Submission.Mostow.sigma n (Submission.Mostow.Sph n)ᶜ = 0 ∧
    (∀ ξ : Submission.Mostow.E n, Submission.Mostow.sigma n {ξ} = 0) ∧
    (∀ U : Set (Submission.Mostow.E n), IsOpen U →
      (U ∩ Submission.Mostow.Sph n).Nonempty → 0 < Submission.Mostow.sigma n U) ∧
    Submission.Mostow.visual n (0 : Submission.Mostow.E n) = Submission.Mostow.sigma n := by
  exact ⟨sigma_isProbabilityMeasure n hn, sigma_compl_sphere n,
    fun ξ => sigma_singleton n hn ξ, fun U hU hne => sigma_pos n hU hne, visual_at_zero n⟩

end

end Work.Mostow
