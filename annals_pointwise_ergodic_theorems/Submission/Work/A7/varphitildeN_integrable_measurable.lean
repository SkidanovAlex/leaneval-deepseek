import Mathlib
import Submission.Work.KMTAreas.A7.Large.Defs

namespace Work.A7

open MeasureTheory

/-- The rescaled KMT cutoff at scale `0` is the cutoff itself: `η_{≤0} = η`. -/
lemma etaCut_kmtEta_zero :
    Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (0 : ℤ)
      = Work.KMTContract.kmtEta := by
  funext θ
  simp [Work.Analysis.IonescuWainger.etaCut]

/-- The KMT cutoff `η` is continuous. -/
lemma kmtEta_continuous : Continuous Work.KMTContract.kmtEta := by
  have h := (Work.KMTAreas.A7.contDiff_etaCut (0 : ℤ)).continuous
  rwa [etaCut_kmtEta_zero] at h

/-- The KMT cutoff `η` has compact support. -/
lemma kmtEta_hasCompactSupport : HasCompactSupport Work.KMTContract.kmtEta := by
  have h := Work.KMTAreas.A7.hasCompactSupport_etaCut (0 : ℤ)
  rwa [etaCut_kmtEta_zero] at h

/-- The KMT cutoff `η` is Lebesgue-integrable on `ℝ`. -/
lemma kmtEta_integrable : MeasureTheory.Integrable Work.KMTContract.kmtEta :=
  kmtEta_continuous.integrable_of_hasCompactSupport kmtEta_hasCompactSupport

/-- A rescaling `ξ ↦ η (c * ξ)` of the KMT cutoff by a nonzero constant `c` is measurable and
Lebesgue-integrable on `ℝ`. -/
lemma kmtEta_rescale_integrable_measurable (c : ℝ) (hc : c ≠ 0) :
    MeasureTheory.Integrable (fun ξ : ℝ => Work.KMTContract.kmtEta (c * ξ)) ∧
      Measurable (fun ξ : ℝ => Work.KMTContract.kmtEta (c * ξ)) :=
  ⟨kmtEta_integrable.comp_mul_left' hc,
    kmtEta_continuous.measurable.comp (measurable_const.mul measurable_id)⟩

/-- `varphitildeN d N k₂` (the rescaled KMT bump `φ̃_N` at the continuous scale `k₂`,
`Submission/Work/KMTAreas/A7/Large/Defs.lean`) is measurable and Lebesgue-integrable on `ℝ`.

Same proof as for `varphiN`: it is a finite linear combination of rescalings `ξ ↦ η (c * ξ)` of
`η = Work.KMTContract.kmtEta` with `c = 2 ^ (d * logN N)` or `c = 2 ^ (d * (logN N - k₂))`
(`Real.rpow`), always nonzero since `2 ^ x > 0`.

Suggested route: `Work.KMTAreas.A7.contDiff_etaCut 0` + `Work.KMTAreas.A7.hasCompactSupport_etaCut 0`
(so `Integrable kmtEta volume` via `Continuous.integrable_of_hasCompactSupport`),
`Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2)`, `MeasureTheory.Integrable.comp_mul_left'`,
`Integrable.sub`, and `split_ifs` + `fun_prop` (with the local hypothesis `Measurable kmtEta`)
for measurability. -/
theorem varphitildeN_integrable_measurable (d N k₂ : ℕ) :
    MeasureTheory.Integrable (Work.KMTAreas.A7.varphitildeN d N k₂) ∧
      Measurable (Work.KMTAreas.A7.varphitildeN d N k₂) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hm : ∀ c : ℝ, Measurable (fun ξ : ℝ => Work.KMTContract.kmtEta (c * ξ)) := fun c =>
    kmtEta_continuous.measurable.comp (measurable_const.mul measurable_id)
  have hi : ∀ c : ℝ, c ≠ 0 →
      MeasureTheory.Integrable (fun ξ : ℝ => Work.KMTContract.kmtEta (c * ξ)) := fun c hc =>
    kmtEta_integrable.comp_mul_left' hc
  unfold Work.KMTAreas.A7.varphitildeN
  split_ifs with hk
  · exact ⟨hi _ (ne_of_gt (Real.rpow_pos_of_pos h2 _)), hm _⟩
  · exact ⟨(hi _ (ne_of_gt (Real.rpow_pos_of_pos h2 _))).sub
            (hi _ (ne_of_gt (Real.rpow_pos_of_pos h2 _))), (hm _).sub (hm _)⟩

end Work.A7
