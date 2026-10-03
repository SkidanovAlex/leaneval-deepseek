import Mathlib
import Submission.Work.KMTAreas.A7.Large.Defs

namespace Work.A7

open MeasureTheory
open Work.Analysis.IonescuWainger

/-! ## Integrability and measurability of the KMT cutoff `η`

`kmtEta` *is* the rescaled cutoff `η_{≤0} = etaCut kmtEta 0` (`zpow_zero`, `div_one`), so
`Work.KMTAreas.A7.contDiff_etaCut 0` and `Work.KMTAreas.A7.hasCompactSupport_etaCut 0` apply to
it directly.  A nonzero rescaling `ξ ↦ η (c * ξ)` then inherits integrability from
`MeasureTheory.Integrable.comp_mul_left'`. -/

lemma kmtEta_continuous_zero : Continuous Work.KMTContract.kmtEta := by
  have h0 : etaCut Work.KMTContract.kmtEta (0 : ℤ) = Work.KMTContract.kmtEta := by
    funext θ; simp [etaCut]
  have h := (Work.KMTAreas.A7.contDiff_etaCut (0 : ℤ)).continuous
  rwa [h0] at h

lemma kmtEta_hasCompactSupport_zero : HasCompactSupport Work.KMTContract.kmtEta := by
  have h0 : etaCut Work.KMTContract.kmtEta (0 : ℤ) = Work.KMTContract.kmtEta := by
    funext θ; simp [etaCut]
  have h := Work.KMTAreas.A7.hasCompactSupport_etaCut (0 : ℤ)
  rwa [h0] at h

lemma kmtEta_integrable_zero : Integrable Work.KMTContract.kmtEta :=
  kmtEta_continuous_zero.integrable_of_hasCompactSupport kmtEta_hasCompactSupport_zero

/-- Integrability of a nonzero rescaling of the KMT cutoff. -/
lemma integrable_kmtEta_rescale (c : ℝ) (hc : c ≠ 0) :
    Integrable (fun ξ : ℝ => Work.KMTContract.kmtEta (c * ξ)) :=
  kmtEta_integrable_zero.comp_mul_left' hc

/-- Measurability of a rescaling of the KMT cutoff. -/
lemma measurable_kmtEta_rescale (c : ℝ) :
    Measurable (fun ξ : ℝ => Work.KMTContract.kmtEta (c * ξ)) :=
  kmtEta_continuous_zero.measurable.comp (measurable_const.mul measurable_id)

/-- `varphiN N k₁` (the KMT bump `φ_N` at the continuous scale `k₁`, `Submission/Work/KMTAreas/A7/Large/Defs.lean`)
is measurable and Lebesgue-integrable on `ℝ`.

In each of the two cases `k₁ = 0` / `k₁ ≠ 0` it is a finite linear combination of *rescalings*
`ξ ↦ η (c * ξ)` of the KMT cutoff `η = Work.KMTContract.kmtEta`, with the *nonzero* real
constant `c = 2 ^ (logN N)` or `c = 2 ^ (logN N - k₁)` (`Real.rpow`, `0 < 2^x`).

Suggested route: `Work.KMTAreas.A7.contDiff_etaCut 0` + `Work.KMTAreas.A7.hasCompactSupport_etaCut 0`
give `Continuous`/`HasCompactSupport` for `kmtEta` (after `etaCut kmtEta 0 = kmtEta` by
`zpow_zero`, `div_one`), hence `Integrable kmtEta volume` by
`Continuous.integrable_of_hasCompactSupport`; `Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2)`
gives `c ≠ 0`, and `MeasureTheory.Integrable.comp_mul_left'` transports integrability to the
rescaling. Measurability is `Continuous.measurable` plus `split_ifs` and `fun_prop`
(give `fun_prop` the local hypothesis `Measurable kmtEta`). -/
theorem varphiN_integrable_measurable (N k₁ : ℕ) :
    MeasureTheory.Integrable (Work.KMTAreas.A7.varphiN N k₁) ∧
      Measurable (Work.KMTAreas.A7.varphiN N k₁) := by
  have hrpow : ∀ x : ℝ, (0 : ℝ) < (2 : ℝ) ^ x :=
    fun x => Real.rpow_pos_of_pos (by norm_num) x
  by_cases h : k₁ = 0
  · have hv : Work.KMTAreas.A7.varphiN N k₁
        = fun ξ : ℝ =>
            Work.KMTContract.kmtEta (((2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ)) * ξ) := by
      simp only [Work.KMTAreas.A7.varphiN, h, if_true]
    rw [hv]
    exact ⟨integrable_kmtEta_rescale _ (ne_of_gt (hrpow _)), measurable_kmtEta_rescale _⟩
  · have hv : Work.KMTAreas.A7.varphiN N k₁
        = fun ξ : ℝ =>
            Work.KMTContract.kmtEta
                (((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k₁ : ℝ))) * ξ)
              - Work.KMTContract.kmtEta
                (((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k₁ : ℝ) + 1)) * ξ) := by
      simp only [Work.KMTAreas.A7.varphiN, h, if_false]
    rw [hv]
    exact ⟨(integrable_kmtEta_rescale _ (ne_of_gt (hrpow _))).sub
             (integrable_kmtEta_rescale _ (ne_of_gt (hrpow _))),
           (measurable_kmtEta_rescale _).sub (measurable_kmtEta_rescale _)⟩

end Work.A7
