import Mathlib
import Submission.Commons.MeasureTheory.integrable_indicator_prod_norm_sub
import Submission.Commons.MeasureTheory.integrable_smul_sub_of_locallyIntegrable

open MeasureTheory

namespace Commons.MeasureTheory

/-- **Integrability of a compactly supported kernel against a translated locally integrable
function.**  If `K` and `T` are continuous with compact support and `φ` is locally integrable for
the Lebesgue measure on `Fin d → ℂ`, then `(p₁, p₂) ↦ K p₁ * φ (p₂ - p₁) * T p₂` is integrable for
the product of Lebesgue measure with itself. -/
theorem integrable_mul_shift_sub_prod {d : ℕ} {K T φ : (Fin d → ℂ) → ℝ}
    (hKc : Continuous K) (hKs : HasCompactSupport K)
    (hTc : Continuous T) (hTs : HasCompactSupport T)
    (hφ : MeasureTheory.LocallyIntegrable φ MeasureTheory.volume) :
    MeasureTheory.Integrable
      (fun p : (Fin d → ℂ) × (Fin d → ℂ) => K p.1 * φ (p.2 - p.1) * T p.2)
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  classical
  obtain ⟨CK, hCK⟩ := hKs.exists_bound_of_continuous hKc
  obtain ⟨CT, hCT⟩ := hTs.exists_bound_of_continuous hTc
  have hCKn : 0 ≤ CK := le_trans (norm_nonneg _) (hCK 0)
  have hCTn : 0 ≤ CT := le_trans (norm_nonneg _) (hCT 0)
  -- Local integrability of `u ↦ φ (-u)` (a reflection of `φ`).
  have hV : MeasureTheory.LocallyIntegrable (fun u : Fin d → ℂ => φ (-u))
      (MeasureTheory.volume : Measure (Fin d → ℂ)) := by
    simpa [zero_sub] using locallyIntegrable_sub_self hφ (0 : Fin d → ℂ)
  -- Integrability of `‖φ (p₂ - p₁)‖` cut off to `tsupport K × tsupport T`.
  have hD0 := integrable_indicator_prod_norm_sub hV hKs.isCompact hTs.isCompact
  have hD : MeasureTheory.Integrable
      ((tsupport K ×ˢ tsupport T).indicator (fun p : (Fin d → ℂ) × (Fin d → ℂ) => ‖φ (p.2 - p.1)‖))
      ((MeasureTheory.volume : Measure (Fin d → ℂ)).prod (MeasureTheory.volume : Measure (Fin d → ℂ))) := by
    have hfun : (fun p : (Fin d → ℂ) × (Fin d → ℂ) => ‖(fun u : Fin d → ℂ => φ (-u)) (p.1 - p.2)‖)
        = (fun p : (Fin d → ℂ) × (Fin d → ℂ) => ‖φ (p.2 - p.1)‖) := by
      funext p; simp [neg_sub]
    rw [hfun] at hD0
    exact hD0
  -- The dominating integrable function.
  have hDom : MeasureTheory.Integrable
      (fun p : (Fin d → ℂ) × (Fin d → ℂ) =>
        CK * CT * ((tsupport K ×ˢ tsupport T).indicator (fun p => ‖φ (p.2 - p.1)‖) p))
      ((MeasureTheory.volume : Measure (Fin d → ℂ)).prod (MeasureTheory.volume : Measure (Fin d → ℂ))) :=
    hD.const_mul (CK * CT)
  -- A.e. strong measurability of the integrand.
  have hF_meas : AEStronglyMeasurable
      (fun p : (Fin d → ℂ) × (Fin d → ℂ) => K p.1 * φ (p.2 - p.1) * T p.2)
      ((MeasureTheory.volume : Measure (Fin d → ℂ)).prod (MeasureTheory.volume : Measure (Fin d → ℂ))) := by
    have h1 : AEStronglyMeasurable (fun p : (Fin d → ℂ) × (Fin d → ℂ) => K p.1)
        ((MeasureTheory.volume : Measure (Fin d → ℂ)).prod (MeasureTheory.volume : Measure (Fin d → ℂ))) :=
      (hKc.measurable.comp measurable_fst).aestronglyMeasurable
    have h3 : AEStronglyMeasurable (fun p : (Fin d → ℂ) × (Fin d → ℂ) => T p.2)
        ((MeasureTheory.volume : Measure (Fin d → ℂ)).prod (MeasureTheory.volume : Measure (Fin d → ℂ))) :=
      (hTc.measurable.comp measurable_snd).aestronglyMeasurable
    have hqmp : Measure.QuasiMeasurePreserving
        (fun p : (Fin d → ℂ) × (Fin d → ℂ) => p.2 - p.1)
        ((MeasureTheory.volume : Measure (Fin d → ℂ)).prod (MeasureTheory.volume : Measure (Fin d → ℂ)))
        (MeasureTheory.volume : Measure (Fin d → ℂ)) := by
      have h1q : Measure.QuasiMeasurePreserving
          (fun q : (Fin d → ℂ) × (Fin d → ℂ) => q.1 - q.2)
          ((MeasureTheory.volume : Measure (Fin d → ℂ)).prod (MeasureTheory.volume : Measure (Fin d → ℂ)))
          (MeasureTheory.volume : Measure (Fin d → ℂ)) :=
        quasiMeasurePreserving_sub _ _
      have h2q : Measure.QuasiMeasurePreserving
          (Prod.swap : (Fin d → ℂ) × (Fin d → ℂ) → (Fin d → ℂ) × (Fin d → ℂ))
          ((MeasureTheory.volume : Measure (Fin d → ℂ)).prod (MeasureTheory.volume : Measure (Fin d → ℂ)))
          ((MeasureTheory.volume : Measure (Fin d → ℂ)).prod (MeasureTheory.volume : Measure (Fin d → ℂ))) :=
        (Measure.measurePreserving_swap (μ := (MeasureTheory.volume : Measure (Fin d → ℂ)))
          (ν := (MeasureTheory.volume : Measure (Fin d → ℂ)))).quasiMeasurePreserving
      have := h1q.comp h2q
      simpa [Function.comp_def] using this
    have h2 : AEStronglyMeasurable (fun p : (Fin d → ℂ) × (Fin d → ℂ) => φ (p.2 - p.1))
        ((MeasureTheory.volume : Measure (Fin d → ℂ)).prod (MeasureTheory.volume : Measure (Fin d → ℂ))) :=
      hφ.aestronglyMeasurable.comp_quasiMeasurePreserving hqmp
    exact (h1.mul h2).mul h3
  refine Integrable.mono' hDom hF_meas ?_
  filter_upwards with p
  by_cases hp : p ∈ tsupport K ×ˢ tsupport T
  · rw [Set.indicator_of_mem hp]
    have hxn : 0 ≤ ‖φ (p.2 - p.1)‖ := norm_nonneg _
    calc ‖K p.1 * φ (p.2 - p.1) * T p.2‖
        = ‖K p.1‖ * ‖φ (p.2 - p.1)‖ * ‖T p.2‖ := by rw [norm_mul, norm_mul]
      _ ≤ CK * ‖φ (p.2 - p.1)‖ * CT :=
          mul_le_mul (mul_le_mul (hCK p.1) le_rfl hxn hCKn) (hCT p.2) (norm_nonneg _)
            (mul_nonneg hCKn hxn)
      _ = CK * CT * ‖φ (p.2 - p.1)‖ := by ring
  · rw [Set.indicator_of_notMem hp, mul_zero]
    simp only [Set.mem_prod, not_and_or] at hp
    rcases hp with hp | hp
    · rw [image_eq_zero_of_notMem_tsupport hp]; simp
    · rw [image_eq_zero_of_notMem_tsupport hp]; simp

end Commons.MeasureTheory
