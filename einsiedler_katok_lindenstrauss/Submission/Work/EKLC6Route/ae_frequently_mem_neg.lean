import Mathlib
import Submission.Work.EKLC6Route.Defs
import Submission.Work.EKLC6Core.ae_frequently_mem_of_pos_measure
import Submission.Work.EKLC6Core.covAlong

namespace Work.EKLC6Route

open MeasureTheory Filter Topology

theorem ae_frequently_mem_neg {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {t : Fin 3 → ℝ}
    (hmp : MeasureTheory.MeasurePreserving (Work.EKLC6Route.Tm t) μ μ)
    (hqerg : ∀ E : Set Work.EKLContract.X3, MeasurableSet E →
      (Work.EKLC6Route.Tm t) ⁻¹' E =ᵐ[μ] E → μ E = 0 ∨ μ Eᶜ = 0)
    {B : Set Work.EKLContract.X3} (hB : MeasurableSet B) (hpos : 0 < μ B) :
    ∀ᵐ x ∂μ, ∃ᶠ n in Filter.atTop, ((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag (-t) • y)^[n]) x ∈ B := by
  -- `aDiag (-t) • ·` is the inverse of `Tm t = aDiag t • ·`, and it preserves `μ`.
  have hS : MeasureTheory.MeasurePreserving
      (fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag (-t) • y) μ μ :=
    Work.EKLC6Core.measurePreserving_aDiag_neg hmp
  refine Work.EKLC6Core.ae_frequently_mem_of_pos_measure hS ?_ hB hpos
  -- Ergodicity transfers from `Tm t` to its (pointwise) inverse `aDiag (-t) • ·`.
  intro E hEm hEq
  exact hqerg E hEm (by
    have h1 := hmp.quasiMeasurePreserving.preimage_ae_eq hEq
    have hpre : Work.EKLC6Route.Tm t ⁻¹'
        ((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag (-t) • y) ⁻¹' E) = E := by
      ext x
      simp only [Set.mem_preimage]
      rw [Work.EKLContract.aDiag_neg_smul]
    simpa only [hpre] using h1.symm)

end Work.EKLC6Route
