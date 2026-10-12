import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.KinPSuperadd.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.KinPSuperadd

open MeasureTheory

/-- **Fubini over `Measure.pi` on two slots.**  For a sigma-finite measure `ν` on `ℝ³` and a
function `F` of the two slots which is integrable for the product measure `ν.prod ν`, the
integral over the two-fold product measure written as `Measure.pi (fun _ : Fin 2 => ν)`
(i.e. over the two particle slots) is the iterated integral.

This is the measure-transport core of `fubini_abox_two`: the measurable equivalence
`MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ³) ≃ᵐ ℝ³ × ℝ³`, `x ↦ (x 0, x 1)`, identifies
`Measure.pi (fun _ => ν)` with `ν.prod ν` (`measurePreserving_finTwoArrow`), and
`integral_prod` turns the product integral into the iterated one. -/
private lemma integral_pi_fin_two {ν : Measure (EuclideanSpace ℝ (Fin 3))} [SigmaFinite ν]
    (F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (hF : Integrable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => F p.1 p.2)
      (ν.prod ν)) :
    (∫ x : Fin 2 → EuclideanSpace ℝ (Fin 3), F (x 0) (x 1)
        ∂(Measure.pi (fun _ : Fin 2 => ν)))
      = ∫ z1, ∫ z2, F z1 z2 ∂ν ∂ν := by
  have hmp : MeasurePreserving (MeasurableEquiv.finTwoArrow)
      (Measure.pi (fun _ : Fin 2 => ν)) (ν.prod ν) :=
    measurePreserving_finTwoArrow ν
  have hemb : MeasurableEmbedding
      (MeasurableEquiv.finTwoArrow (α := EuclideanSpace ℝ (Fin 3))) :=
    MeasurableEquiv.measurableEmbedding _
  have h1 : (∫ x, F (x 0) (x 1) ∂(Measure.pi (fun _ : Fin 2 => ν)))
      = ∫ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3), F p.1 p.2 ∂(ν.prod ν) := by
    have h := hmp.integral_comp hemb
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => F p.1 p.2)
    simpa using h
  rw [h1]
  exact integral_prod
    (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => F p.1 p.2) hF

/-- Fubini for the two-particle centred box: a function depending on the two particle slots
integrates over `abox 2 s` as the iterated integral over `acube s` (⟺ the product of the two
restricted cube measures). -/
theorem fubini_abox_two {s : ℝ} (F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (hF : Integrable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => F p.1 p.2)
      (((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (Submission.BoseGases.acube s)).prod
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (Submission.BoseGases.acube s)))) :
    (∫ x in Submission.BoseGases.abox 2 s, F (x 0) (x 1))
      = ∫ z1 in Submission.BoseGases.acube s,
          ∫ z2 in Submission.BoseGases.acube s, F z1 z2 := by
  have hmeas : (volume : Measure (Submission.BoseGases.X 2)).restrict
        (Submission.BoseGases.abox 2 s)
      = Measure.pi (fun _ : Fin 2 =>
          (volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (Submission.BoseGases.acube s)) :=
    Submission.BoseGases.restrict_abox_eq_pi 2 s
  rw [hmeas]
  exact integral_pi_fin_two F hF

end Work.KinPSuperadd
