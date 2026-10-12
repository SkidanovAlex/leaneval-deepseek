import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Momentum.cubFT_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Strong measurability of the unit-cube Fourier symbol `cubFT`

`Work.BoseKinLoc.Momentum.cubFT` is the (real-form) Fourier symbol of the unit cube,

    `cubFT q = ∫_{acube 1} cos ⟪q,x⟫ dx`.

We record that it is **continuous**, hence strongly measurable.  The proof is the
standard parametric-integral argument: the integrand `(q, x) ↦ cos ⟪q,x⟫` is jointly
continuous, the domain `acube 1` is compact, and the measure is locally finite, so
`MeasureTheory.continuous_parametric_integral_of_continuous` applies.

Compactness of `acube 1` is obtained by transporting the coordinatewise compact product
`∏ᵢ [-1/2, 1/2]` along the linear isometry equivalence `EuclideanSpace.equiv (Fin 3) ℝ`
(which is a homeomorphism).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Momentum

open Submission.BoseGases

set_option autoImplicit false

/-- The unit cube `acube 1` is compact: it is the preimage under the linear isometry
equivalence `EuclideanSpace.equiv (Fin 3) ℝ` of the coordinatewise compact product
`∏ᵢ [-1/2, 1/2]`. -/
lemma isCompact_acube_one : IsCompact (Submission.BoseGases.acube (1 : ℝ)) := by
  have hcoord : IsCompact (Set.univ.pi (fun _ : Fin 3 => Set.Icc (-(1 : ℝ) / 2) (1 / 2))) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hpre : Submission.BoseGases.acube (1 : ℝ)
      = (EuclideanSpace.equiv (Fin 3) ℝ) ⁻¹'
        (Set.univ.pi fun _ : Fin 3 => Set.Icc (-(1 : ℝ) / 2) (1 / 2)) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
      Submission.BoseGases.mem_acube_iff]
    constructor <;> intro h i <;> simpa using h i
  rw [hpre]
  exact (Homeomorph.isCompact_preimage
    (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph).mpr hcoord

/-- `cubFT` is continuous, being the parametric integral of the jointly continuous
integrand `(q, x) ↦ cos ⟪q,x⟫` over the compact set `acube 1`. -/
lemma cubFT_continuous : Continuous (Work.BoseKinLoc.Momentum.cubFT) :=
  continuous_parametric_integral_of_continuous (μ := volume)
    (f := fun (q x : EuclideanSpace ℝ (Fin 3)) => Real.cos (inner ℝ q x))
    (by fun_prop) isCompact_acube_one

theorem sm_cubFT : MeasureTheory.StronglyMeasurable (Work.BoseKinLoc.Momentum.cubFT) := by
  exact cubFT_continuous.stronglyMeasurable

end Work.BoseKinLoc.Momentum
