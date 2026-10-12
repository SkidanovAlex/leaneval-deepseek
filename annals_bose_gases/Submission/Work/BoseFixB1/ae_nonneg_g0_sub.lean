import ChallengeDeps
import Submission.Work.BoseFixB1.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.ae_nonneg_g0_sub`

`g₀(x − y) ≥ 0` for a.e. pair `(x, y)` w.r.t. Lebesgue `×` Lebesgue on `ℝ³ × ℝ³`.

This is the two-variable version of `Submission.BoseGases.g0_nonneg_ae`
(`0 ≤ g₀` a.e. on `ℝ³`, which is FS's `w₀ ≤ 1` a.e. together with `v ≥ 0`).

The passage from one variable to two is by translation invariance of Lebesgue
measure: first `∀ᵐ (x,y), 0 ≤ g₀ x` (first projection of the product measure is
quasi-measure-preserving), and then the *measure-preserving* shear
`(x, y) ↦ (x − y, y)` (`MeasureTheory.measurePreserving_sub_prod`, whose
second component is the identity and which has "Jacobian `1`") transports this
a.e. statement to `∀ᵐ (x,y), 0 ≤ g₀ (x − y)`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem ae_nonneg_g0_sub {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) :
    ∀ᵐ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)
      ∂((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))),
      0 ≤ Submission.BoseGases.g0 v h (p.1 - p.2) := by
  have hg0 : ∀ᵐ x : E3, 0 ≤ Submission.BoseGases.g0 v h x :=
    Submission.BoseGases.g0_nonneg_ae hR hv hvrad hv_supp h
  -- on the product of Lebesgue measures, the first coordinate alone is a.e. `g₀ ≥ 0`
  have h1 : ∀ᵐ p : E3 × E3 ∂((MeasureTheory.volume : MeasureTheory.Measure E3).prod
      (MeasureTheory.volume : MeasureTheory.Measure E3)),
      0 ≤ Submission.BoseGases.g0 v h p.1 :=
    (MeasureTheory.Measure.quasiMeasurePreserving_fst
      (μ := (MeasureTheory.volume : MeasureTheory.Measure E3))
      (ν := (MeasureTheory.volume : MeasureTheory.Measure E3))).ae hg0
  -- the shear `(x, y) ↦ (x - y, y)` preserves `volume × volume`
  have hmp := measurePreserving_sub_prod
    (MeasureTheory.volume : MeasureTheory.Measure E3)
    (MeasureTheory.volume : MeasureTheory.Measure E3)
  exact hmp.quasiMeasurePreserving.ae h1

end Work.BoseFixB1

end
