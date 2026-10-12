import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.FarLatDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR.FarLat

theorem ofRealMulAeEq {W φ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hWnn : 0 ≤ᵐ[MeasureTheory.volume] W) :
    (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        ENNReal.ofReal (W p.1) * ENNReal.ofReal (W p.2) * ENNReal.ofReal (φ (p.1 - p.2)))
      =ᵐ[MeasureTheory.volume.prod MeasureTheory.volume]
      fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        ENNReal.ofReal (W p.1 * W p.2 * φ (p.1 - p.2)) := by
  -- `W` is a.e. nonnegative for the volume on `ℝ³`; pull that a.e. statement back along the two
  -- projections, which are quasi-measure-preserving for `volume.prod volume` (the corresponding
  -- Mathlib lemmas hold for *any* product measure, and in particular require no measurability
  -- of `W`).
  have h1 : ∀ᵐ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) ∂
      (MeasureTheory.volume.prod MeasureTheory.volume), 0 ≤ W p.1 :=
    (MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := MeasureTheory.volume)
      (ν := MeasureTheory.volume)).ae (p := fun z => 0 ≤ W z) hWnn
  have h2 : ∀ᵐ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) ∂
      (MeasureTheory.volume.prod MeasureTheory.volume), 0 ≤ W p.2 :=
    (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := MeasureTheory.volume)
      (ν := MeasureTheory.volume)).ae (p := fun z => 0 ≤ W z) hWnn
  -- Pointwise, `ENNReal.ofReal` is multiplicative on nonnegative arguments.
  filter_upwards [h1, h2] with p hp1 hp2
  rw [ENNReal.ofReal_mul (mul_nonneg hp1 hp2), ENNReal.ofReal_mul hp1]

end Work.BoseFixR.FarLat
