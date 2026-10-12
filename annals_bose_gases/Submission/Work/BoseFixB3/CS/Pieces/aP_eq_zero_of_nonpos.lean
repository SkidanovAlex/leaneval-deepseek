import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.Polar.polB_bilinear
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB3.CS.Pieces

open MeasureTheory
open scoped Real

/-- For `ℓ ≤ 0` the centred cube `acube ℓ` is a null set: it is empty when `ℓ < 0`,
and the singleton `{0}` when `ℓ = 0`. -/
lemma acube_volume_eq_zero (ℓ : ℝ) (hℓ : ℓ ≤ 0) :
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) (Submission.BoseGases.acube ℓ) = 0 := by
  rcases lt_or_eq_of_le hℓ with hlt | heq
  · have hemp : Submission.BoseGases.acube ℓ = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro y hy
      have hm : y (0 : Fin 3) ∈ Set.Icc (-ℓ / 2) (ℓ / 2) := hy 0
      obtain ⟨h1, h2⟩ := hm
      linarith
    rw [hemp, measure_empty]
  · rw [heq, Submission.BoseGases.acube_volume 0 le_rfl]
    simp

theorem aP_eq_zero_of_nonpos {N : ℕ} {ℓ : ℝ} (hℓ : ℓ ≤ 0) (i : Fin N)
    (Φ : Submission.BoseGases.X N → ℝ) (x : Submission.BoseGases.X N) :
    Submission.BoseGases.aP ℓ i Φ x = 0 := by
  have hμ : (volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
      (Submission.BoseGases.acube ℓ) = 0 := by
    rw [Measure.restrict_eq_zero]
    exact acube_volume_eq_zero ℓ hℓ
  unfold Submission.BoseGases.aP
  rw [show (∫ y in Submission.BoseGases.acube ℓ, Φ (Function.update x i y)) = 0 by
    rw [hμ]; simp]
  simp

end Work.BoseFixB3.CS.Pieces
