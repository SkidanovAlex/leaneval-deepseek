import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Q0Sector
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.chiRow_slotWeightMean`

The slot weight mean identity of the FS `Q₁` χ-row: the slot mean `PᵢΦ = aP ℓ i Φ` does not
depend on the value of the `i`-th coordinate (`Submission.BoseGases.aP_const_in_coord`), so
averaging the product `(PᵢΦ) · w(xᵢ)` over the `i`-th slot factors:

    `Pᵢ ((PᵢΦ) · w(·ᵢ)) = (PᵢΦ) · (ℓ³)⁻¹ ∫_{acube ℓ} w`.

Pointwise, with `y` the slot variable: `aP ℓ i Φ (update x i y) = aP ℓ i Φ x` and
`(update x i y) i = y`; the constant is then pulled out of the slot integral.
-/

namespace Work.BoseBoxFock

theorem chiRow_slotWeightMean {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦc : Continuous Φ) (w : EuclideanSpace ℝ (Fin 3) → ℝ) (x : Submission.BoseGases.X N) :
    Submission.BoseGases.aP ℓ i (fun z : Submission.BoseGases.X N => Submission.BoseGases.aP ℓ i Φ z * w (z i)) x
      = Submission.BoseGases.aP ℓ i Φ x * ((1 / ℓ ^ 3) * ∫ y in Submission.BoseGases.acube ℓ, w y) := by
  have hconst : ∀ y : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.aP ℓ i Φ (Function.update x i y) = Submission.BoseGases.aP ℓ i Φ x :=
    fun y => Submission.BoseGases.aP_const_in_coord hℓ i hΦc x y
  have key : (∫ y in Submission.BoseGases.acube ℓ,
        (fun z : Submission.BoseGases.X N => Submission.BoseGases.aP ℓ i Φ z * w (z i))
          (Function.update x i y))
      = ∫ y in Submission.BoseGases.acube ℓ, Submission.BoseGases.aP ℓ i Φ x * w y := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    simp [hconst y]
  rw [show Submission.BoseGases.aP ℓ i
        (fun z : Submission.BoseGases.X N => Submission.BoseGases.aP ℓ i Φ z * w (z i)) x
      = (1 / ℓ ^ 3) * ∫ y in Submission.BoseGases.acube ℓ,
          (fun z : Submission.BoseGases.X N => Submission.BoseGases.aP ℓ i Φ z * w (z i))
            (Function.update x i y) from rfl]
  rw [key, MeasureTheory.integral_const_mul]
  ring

end Work.BoseBoxFock
