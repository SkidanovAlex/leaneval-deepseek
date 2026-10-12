import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.PotAppPeel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.Pieces.integrable_prod_wPair_mul_bounded`

The product `(x,y) ↦ B x y · wPair ℓ h x y` is `L¹(ℝ³ × ℝ³)` whenever

* `h` is `L¹`, supported in the ball `‖z‖ ≤ R` with `R ≤ ℓ·chiR0` (the dilute
  regime), and
* `|B|` is a.e. bounded by a constant `C ≥ 0` and `B` is a.e. strongly
  measurable for the product measure.

The whole analytic content is `Submission.BoseGases.integrable_wPairU_full`
(`wPairU ℓ h ∈ L¹(ℝ³ × ℝ³)` in the dilute regime); the bounded factor `B` is
then removed by the a.e. domination
`‖B x y · wPair ℓ h x y‖ ≤ C · ‖wPairU ℓ h (x,y)‖` together with
`Submission.BoseGases.aesm_wPairU_prod` for the a.e. strong measurability.
-/

namespace Work.BoseFixB3.CS.Pieces

open MeasureTheory

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

theorem integrable_prod_wPair_mul_bounded {ℓ R : ℝ} (hℓ : 0 < ℓ)
    {h : EuclideanSpace ℝ (Fin 3) → ℝ} (hh : MeasureTheory.Integrable h)
    (hsupp : ∀ z : EuclideanSpace ℝ (Fin 3), R ≤ ‖z‖ → h z = 0)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0)
    {B : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hBm : MeasureTheory.AEStronglyMeasurable (Function.uncurry B)
      (MeasureTheory.volume.prod MeasureTheory.volume))
    {C : ℝ} (hC : 0 ≤ C)
    (hBb : ∀ᵐ z ∂(MeasureTheory.volume.prod MeasureTheory.volume), ‖B z.1 z.2‖ ≤ C) :
    MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        B z.1 z.2 * Submission.BoseGases.wPair ℓ h z.1 z.2)
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  -- `wPairU ℓ h ∈ L¹(ℝ³ × ℝ³)` in the dilute regime.
  have hw : MeasureTheory.Integrable (Submission.BoseGases.wPairU ℓ h)
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
    Submission.BoseGases.integrable_wPairU_full hℓ hh hsupp hRℓ
  have haesm_w : MeasureTheory.AEStronglyMeasurable (Submission.BoseGases.wPairU ℓ h)
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
    Submission.BoseGases.aesm_wPairU_prod hh
  -- a.e. strong measurability of the product
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        B z.1 z.2 * Submission.BoseGases.wPair ℓ h z.1 z.2)
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    have h := hBm.mul haesm_w
    refine h.congr ?_
    filter_upwards with z
    simp [Submission.BoseGases.wPairU, Function.uncurry]
  -- a.e. domination by the integrable function `C * ‖wPairU ℓ h‖`
  refine MeasureTheory.Integrable.mono' (hw.norm.const_mul C) haesm ?_
  filter_upwards [hBb] with z hz
  rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
  refine le_trans (mul_le_mul_of_nonneg_right hz (abs_nonneg _)) (le_of_eq ?_)
  simp [Submission.BoseGases.wPairU]

end Work.BoseFixB3.CS.Pieces
