import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.Band.PotSplit
import Submission.Work.BoseFixB2.DvApriori.Band.PotIntegrable
import Submission.Work.BoseFixB2.Pot.potWordU_integrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Band.integrableOn_potOnePiece`

Integrability on the box of the one-body summand of the localised potential word,

    `x ↦ potOnePiece N g ℓ i x = ∫_y wLoc ℓ g 0 (xᵢ) y`,

for an **arbitrary integrable** numerator `g` (no positivity, no support/diluteness
hypothesis on `g` relative to `ℓ`).

This is the one-body companion of `DvApriori.integrableOn_wPairC_fibre` (which treats the
same fibre *restricted* to the cube `acube ℓ`); it is needed because `potOnePiece` is the
*unrestricted* fibre, but the argument is in fact the same and slightly shorter: by
`enorm_integral_le_lintegral_enorm` the Bochner integral of the fibre is dominated, for
every `x`, by the full-space lintegral `∫⁻_y ‖wPairC ℓ g (xᵢ) y‖ₑ` (using
`wLoc_zero_eq_wPairC`), so no truncation of the `y`-integral is needed.  Peeling the
`x`-integral over the box with `lintegral_coord_abox` reduces the whole thing to the
single-coordinate bound `cube_fibre_bound`, which is finite.

Note that the fibre is *not* pointwise bounded (the quotient `g/(χ⋆χ)_ℓ` may blow up), so
the argument has to go through the `∫⁻` language throughout.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace Work.BoseFixB2.Band

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem integrableOn_potOnePiece {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {g : EuclideanSpace ℝ (Fin 3) → ℝ} (hg : MeasureTheory.Integrable g) (i : Fin N) :
    MeasureTheory.IntegrableOn (Work.BoseFixB2.Band.potOnePiece N g ℓ i)
      (Submission.BoseGases.abox N ℓ) := by
  change MeasureTheory.Integrable
    (fun x : Submission.BoseGases.X N =>
      ∫ y : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.wLoc ℓ g 0 (x i) y)
    ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
      (Submission.BoseGases.abox N ℓ))
  have hℓnn : (0 : ℝ) ≤ ℓ := le_of_lt hℓ
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun x : Submission.BoseGases.X N =>
        ∫ y : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.wLoc ℓ g 0 (x i) y)
      (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)) :=
    Work.BoseFixB2.Pot.aesm_wLoc_integral_X (ℓ := ℓ) (u := 0) hg.aestronglyMeasurable i
  have hQmeas : MeasureTheory.AEStronglyMeasurable
      (fun a : EuclideanSpace ℝ (Fin 3) =>
        ∫⁻ y : EuclideanSpace ℝ (Fin 3), ‖Submission.BoseGases.wPairC ℓ g a y‖ₑ)
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) :=
    (AEMeasurable.lintegral_prod_right'
      (Work.BoseFixB2.Pot.aemeasurable_wPairC_prod hg.aestronglyMeasurable).enorm).aestronglyMeasurable
  refine ⟨haesm.restrict, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
  have hpt : ∀ x : Submission.BoseGases.X N,
      ‖(fun x : Submission.BoseGases.X N =>
        ∫ y : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.wLoc ℓ g 0 (x i) y) x‖ₑ
        ≤ ∫⁻ y : EuclideanSpace ℝ (Fin 3), ‖Submission.BoseGases.wPairC ℓ g (x i) y‖ₑ := by
    intro x
    refine le_trans (MeasureTheory.enorm_integral_le_lintegral_enorm
      (fun y : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.wLoc ℓ g 0 (x i) y)) ?_
    exact lintegral_mono (fun y => le_of_eq (congrArg (fun z => ‖z‖ₑ)
      (Work.BoseFixB2.Pot.wLoc_zero_eq_wPairC ℓ g (x i) y)))
  calc (∫⁻ x : Submission.BoseGases.X N,
        ‖(fun x : Submission.BoseGases.X N =>
          ∫ y : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.wLoc ℓ g 0 (x i) y) x‖ₑ
        ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
          (Submission.BoseGases.abox N ℓ)))
      ≤ (∫⁻ x : Submission.BoseGases.X N,
          (∫⁻ y : EuclideanSpace ℝ (Fin 3), ‖Submission.BoseGases.wPairC ℓ g (x i) y‖ₑ)
          ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
            (Submission.BoseGases.abox N ℓ))) := lintegral_mono hpt
    _ = ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
            (Submission.BoseGases.acube ℓ)) ^ (N - 1)
          * (∫⁻ a : EuclideanSpace ℝ (Fin 3),
              (∫⁻ y : EuclideanSpace ℝ (Fin 3), ‖Submission.BoseGases.wPairC ℓ g a y‖ₑ)
              ∂((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
                (Submission.BoseGases.acube ℓ))) :=
        Work.BoseFixB2.Pot.lintegral_coord_abox hℓ i hQmeas
    _ ≤ ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
            (Submission.BoseGases.acube ℓ)) ^ (N - 1)
          * ENNReal.ofReal (ℓ ^ 3 * ∫ z : EuclideanSpace ℝ (Fin 3), |g z|) :=
        mul_le_mul_right (Work.BoseFixB2.DvApriori.cube_fibre_bound hℓ hg) _
    _ < ⊤ := ENNReal.mul_lt_top
        (ENNReal.pow_lt_top (Submission.BoseGases.acube_lt_top ℓ hℓnn)) ENNReal.ofReal_lt_top

end Work.BoseFixB2.Band
