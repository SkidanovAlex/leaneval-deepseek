import Mathlib.CategoryTheory.Countable
import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.SlotWord.centreFibre_norm_eq
import Submission.Work.SlotWord.dlThreshold_le_diagWeBAt_of_smallbox
import Submission.Work.SlotWord.integrable_fibre_cnPlusBoxInd
import Submission.Work.SlotWord.integrable_fibre_qLHSword
import Submission.Work.SlotWord.integrable_slotFibreMassReal_piece
import Submission.Work.SlotWord.slotSplit_lintegral_slotBox
import Submission.Work.SlotWord.tBdiagFormInd_slotFibre
import Submission.Work.SlotWord.wSmall1Pair_support_left
import Submission.Work.SlotWord.wSmallPair_support_left
import Submission.Work.SlotWord.wordFibreFactorisation_of_pieces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.SlotWord.aestronglyMeasurable_fibre_tBdiagFormInd`

The FS-faithful `p`-diagonal kinetic form of the *fibre* of a slot piece,
`y ↦ tBdiagFormInd L (dlBox L d u) (boxMass L d u) (chiB L d u) (fsKinCoeff c)
      (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y)`,
is a.e.-strongly-measurable for Lebesgue measure on the outside configurations restricted to the
outside set `slotOutside L (dlBox L d u) S`, for every **measurable** state `Φ`.

This is the measurability side condition of the spectral fibre factorisation
`Work.SlotWord.tBdiagFormInd_slotFibre` of the slot-word chapter: the `y`-integrand on the right of
that factorisation is a genuine measurable function of `y`, so the Fubini/dominated-convergence
arguments of the chapter apply to it.

## The proof

Unfolding `tBdiagFormInd` and `fibreAmpEnergy` (the latter is *definitionally* the
`j`-th box integral appearing in the former), the function is

    y ↦ Σ_{j : Fin |S|} (2π)⁻³ ∫_p  fsKinCoeff c ‖p‖ · (L³)⁻¹ · ∫_{z ∈ abox |S| L}
              ‖tBamp χ_B p (Q_{B,j}(fibre_y)) j z‖² ,

and each summand is a *Bochner* partial integral of a jointly strongly measurable function:

* the joint integrand `(p, z) ↦ ‖tBamp χ_B p (Q_{B,j}(fibre_y)) j z‖²` is measurable in
  `((p, y), z)` by `Work.SlotWord.measurable_tBamp_fibre` (the fibre and FS's box projection
  `Q_{B,j}` are jointly measurable, and `tBamp` — one parametric integral over `ℝ³` — preserves
  measurability); the `z`-integral over `abox |S| L` is handled by
  `StronglyMeasurable.integral_prod_right'`;
* multiplying by the (continuous, hence strongly measurable) kinetic symbol gives the joint
  `(p, y)`-integrand, and the *symmetric* Bochner partial integral
  `StronglyMeasurable.integral_prod_left'` produces `y ↦ ∫_p …` without ever having to exchange
  the product measure;
* the resulting functions of `y` are summed over `j` and the sum of strongly measurable functions
  is strongly measurable (`Finset.stronglyMeasurable_sum`); a strongly measurable function is
  a.e.-strongly-measurable for *every* measure, so no integrability or support condition is used.
-/

namespace Work.SlotWord

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open BoseGases
open Work.PerSector
open Work.UBBInputs8
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false

variable {N : ℕ}

/-- The FS spectral coefficient `r ↦ [r − c]₊²` is continuous. -/
private lemma continuous_fsKinCoeff' (c : ℝ) :
    Continuous (Submission.BoseGases.fsKinCoeff c) := by
  unfold Submission.BoseGases.fsKinCoeff
  exact ((continuous_id.sub continuous_const).max continuous_const).pow 2

/-- **The box amplitude energy of the fibre is strongly measurable in the sliding momentum.**
For a *measurable* state `Φ`, the map

    (p, y) ↦ ∫_{z ∈ abox |S| L} ‖tBamp χ_B p (Q_{B,j}(fibre_y)) j z‖²

is strongly measurable.  (This is `Work.SlotWord.aemeasurable_fibreAmpEnergy` with
`Measurable Φ` in place of `Continuous Φ`, and its conclusion strengthened from
a.e.-strongly-measurable to strongly measurable: the proof of that lemma only ever uses
measurability of `Φ`.) -/
private theorem stronglyMeasurable_fibreAmpEnergy_meas {N : ℕ} (L d : ℝ) (u : ℝ³)
    (S : Finset (Fin N)) {Φ : X N → ℝ} (hΦ : Measurable Φ)
    (e : SlotIn N S ≃ Fin S.card) (j : Fin S.card) :
    StronglyMeasurable
      (fun q : ℝ³ × (SlotOut N S → ℝ³) =>
        ∫ z in abox S.card L,
          ‖Work.SmallBoxTBWord.tBamp (chiB L d u) q.1
            (boxQInd (boxMass L d u) (dlBox L d u) j
              (slotFibreState S e (slotPiece (dlBox L d u) S Φ) q.2)) j z‖ ^ 2) := by
  have hA : MeasurableSet (dlBox L d u) := measurableSet_dlBox L d u
  have hΨ : Measurable (slotPiece (dlBox L d u) S Φ) := slotPiece_measurable _ hA S hΦ
  have hamp := measurable_tBamp_fibre L d u (boxMass L d u) (dlBox L d u) hA S e j hΨ
  have hnorm : Measurable (fun p : (ℝ³ × (SlotOut N S → ℝ³)) × X S.card =>
      ‖Work.SmallBoxTBWord.tBamp (chiB L d u) p.1.1
        (boxQInd (boxMass L d u) (dlBox L d u) j
          (slotFibreState S e (slotPiece (dlBox L d u) S Φ) p.1.2)) j p.2‖ ^ 2) :=
    hamp.norm.pow_const 2
  exact hnorm.stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure (X S.card)).restrict (abox S.card L))

theorem aestronglyMeasurable_fibre_tBdiagFormInd {N : ℕ} (L d c : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) (S : Finset (Fin N))
    {Φ : Submission.BoseGases.X N → ℝ} (hΦm : Measurable Φ)
    (e : Work.PerSector.SlotIn N S ≃ Fin S.card) :
    MeasureTheory.AEStronglyMeasurable
      (fun y : Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3) =>
        Work.UBBInputs8.tBdiagFormInd L (Submission.BoseGases.dlBox L d u)
          (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u)
          (Submission.BoseGases.fsKinCoeff c)
          (Work.PerSector.slotFibreState S e
            (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) y))
      ((MeasureTheory.volume : MeasureTheory.Measure
        (Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3))).restrict
        (Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S)) := by
  -- the box amplitude energy of the fibre, individually strongly measurable in `(p, y)`
  have hbox : ∀ j : Fin S.card, StronglyMeasurable
      (fun q : ℝ³ × (SlotOut N S → ℝ³) =>
        ∫ z in abox S.card L,
          ‖Work.SmallBoxTBWord.tBamp (chiB L d u) q.1
            (boxQInd (boxMass L d u) (dlBox L d u) j
              (slotFibreState S e (slotPiece (dlBox L d u) S Φ) q.2)) j z‖ ^ 2) :=
    fun j => stronglyMeasurable_fibreAmpEnergy_meas L d u S hΦm e j
  -- the kinetic symbol
  have hkin : Measurable (fun q : ℝ³ × (SlotOut N S → ℝ³) => fsKinCoeff c ‖q.1‖) :=
    (continuous_fsKinCoeff' c).measurable.comp continuous_fst.norm.measurable
  -- the joint `(p, y)`-integrand of the `j`-th summand
  have hjoint : ∀ j : Fin S.card, StronglyMeasurable
      (fun q : ℝ³ × (SlotOut N S → ℝ³) => fsKinCoeff c ‖q.1‖ * ((L ^ 3)⁻¹ *
        ∫ z in abox S.card L,
          ‖Work.SmallBoxTBWord.tBamp (chiB L d u) q.1
            (boxQInd (boxMass L d u) (dlBox L d u) j
              (slotFibreState S e (slotPiece (dlBox L d u) S Φ) q.2)) j z‖ ^ 2)) := by
    intro j
    exact hkin.stronglyMeasurable.mul ((hbox j).const_mul _)
  -- the Bochner partial integral over the momentum variable
  have hInt : ∀ j : Fin S.card, StronglyMeasurable
      (fun y : SlotOut N S → ℝ³ => ∫ p : ℝ³, fsKinCoeff c ‖p‖ * ((L ^ 3)⁻¹ *
        ∫ z in abox S.card L,
          ‖Work.SmallBoxTBWord.tBamp (chiB L d u) p
            (boxQInd (boxMass L d u) (dlBox L d u) j
              (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y)) j z‖ ^ 2)) := by
    intro j
    exact (hjoint j).integral_prod_left' (μ := (volume : Measure ℝ³))
  -- the sum over the fibre slots
  have hSum : AEStronglyMeasurable
      (fun y : SlotOut N S → ℝ³ => ∑ j : Fin S.card, ((2 * Real.pi) ^ 3)⁻¹ *
        ∫ p : ℝ³, fsKinCoeff c ‖p‖ * ((L ^ 3)⁻¹ *
          ∫ z in abox S.card L,
            ‖Work.SmallBoxTBWord.tBamp (chiB L d u) p
              (boxQInd (boxMass L d u) (dlBox L d u) j
                (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y)) j z‖ ^ 2))
      ((volume : Measure (SlotOut N S → ℝ³)).restrict (slotOutside L (dlBox L d u) S)) := by
    have hsum : AEStronglyMeasurable
        (∑ j ∈ Finset.univ, fun y : SlotOut N S → ℝ³ => ((2 * Real.pi) ^ 3)⁻¹ *
          ∫ p : ℝ³, fsKinCoeff c ‖p‖ * ((L ^ 3)⁻¹ *
            ∫ z in abox S.card L,
              ‖Work.SmallBoxTBWord.tBamp (chiB L d u) p
                (boxQInd (boxMass L d u) (dlBox L d u) j
                  (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y)) j z‖ ^ 2))
        ((volume : Measure (SlotOut N S → ℝ³)).restrict (slotOutside L (dlBox L d u) S)) :=
      Finset.aestronglyMeasurable_sum Finset.univ
        (fun j _ => (hInt j).aestronglyMeasurable.const_mul _)
    convert hsum using 1
    funext y
    simp only [Finset.sum_apply]
  -- compare with the unfolded definition of `tBdiagFormInd` at the fibre
  refine hSum.congr ?_
  filter_upwards with y
  simp only [tBdiagFormInd]

end

end Work.SlotWord
