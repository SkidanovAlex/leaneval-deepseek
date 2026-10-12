import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.SlotWord.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SlotWord

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open BoseGases
open Work.PerSector

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

variable {N : ℕ}

/-! ## Helper lemmas -/

/-- **The transported fibre is jointly measurable.**  The map `(y, x) ↦ slotFibreState S e Φ y x`
is `Φ` composed with the (measurable) slot reassembly of `y` and of the fibre coordinate `x`
transported along the bijection `e`. -/
theorem measurable_slotFibreState_pair' {N : ℕ} (S : Finset (Fin N))
    (e : SlotIn N S ≃ Fin S.card) {Φ : Submission.BoseGases.X N → ℝ} (hΦ : Measurable Φ) :
    Measurable (fun p : (SlotOut N S → ℝ³) × Submission.BoseGases.X S.card =>
      slotFibreState S e Φ p.1 p.2) := by
  have hpair : Measurable (fun p : (SlotOut N S → ℝ³) × Submission.BoseGases.X S.card =>
      ((fun i : SlotIn N S => p.2 (e i)), p.1)) := by
    refine Measurable.prod ?_ ?_
    · rw [measurable_pi_iff]; intro i
      exact (measurable_pi_apply (e i)).comp measurable_snd
    · exact measurable_fst
  have h := (Work.PerSector.measurable_slotFibre_pair S hΦ).comp hpair
  simpa only [Function.comp_def, slotFibreState_apply] using h

/-- **The diagonal density is measurable.**  `qLHSden N L μ w w1` is built from the parametric box
integral `w1Fibre L w1 (x i) = ∫_{acube L} w1 (x i) y` (measurable in `x` because `w1` is jointly
measurable, by `StronglyMeasurable.integral_prod_right`) and the pair terms `x ↦ w (x p.1) (x p.2)`
(measurable because `w` is jointly measurable). -/
theorem measurable_qLHSden_fibre {N : ℕ} (L μ : ℝ)
    (w w1 : ℝ³ → ℝ³ → ℝ) (hwm : Measurable (Function.uncurry w))
    (hw1m : Measurable (Function.uncurry w1)) :
    Measurable (fun x : Submission.BoseGases.X N => qLHSden N L μ w w1 x) := by
  have hw1F (i : Fin N) :
      Measurable (fun x : Submission.BoseGases.X N => w1Fibre L w1 (x i)) := by
    have hφ : Measurable (fun p : Submission.BoseGases.X N × ℝ³ => (p.1 i, p.2)) :=
      Measurable.prodMk ((measurable_pi_apply i).comp measurable_fst) measurable_snd
    have hjoint : StronglyMeasurable
        (Function.uncurry (fun (x : Submission.BoseGases.X N) (y : ℝ³) => w1 (x i) y)) :=
      hw1m.stronglyMeasurable.comp_measurable hφ
    have h := StronglyMeasurable.integral_prod_right
      (ν := (volume : Measure ℝ³).restrict (acube L))
      (f := fun (x : Submission.BoseGases.X N) (y : ℝ³) => w1 (x i) y) hjoint
    simpa [w1Fibre] using h.measurable
  have hm_pair (p : Fin N × Fin N) :
      Measurable (fun x : Submission.BoseGases.X N => w (x p.1) (x p.2)) :=
    hwm.comp (Measurable.prodMk (measurable_pi_apply p.1) (measurable_pi_apply p.2))
  have hsum1 : Measurable (fun x : Submission.BoseGases.X N =>
      ∑ i : Fin N, w1Fibre L w1 (x i)) :=
    Finset.measurable_sum Finset.univ (fun i _ => hw1F i)
  have hsum2 : Measurable (fun x : Submission.BoseGases.X N =>
      ∑ p ∈ pairSet N, w (x p.1) (x p.2)) :=
    Finset.measurable_sum (pairSet N) (fun p _ => hm_pair p)
  change Measurable (fun x : Submission.BoseGases.X N =>
    - μ * (∑ i : Fin N, w1Fibre L w1 (x i))
      + (1 / 2 : ℝ) * (∑ p ∈ pairSet N, w (x p.1) (x p.2)))
  exact (measurable_const.mul hsum1).add (measurable_const.mul hsum2)

/-! ## The target -/

theorem aemeasurable_fibre_qLHSword {N : ℕ} (L μ : ℝ)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (S : Finset (Fin N)) (e : Work.PerSector.SlotIn N S ≃ Fin S.card)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨ : Measurable Ψ)
    (w w1 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (hwm : Measurable (Function.uncurry w)) (hw1m : Measurable (Function.uncurry w1)) :
    MeasureTheory.AEStronglyMeasurable
      (fun y : Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.qLHSword (N := S.card) L μ w w1
          (Work.PerSector.slotFibreState S e (Work.PerSector.slotPiece A S Ψ) y))
      ((MeasureTheory.volume : MeasureTheory.Measure
        (Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3))).restrict
        (Work.PerSector.slotOutside L A S)) := by
  have hΦ : Measurable (slotPiece A S Ψ) := slotPiece_measurable A hA S hΨ
  have hfib : Measurable (fun p : (SlotOut N S → ℝ³) × Submission.BoseGases.X S.card =>
      slotFibreState S e (slotPiece A S Ψ) p.1 p.2) :=
    measurable_slotFibreState_pair' S e hΦ
  have hD : Measurable (fun x : Submission.BoseGases.X S.card => qLHSden S.card L μ w w1 x) :=
    measurable_qLHSden_fibre (N := S.card) L μ w w1 hwm hw1m
  have hg : Measurable (fun p : (SlotOut N S → ℝ³) × Submission.BoseGases.X S.card =>
      (slotFibreState S e (slotPiece A S Ψ) p.1 p.2) ^ 2 * qLHSden S.card L μ w w1 p.2) :=
    (hfib.pow_const 2).mul (hD.comp measurable_snd)
  have hSM : StronglyMeasurable (fun y : SlotOut N S → ℝ³ =>
      ∫ x, (slotFibreState S e (slotPiece A S Ψ) y x) ^ 2 * qLHSden S.card L μ w w1 x
        ∂((volume : Measure (Submission.BoseGases.X S.card)).restrict (abox S.card L))) :=
    hg.stronglyMeasurable.integral_prod_right'
      (ν := (volume : Measure (Submission.BoseGases.X S.card)).restrict (abox S.card L))
  have hfin : Measurable (fun y : SlotOut N S → ℝ³ =>
      qLHSword (N := S.card) L μ w w1 (slotFibreState S e (slotPiece A S Ψ) y)) := by
    convert hSM.measurable using 1
    funext y
    rw [qLHSword_eq_integral_qLHSden]
  exact hfin.aestronglyMeasurable

end
end Work.SlotWord
