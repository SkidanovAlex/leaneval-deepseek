import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SlotWord.aemeasurable_fibre_qLHSword
import Submission.Work.SlotWord.exists_bound_fibre_qLHSword
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.SlotWord.integrable_fibre_qLHSword` — the fibre of the potential word is integrable

The potential word `qLHSword` at the fibre `slotFibreState S e (slotPiece A S Ψ) y` is the
`abox |S| L`-integral of `(fibre y x)² · qLHSden … x` (`Submission.BoseGases.
qLHSword_eq_integral_qLHSden`).  Integrability in `y` over the outside configurations
`slotOutside L A S` therefore rests on three independent facts:

* `aemeasurable_fibre_qLHSword` — *measurability*: the joint `(y, x)`-integrand is measurable
  (the fibre is `Ψ` composed with the reassembly `slotComb`, and `qLHSden` is built from the
  measurable `w`, `w1` and the fibre average `w1Fibre`), so the parametric integral is
  a.e.-strongly measurable (`StronglyMeasurable.integral_prod_right'`);
* `exists_bound_fibre_qLHSword` — *a uniform bound on the exterior*: for `y ∈ slotOutside L A S`
  every outside coordinate lies in `acube L` and outside `A ⊆ acube L`, so every reassembled
  configuration of the box `abox |S| L` lies in `abox N L`; the state and both kernels are bounded
  there, and `|qLHSden|` is bounded by `|μ|·|S|·Cw₁L³ + ½·#pairSet·Cw`;
* `volume_slotOutside_lt_top` — the outside-configuration set has *finite volume*, since it sits in
  the product of the one-particle cubes `acube L`.

This is the integrability side condition (R3) of the fibre factorisation `qLHSword_slotFibre`:
it is what makes the Bochner convention `∫ = 0` harmless in the `y`-`x` exchange.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SlotWord

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open Work.PerSector

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

variable {N : ℕ}

/-! ## 1. The exterior set is measurable and has finite volume -/

/-- The outside configurations `slotOutside L A S = {y | ∀ j, y j ∈ acube L \ A}` form a
measurable set: they are the slot box of `acube L ∩ Aᶜ`. -/
theorem measurableSet_slotOutside (L : ℝ) {A : Set ℝ³} (hA : MeasurableSet A)
    (S : Finset (Fin N)) : MeasurableSet (slotOutside L A S) := by
  rw [slotOutside, Work.PerSector.Work.PerSector.slotBox_inter_eq]
  exact (Work.PerSector.Work.PerSector.slotBox_measurable (acube_measurable L)).inter
    (Work.PerSector.Work.PerSector.slotBox_measurable hA.compl)

/-- **The outside configurations have finite volume**: they are contained in the slot box of the
one-particle cube `acube L`, whose volume is the finite product `∏_{j : SlotOut N S} L³`. -/
theorem volume_slotOutside_lt_top (L : ℝ) (hL : 0 ≤ L)
    (A : Set ℝ³) (S : Finset (Fin N)) :
    (volume : Measure (SlotOut N S → ℝ³)) (slotOutside L A S) < ⊤ := by
  have hsub : slotOutside L A S ⊆ slotBox (ι := SlotOut N S) (acube L) := by
    intro y hy
    exact (mem_slotOutside_iff.mp hy).1
  refine lt_of_le_of_lt (measure_mono hsub) ?_
  have hbox : slotBox (ι := SlotOut N S) (acube L)
      = Set.univ.pi (fun _ : SlotOut N S => acube L) := by
    ext z
    simp [slotBox]
  rw [hbox, volume_pi, Measure.pi_pi]
  refine ENNReal.prod_lt_top ?_
  intro i _
  rw [acube_volume L hL]
  exact ENNReal.ofReal_lt_top

/-! ## 2. The integrability -/

theorem integrable_fibre_qLHSword {N : ℕ} (L μ : ℝ) (hL : 0 < L)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube L)
    (S : Finset (Fin N)) (e : Work.PerSector.SlotIn N S ≃ Fin S.card)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨ : Measurable Ψ) {C : ℝ} (hC : 0 ≤ C)
    (hΨb : ∀ x ∈ Submission.BoseGases.abox N L, |Ψ x| ≤ C)
    (w w1 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (hwm : Measurable (Function.uncurry w)) (hw1m : Measurable (Function.uncurry w1))
    {Cw Cw1 : ℝ}
    (hw : ∀ x y : EuclideanSpace ℝ (Fin 3), |w x y| ≤ Cw)
    (hw1 : ∀ x : EuclideanSpace ℝ (Fin 3), ∀ y ∈ Submission.BoseGases.acube L, |w1 x y| ≤ Cw1) :
    MeasureTheory.Integrable
      (fun y : Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.qLHSword (N := S.card) L μ w w1
          (Work.PerSector.slotFibreState S e (Work.PerSector.slotPiece A S Ψ) y))
      ((MeasureTheory.volume : MeasureTheory.Measure
        (Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3))).restrict
        (Work.PerSector.slotOutside L A S)) := by
  obtain ⟨K, hK⟩ := exists_bound_fibre_qLHSword L μ hL hAc S e hC hΨb w w1 hw hw1
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun y : Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.qLHSword (N := S.card) L μ w w1
          (Work.PerSector.slotFibreState S e (Work.PerSector.slotPiece A S Ψ) y))
      ((MeasureTheory.volume : MeasureTheory.Measure
        (Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3))).restrict
        (Work.PerSector.slotOutside L A S)) :=
    aemeasurable_fibre_qLHSword L μ hA S e hΨ w w1 hwm hw1m
  have hbdd : ∀ᵐ y ∂(MeasureTheory.volume : MeasureTheory.Measure
      (Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3))).restrict
      (Work.PerSector.slotOutside L A S),
      ‖Submission.BoseGases.qLHSword (N := S.card) L μ w w1
        (Work.PerSector.slotFibreState S e (Work.PerSector.slotPiece A S Ψ) y)‖ ≤ K := by
    refine ae_restrict_of_forall_mem (measurableSet_slotOutside L hA S) (fun y hy => ?_)
    simpa using hK y hy
  exact IntegrableOn.of_bound (volume_slotOutside_lt_top L hL.le A S) hmeas K hbdd

end Work.SlotWord
