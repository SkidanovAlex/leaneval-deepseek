import Mathlib.CategoryTheory.Countable
import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.SlotWord.slotFibre_pointwise
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.SlotWord.aemeasurable_fibreAmpEnergy`

The fibre amplitude energy
`q ↦ ∫_{abox |S| L} ‖tBamp χ_{B(u)} q.1 (Q_{B(u),j} (fibre of the slot piece at q.2)) j z‖²`
is a.e.-strongly-measurable for the product of Lebesgue measure on the sliding centre and Lebesgue
measure on the outside configurations, restricted to the outside set `slotOutside`.

Everything rests on one chain of `Measurable` assertions.  The fibre `y ↦ slotFibre S Ψ y` is
jointly measurable in `(y, z)` because it is `Φ` composed with the (measurable) slot reassembly;
FS's box projection `Q_{B,j}` — an algebraic expression in `Ψ` together with *one* parametric
integral over the box `B` — preserves joint measurability; and the windowed amplitude `tBamp` —
*one* parametric integral over `ℝ³` — again preserves it.  The two parametric integrals are handled
with `StronglyMeasurable.integral_prod_right'`, and the final `z`-integral over `abox` with the same
lemma, after which `Measurable` gives `AEStronglyMeasurable` for any measure.
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
set_option maxHeartbeats 2000000

variable {N : ℕ}

/-! ## 1. The window cutoff is continuous -/

theorem continuous_chiB (L d : ℝ) (u : ℝ³) : Continuous (chiB L d u) := by
  unfold chiB
  exact (chiScale_continuous L).mul
    ((chiScale_continuous (L * d)).comp (continuous_id.sub continuous_const))

/-! ## 2. The fibre is jointly measurable -/

/-- The configuration reassembled from an outside configuration `y` and an in-box configuration `z`
(transported along a bijection `e : SlotIn N S ≃ Fin |S|`). -/
def fibreEval (S : Finset (Fin N)) (e : SlotIn N S ≃ Fin S.card) :
    (SlotOut N S → ℝ³) × X S.card → X N :=
  fun p => slotComb S (fun i : SlotIn N S => p.2 (e i)) p.1

theorem measurable_fibreEval (S : Finset (Fin N)) (e : SlotIn N S ≃ Fin S.card) :
    Measurable (fibreEval S e) := by
  have h1 : Measurable (fun p : (SlotOut N S → ℝ³) × X S.card =>
      ((fun i : SlotIn N S => p.2 (e i)), p.1)) := by
    refine Measurable.prod ?_ ?_
    · rw [measurable_pi_iff]; intro i
      exact (measurable_pi_apply (e i)).comp measurable_snd
    · exact measurable_fst
  have h2 : Measurable (⇑(Equiv.piEquivPiSubtypeProd (fun i : Fin N => i ∈ S)
      (fun _ => ℝ³)).symm) :=
    measurable_piEquivPiSubtypeProd_symm (fun _ : Fin N => ℝ³) (fun i : Fin N => i ∈ S)
  exact h2.comp h1

/-- The transported fibre `(y, z) ↦ slotFibreState S e Φ y z` is jointly measurable. -/
theorem measurable_slotFibreState_pair (S : Finset (Fin N)) (e : SlotIn N S ≃ Fin S.card)
    {Φ : X N → ℝ} (hΦ : Measurable Φ) :
    Measurable (fun p : (SlotOut N S → ℝ³) × X S.card => slotFibreState S e Φ p.1 p.2) := by
  have h : Measurable (fun p : (SlotOut N S → ℝ³) × X S.card =>
      Φ (slotComb S (fun i : SlotIn N S => p.2 (e i)) p.1)) := by
    have hmap : Measurable (fun p : (SlotOut N S → ℝ³) × X S.card =>
        ((fun i : SlotIn N S => p.2 (e i)), p.1)) := by
      refine Measurable.prod ?_ ?_
      · rw [measurable_pi_iff]; intro i
        exact (measurable_pi_apply (e i)).comp measurable_snd
      · exact measurable_fst
    have h2 : Measurable (⇑(Equiv.piEquivPiSubtypeProd (fun i : Fin N => i ∈ S)
        (fun _ => ℝ³)).symm) :=
      measurable_piEquivPiSubtypeProd_symm (fun _ : Fin N => ℝ³) (fun i : Fin N => i ∈ S)
    exact hΦ.comp (h2.comp hmap)
  exact h

/-! ## 3. The FS box projection of the fibre is jointly measurable -/

theorem measurable_boxQInd_fibre (volA : ℝ) (A : Set ℝ³) (hA : MeasurableSet A)
    (S : Finset (Fin N)) (e : SlotIn N S ≃ Fin S.card) (j : Fin S.card)
    {Φ : X N → ℝ} (hΦ : Measurable Φ) :
    Measurable (fun p : (SlotOut N S → ℝ³) × X S.card =>
      boxQInd volA A j (slotFibreState S e Φ p.1) p.2) := by
  classical
  have hfib : Measurable (fun p : (SlotOut N S → ℝ³) × X S.card =>
      slotFibreState S e Φ p.1 p.2) := measurable_slotFibreState_pair S e hΦ
  have hind : Measurable (fun p : (SlotOut N S → ℝ³) × X S.card =>
      A.indicator (fun _ => (1 : ℝ)) (p.2 j)) :=
    (measurable_const.indicator hA).comp ((measurable_pi_apply j).comp measurable_snd)
  -- joint measurability of the box-mean integrand
  have hupd2 : Measurable (fun q : ((SlotOut N S → ℝ³) × X S.card) × ℝ³ =>
      (q.1.2, q.2)) :=
    Measurable.prodMk (measurable_snd.comp measurable_fst) measurable_snd
  have hupd : Measurable (fun q : ((SlotOut N S → ℝ³) × X S.card) × ℝ³ =>
      Function.update q.1.2 j q.2) :=
    (measurable_update' (X := fun _ : Fin S.card => ℝ³) (a := j)).comp hupd2
  have hjoint1 : Measurable (fun q : ((SlotOut N S → ℝ³) × X S.card) × ℝ³ =>
      slotFibreState S e Φ q.1.1 (Function.update q.1.2 j q.2)) :=
    hfib.comp (Measurable.prodMk (measurable_fst.comp measurable_fst) hupd)
  have hjoint : Measurable (fun q : ((SlotOut N S → ℝ³) × X S.card) × ℝ³ =>
      A.indicator (fun z => slotFibreState S e Φ q.1.1 (Function.update q.1.2 j z)) q.2) := by
    have hEq : (fun q : ((SlotOut N S → ℝ³) × X S.card) × ℝ³ =>
        A.indicator (fun z => slotFibreState S e Φ q.1.1 (Function.update q.1.2 j z)) q.2)
        = fun q => if q.2 ∈ A then slotFibreState S e Φ q.1.1 (Function.update q.1.2 j q.2)
            else 0 := by
      funext q; exact Set.indicator_apply _ _ _
    rw [hEq]
    exact Measurable.ite (hA.preimage measurable_snd) hjoint1 measurable_const
  have hSM := hjoint.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ³))
  have hint : Measurable (fun p : (SlotOut N S → ℝ³) × X S.card =>
      ∫ z in A, slotFibreState S e Φ p.1 (Function.update p.2 j z)) := by
    have h2 := hSM.measurable
    have heq : (fun p : (SlotOut N S → ℝ³) × X S.card =>
        ∫ z, A.indicator (fun z => slotFibreState S e Φ p.1 (Function.update p.2 j z)) z
          ∂(volume : Measure ℝ³))
        = fun p => ∫ z in A, slotFibreState S e Φ p.1 (Function.update p.2 j z) := by
      funext p; exact MeasureTheory.integral_indicator hA
    rw [heq] at h2
    exact h2
  have hboxP : Measurable (fun p : (SlotOut N S → ℝ³) × X S.card =>
      boxPInd volA A j (slotFibreState S e Φ p.1) p.2) := by
    have h : Measurable (fun p : (SlotOut N S → ℝ³) × X S.card =>
        (1 / volA) * (∫ z in A, slotFibreState S e Φ p.1 (Function.update p.2 j z)) *
          A.indicator (fun _ => (1 : ℝ)) (p.2 j)) :=
      (measurable_const.mul hint).mul hind
    convert h using 1
    funext p
    rw [boxPInd]
  have h : Measurable (fun p : (SlotOut N S → ℝ³) × X S.card =>
      A.indicator (fun _ => (1 : ℝ)) (p.2 j) * slotFibreState S e Φ p.1 p.2 -
        boxPInd volA A j (slotFibreState S e Φ p.1) p.2) :=
    (hind.mul hfib).sub hboxP
  convert h using 1
  funext p
  rw [boxQInd]

/-! ## 4. The windowed amplitude of the fibre is jointly measurable -/

theorem measurable_tBamp_fibre (L d : ℝ) (u : ℝ³) (volA : ℝ) (A : Set ℝ³) (hA : MeasurableSet A)
    (S : Finset (Fin N)) (e : SlotIn N S ≃ Fin S.card) (j : Fin S.card)
    {Φ : X N → ℝ} (hΦ : Measurable Φ) :
    Measurable (fun p : (ℝ³ × (SlotOut N S → ℝ³)) × X S.card =>
      Work.SmallBoxTBWord.tBamp (chiB L d u) p.1.1
        (boxQInd volA A j (slotFibreState S e Φ p.1.2)) j p.2) := by
  classical
  have hboxQ := measurable_boxQInd_fibre volA A hA S e j hΦ
  -- joint measurability of the amplitude integrand
  have hupd2 : Measurable (fun q : ((ℝ³ × (SlotOut N S → ℝ³)) × X S.card) × ℝ³ =>
      (q.1.2, q.2)) :=
    Measurable.prodMk (measurable_snd.comp measurable_fst) measurable_snd
  have hupd : Measurable (fun q : ((ℝ³ × (SlotOut N S → ℝ³)) × X S.card) × ℝ³ =>
      Function.update q.1.2 j q.2) :=
    (measurable_update' (X := fun _ : Fin S.card => ℝ³) (a := j)).comp hupd2
  have hboxQw : Measurable (fun q : ((ℝ³ × (SlotOut N S → ℝ³)) × X S.card) × ℝ³ =>
      boxQInd volA A j (slotFibreState S e Φ q.1.1.2) (Function.update q.1.2 j q.2)) :=
    hboxQ.comp (Measurable.prodMk (measurable_snd.comp (measurable_fst.comp measurable_fst)) hupd)
  have hinner : Continuous (fun q : ((ℝ³ × (SlotOut N S → ℝ³)) × X S.card) × ℝ³ =>
      (inner ℝ q.1.1.1 q.2 : ℂ)) :=
    Complex.continuous_ofReal.comp
      (Continuous.inner (continuous_fst.comp (continuous_fst.comp continuous_fst)) continuous_snd)
  have h1 : Measurable (fun q : ((ℝ³ × (SlotOut N S → ℝ³)) × X S.card) × ℝ³ =>
      (chiB L d u q.2 : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp
      ((continuous_chiB L d u).measurable.comp measurable_snd)
  have h2 : Measurable (fun q : ((ℝ³ × (SlotOut N S → ℝ³)) × X S.card) × ℝ³ =>
      Complex.exp (-(Complex.I * (inner ℝ q.1.1.1 q.2 : ℂ)))) :=
    (Complex.continuous_exp.comp ((continuous_const.mul hinner).neg)).measurable
  have h3 : Measurable (fun q : ((ℝ³ × (SlotOut N S → ℝ³)) × X S.card) × ℝ³ =>
      ((boxQInd volA A j (slotFibreState S e Φ q.1.1.2) (Function.update q.1.2 j q.2) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp hboxQw
  have hJ : Measurable (fun q : ((ℝ³ × (SlotOut N S → ℝ³)) × X S.card) × ℝ³ =>
      (chiB L d u q.2 : ℂ) * Complex.exp (-(Complex.I * (inner ℝ q.1.1.1 q.2 : ℂ))) *
        ((boxQInd volA A j (slotFibreState S e Φ q.1.1.2) (Function.update q.1.2 j q.2) : ℝ) : ℂ)) :=
    (h1.mul h2).mul h3
  have hSM := hJ.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ³))
  convert hSM.measurable using 1
  funext p
  simp only [Work.SmallBoxTBWord.tBamp]

/-! ## 5. The target -/

theorem aemeasurable_fibreAmpEnergy {N : ℕ} (L d : ℝ) (u : EuclideanSpace ℝ (Fin 3))
    (S : Finset (Fin N)) (Φ : Submission.BoseGases.X N → ℝ) (hΦ : Continuous Φ)
    (e : Work.PerSector.SlotIn N S ≃ Fin S.card) (j : Fin S.card) :
    MeasureTheory.AEStronglyMeasurable
      (fun q : EuclideanSpace ℝ (Fin 3) × (Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3)) =>
        ∫ z in Submission.BoseGases.abox S.card L,
          ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB L d u) q.1
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.dlBox L d u) j
              (Work.PerSector.slotFibreState S e (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) q.2)) j z‖ ^ 2)
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3))).restrict
          (Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S))) := by
  have hA : MeasurableSet (dlBox L d u) := measurableSet_dlBox L d u
  have hΦm : Measurable Φ := hΦ.measurable
  have hΨ : Measurable (slotPiece (dlBox L d u) S Φ) :=
    slotPiece_measurable (dlBox L d u) hA S hΦm
  have hamp := measurable_tBamp_fibre L d u (boxMass L d u) (dlBox L d u) hA S e j hΨ
  have hnorm : Measurable (fun p : (ℝ³ × (SlotOut N S → ℝ³)) × X S.card =>
      ‖Work.SmallBoxTBWord.tBamp (chiB L d u) p.1.1
        (boxQInd (boxMass L d u) (dlBox L d u) j
          (slotFibreState S e (slotPiece (dlBox L d u) S Φ) p.1.2)) j p.2‖ ^ 2) :=
    hamp.norm.pow_const 2
  have hSM := hnorm.stronglyMeasurable.integral_prod_right'
      (ν := (volume : Measure (X S.card)).restrict (abox S.card L))
  have hfin : Measurable (fun q : ℝ³ × (SlotOut N S → ℝ³) =>
      ∫ z in abox S.card L,
        ‖Work.SmallBoxTBWord.tBamp (chiB L d u) q.1
          (boxQInd (boxMass L d u) (dlBox L d u) j
            (slotFibreState S e (slotPiece (dlBox L d u) S Φ) q.2)) j z‖ ^ 2) :=
    hSM.measurable
  exact hfin.aestronglyMeasurable

end

end Work.SlotWord
