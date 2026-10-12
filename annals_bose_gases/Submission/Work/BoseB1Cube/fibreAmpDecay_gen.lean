import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.sbKinSliceSplitW
import Submission.Work.BoseFixB1S.win.chiSmallB_windowIntegrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB1Cube

noncomputable section

open Classical
open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open Work.PerSector
open Work.UBBInputs8
open Work.SmallBoxTBWord
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

variable {N : ℕ}

/-! ## 1. The windowed amplitude of the slot fibre, at an arbitrary window carried by the box

`Work.SlotWord.tBamp_slotFibreState_boxQInd` states the collapse of the `w`-integral defining
`tBamp` for the *specific* window `chiB L d u` (the corpus ball-window).  The cube chapter needs
the same collapse for an arbitrary window `χ` carried by the box `A = dlBox L d u` and only
`C³`-smooth (`chiSmallB` resp. its `C^∞` cube twin are not `ContDiff ℝ ⊤`).

The proof is a verbatim transcription: the *only* place where the window enters is the elementary
identity `χ z · 1_A(z) = χ z`, which holds precisely because `χ` is carried by `A`. -/

/-- **The windowed amplitude of the projected slot fibre, general window.**  Since `χ` is carried
by the box `A = dlBox L d u` and the fibre's value at `ζ_{j←w}` is `η · 1_A(w)` times the fixed
function `boxQ volA A i₀ Φ` evaluated along the translate `x₀_{i₀←·}`, the `w`-integral defining
`tBamp` collapses to `η` times the amplitude of that fixed function. -/
theorem tBamp_slotFibreState_boxQInd_gen {N : ℕ} (L d : ℝ) (hL : 0 < L) (hd : 0 < d)
    (u : E3) (S : Finset (Fin N)) (Φ : X N → ℝ) (e : SlotIn N S ≃ Fin S.card)
    (j : Fin S.card) (p : E3) (ζ : X S.card) (y : SlotOut N S → E3)
    {χ : E3 → ℝ} (hχsupp : ∀ z : E3, χ z ≠ 0 → z ∈ dlBox L d u)
    (hy : y ∈ slotOutside L (dlBox L d u) S) :
    tBamp χ p
        (boxQInd (boxMass L d u) (dlBox L d u) j
          (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y)) j ζ
      = (if ∀ i : SlotIn N S, e i ≠ j → ζ (e i) ∈ dlBox L d u then (1:ℂ) else 0)
        * tBamp χ p
            (boxQ (boxMass L d u) (dlBox L d u) ((e.symm j).1) Φ) ((e.symm j).1)
            (slotComb S (fun i : SlotIn N S => ζ (e i)) y) := by
  have hpt : ∀ z, boxQInd (boxMass L d u) (dlBox L d u) j
        (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y) (Function.update ζ j z)
      = (if ∀ i : SlotIn N S, e i ≠ j → ζ (e i) ∈ dlBox L d u then (1:ℝ) else 0)
        * (dlBox L d u).indicator (fun _ => (1:ℝ)) z
        * boxQ (boxMass L d u) (dlBox L d u) ((e.symm j).1) Φ
            (Function.update (slotComb S (fun i : SlotIn N S => ζ (e i)) y) ((e.symm j).1) z) :=
    fun z => Work.SlotWord.slotFibreState_boxQInd_update_if L d u S Φ e j ζ y hy z
  have hχA : ∀ z, χ z * (dlBox L d u).indicator (fun _ => (1:ℝ)) z = χ z := by
    intro z
    by_cases hz : z ∈ dlBox L d u
    · rw [Set.indicator_of_mem hz, mul_one]
    · rw [Set.indicator_of_notMem hz, mul_zero]
      by_cases hcz : χ z = 0
      · rw [hcz]
      · exact absurd (hχsupp z hcz) hz
  have hχAc : ∀ z, (χ z : ℂ) * (((dlBox L d u).indicator (fun _ => (1:ℝ)) z : ℝ) : ℂ)
      = (χ z : ℂ) := by
    intro z
    rw [← Complex.ofReal_mul, hχA z]
  have hcast : (((if ∀ i : SlotIn N S, e i ≠ j → ζ (e i) ∈ dlBox L d u then (1:ℝ) else 0) : ℝ)
        : ℂ)
      = (if ∀ i : SlotIn N S, e i ≠ j → ζ (e i) ∈ dlBox L d u then (1:ℂ) else 0) := by
    split_ifs with h <;> norm_num
  rw [tBamp, tBamp]
  rw [show (if ∀ i : SlotIn N S, e i ≠ j → ζ (e i) ∈ dlBox L d u then (1:ℂ) else 0)
        * ∫ z, (χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
            (boxQ (boxMass L d u) (dlBox L d u) ((e.symm j).1) Φ
              (Function.update (slotComb S (fun i : SlotIn N S => ζ (e i)) y)
                ((e.symm j).1) z) : ℂ)
      = ∫ z, (if ∀ i : SlotIn N S, e i ≠ j → ζ (e i) ∈ dlBox L d u then (1:ℂ) else 0)
          * ((χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
              (boxQ (boxMass L d u) (dlBox L d u) ((e.symm j).1) Φ
                (Function.update (slotComb S (fun i : SlotIn N S => ζ (e i)) y)
                  ((e.symm j).1) z) : ℂ))
      from (MeasureTheory.integral_const_mul _ _).symm]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with z
  rw [hpt z]
  have hB : (((if ∀ i : SlotIn N S, e i ≠ j → ζ (e i) ∈ dlBox L d u then (1:ℝ) else 0)
        * (dlBox L d u).indicator (fun _ => (1:ℝ)) z
        * boxQ (boxMass L d u) (dlBox L d u) ((e.symm j).1) Φ
            (Function.update (slotComb S (fun i : SlotIn N S => ζ (e i)) y)
              ((e.symm j).1) z) : ℝ) : ℂ)
      = (if ∀ i : SlotIn N S, e i ≠ j → ζ (e i) ∈ dlBox L d u then (1:ℂ) else 0)
        * (((dlBox L d u).indicator (fun _ => (1:ℝ)) z : ℝ) : ℂ)
        * (boxQ (boxMass L d u) (dlBox L d u) ((e.symm j).1) Φ
            (Function.update (slotComb S (fun i : SlotIn N S => ζ (e i)) y)
              ((e.symm j).1) z) : ℂ) := by
    rw [Complex.ofReal_mul, Complex.ofReal_mul, hcast]
  rw [hB]
  rw [show (χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
        ((if ∀ i : SlotIn N S, e i ≠ j → ζ (e i) ∈ dlBox L d u then (1:ℂ) else 0)
          * (((dlBox L d u).indicator (fun _ => (1:ℝ)) z : ℝ) : ℂ)
          * (boxQ (boxMass L d u) (dlBox L d u) ((e.symm j).1) Φ
              (Function.update (slotComb S (fun i : SlotIn N S => ζ (e i)) y)
                ((e.symm j).1) z) : ℂ))
      = ((χ z : ℂ) * (((dlBox L d u).indicator (fun _ => (1:ℝ)) z : ℝ) : ℂ))
        * ((if ∀ i : SlotIn N S, e i ≠ j → ζ (e i) ∈ dlBox L d u then (1:ℂ) else 0)
          * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
          * (boxQ (boxMass L d u) (dlBox L d u) ((e.symm j).1) Φ
              (Function.update (slotComb S (fun i : SlotIn N S => ζ (e i)) y)
                ((e.symm j).1) z) : ℂ)) by ring]
  rw [hχAc z]
  ring

/-! ## 2. The target -/

theorem fibreAmpDecay_gen {N : ℕ} (L d : ℝ) (hL : 0 < L) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) (S : Finset (Fin N)) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (e : Work.PerSector.SlotIn N S ≃ Fin S.card)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχc : ContDiff ℝ 3 χ) (hχs : HasCompactSupport χ)
    (hχsupp : ∀ z : EuclideanSpace ℝ (Fin 3), χ z ≠ 0 → z ∈ Submission.BoseGases.dlBox L d u) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (j : Fin S.card) (p : EuclideanSpace ℝ (Fin 3))
        (y : Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3)),
        y ∈ Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S →
        ∀ ζ ∈ Submission.BoseGases.abox S.card L,
        ‖Work.SmallBoxTBWord.tBamp χ p
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) j
              (Work.PerSector.slotFibreState S e
                (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) y)) j ζ‖
          ≤ C / (1 + ‖p‖) ^ 3 := by
  have hdec : ∀ i : Fin N, ∃ Ci : ℝ, 0 ≤ Ci ∧ ∀ x ∈ abox N L, ∀ i' : Fin N, ∀ p : E3,
      ‖Work.SmallBoxTBWord.tBamp χ p
          (boxQ (boxMass L d u) (dlBox L d u) i Φ) i' x‖
        ≤ Ci / (1 + ‖p‖) ^ 3 :=
    fun i => Work.BoseFixB1S.win.tBamp_decay_three (N := N) (a := L) hL hχc hχs
      (boxQ_contDiff_of_compact (isCompact_dlBox hL hd u) (boxMass L d u) i hΦ)
  choose Cfun hCfun using hdec
  refine ⟨∑ i : Fin N, Cfun i, Finset.sum_nonneg (fun i _ => (hCfun i).1), ?_⟩
  intro j p y hy ζ hζ
  rw [tBamp_slotFibreState_boxQInd_gen L d hL hd u S Φ e j p ζ y hχsupp hy, norm_mul]
  have hη : ‖(if ∀ i : SlotIn N S, e i ≠ j → ζ (e i) ∈ dlBox L d u then (1:ℂ) else 0)‖ ≤ 1 := by
    split <;> simp
  have hx : slotComb S (fun i : SlotIn N S => ζ (e i)) y ∈ abox N L := by
    rw [mem_abox_iff]
    intro i
    rw [slotComb_apply]
    by_cases hi : i ∈ S
    · rw [dif_pos hi]
      exact (mem_abox_iff S.card L ζ).mp hζ (e ⟨i, hi⟩)
    · rw [dif_neg hi]
      exact (mem_slotOutside_iff.mp hy).1 ⟨i, hi⟩
  have hb := (hCfun ((e.symm j).1)).2 _ hx ((e.symm j).1) p
  calc ‖(if ∀ i : SlotIn N S, e i ≠ j → ζ (e i) ∈ dlBox L d u then (1:ℂ) else 0)‖
        * ‖Work.SmallBoxTBWord.tBamp χ p
            (boxQ (boxMass L d u) (dlBox L d u) ((e.symm j).1) Φ) ((e.symm j).1)
            (slotComb S (fun i : SlotIn N S => ζ (e i)) y)‖
      ≤ 1 * (Cfun ((e.symm j).1) / (1 + ‖p‖) ^ 3) :=
        mul_le_mul hη hb (norm_nonneg _) (by norm_num)
    _ = Cfun ((e.symm j).1) / (1 + ‖p‖) ^ 3 := one_mul _
    _ ≤ (∑ i : Fin N, Cfun i) / (1 + ‖p‖) ^ 3 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact Finset.single_le_sum (fun i _ => (hCfun i).1) (Finset.mem_univ _)

end

end Work.BoseB1Cube
