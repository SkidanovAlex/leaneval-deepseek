import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
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

namespace Work.SlotWord

noncomputable section

open Classical
open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open Work.PerSector
open Work.UBBInputs8
open Work.SmallBoxTBWord
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

variable {N : ℕ}

/-! ## 1. The pointwise value of `Q_{A,j}` of the slot fibre

`A = dlBox L d u`, `i₀ = (e.symm j).1`, `x₀ = slotComb S (ζ ∘ e) y`.  Because the outside
configuration `y` has all its coordinates outside `A`, the fibre of the slot piece at
`ζ_{j←w}` reduces on the support of the window to `η · 1_A(w) · Φ(x₀_{i₀←w})` with
`η ∈ {0,1}`; projecting out the box mean then produces exactly `Q_{A,i₀}Φ(x₀_{i₀←w})`.-/
theorem slotFibreState_boxQInd_update_if {N : ℕ} (L d : ℝ) (u : ℝ³) (S : Finset (Fin N))
    (Φ : X N → ℝ) (e : SlotIn N S ≃ Fin S.card) (j : Fin S.card) (ζ : X S.card)
    (y : SlotOut N S → ℝ³) (hy : y ∈ slotOutside L (dlBox L d u) S) (w : ℝ³) :
    boxQInd (boxMass L d u) (dlBox L d u) j
        (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y) (Function.update ζ j w)
      = (if ∀ i : SlotIn N S, e i ≠ j → ζ (e i) ∈ dlBox L d u then (1:ℝ) else 0)
        * (dlBox L d u).indicator (fun _ => (1:ℝ)) w
        * boxQ (boxMass L d u) (dlBox L d u) ((e.symm j).1) Φ
            (Function.update (slotComb S (fun i : SlotIn N S => ζ (e i)) y) ((e.symm j).1) w) := by
  set A := dlBox L d u with hA
  set i₀ : Fin N := (e.symm j).1 with hi₀def
  set x₀ : X N := slotComb S (fun i : SlotIn N S => ζ (e i)) y with hx₀
  set η : ℝ := if ∀ i : SlotIn N S, e i ≠ j → ζ (e i) ∈ A then (1:ℝ) else 0 with hη
  have hej : ∀ i : SlotIn N S, e i = j ↔ i = e.symm j := fun i => (Equiv.eq_symm_apply e).symm
  have hyA : ∀ jj : SlotOut N S, y jj ∉ A := by
    intro jj; rw [hA]; exact (mem_slotOutside_iff.mp hy).2 jj
  -- the slot-`j` update of `ζ` moves exactly the slot-`i₀` coordinate of `x₀`
  have hupd : ∀ w, slotComb S (fun i : SlotIn N S => (Function.update ζ j w) (e i)) y
      = Function.update x₀ i₀ w := by
    intro w
    rw [hx₀, hi₀def]
    funext i
    rw [slotComb_apply, Function.update_apply, slotComb_apply]
    by_cases hi : i ∈ S
    · rw [dif_pos hi, dif_pos hi, Function.update_apply]
      by_cases hii : i = (e.symm j).1
      · have hh : (⟨i, hi⟩ : SlotIn N S) = e.symm j := Subtype.ext hii
        rw [if_pos hii, if_pos (by rw [hh]; exact Equiv.apply_symm_apply e j)]
      · rw [if_neg hii]
        rw [if_neg]
        intro hh
        have hh' : (⟨i, hi⟩ : SlotIn N S) = e.symm j := by
          rw [← hh]; exact (Equiv.symm_apply_apply e ⟨i, hi⟩).symm
        exact hii (congrArg Subtype.val hh')
    · rw [dif_neg hi, dif_neg hi, if_neg]
      intro hh
      exact hi (by rw [hh]; exact (e.symm j).2)
  have hfib : ∀ w, slotFibreState S e (slotPiece A S Φ) y (Function.update ζ j w)
      = slotPiece A S Φ (Function.update x₀ i₀ w) := by
    intro w; rw [slotFibreState_apply, hupd w]
  -- membership in the slot set: `η` and `w ∈ A`
  have hmem : ∀ w, Function.update x₀ i₀ w ∈ slotSet A S
      ↔ (∀ i : SlotIn N S, e i ≠ j → ζ (e i) ∈ A) ∧ w ∈ A := by
    intro w
    rw [mem_slotSet_iff]
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · intro i hei
        have hne : i.1 ≠ i₀ := by
          intro hii
          exact hei ((hej i).mpr (Subtype.ext hii))
        have h1 := h i.1
        rw [Function.update_apply, if_neg hne, hx₀, slotComb_apply, dif_pos i.2] at h1
        exact h1.mpr i.2
      · have h1 := h i₀
        rw [Function.update_self] at h1
        exact h1.mpr (e.symm j).2
    · rintro ⟨hη', hw⟩ i
      rw [Function.update_apply]
      by_cases hii : i = i₀
      · rw [if_pos hii]
        exact ⟨fun _ => by rw [hii]; exact (e.symm j).2, fun _ => hw⟩
      · rw [if_neg hii, hx₀, slotComb_apply]
        by_cases his : i ∈ S
        · rw [dif_pos his]
          refine ⟨fun _ => his, fun _ => hη' ⟨i, his⟩ ?_⟩
          intro heq
          exact hii (congrArg Subtype.val ((hej ⟨i, his⟩).mp heq))
        · rw [dif_neg his]
          exact ⟨fun hc => absurd hc (hyA ⟨i, his⟩), fun hsi => absurd hsi his⟩
  have hpiece : ∀ w, slotPiece A S Φ (Function.update x₀ i₀ w)
      = η * A.indicator (fun _ => (1:ℝ)) w * Φ (Function.update x₀ i₀ w) := by
    intro w
    rw [slotPiece, Set.indicator_apply, hη]
    by_cases hQ : Function.update x₀ i₀ w ∈ slotSet A S
    · rw [if_pos hQ, if_pos ((hmem w).mp hQ).1,
        Set.indicator_of_mem ((hmem w).mp hQ).2 (fun _ => (1:ℝ))]
      ring
    · rw [if_neg hQ]
      by_cases hP : ∀ i : SlotIn N S, e i ≠ j → ζ (e i) ∈ A
      · rw [if_pos hP, Set.indicator_of_notMem (fun hw => hQ ((hmem w).mpr ⟨hP, hw⟩))
          (fun _ => (1:ℝ))]
        ring
      · rw [if_neg hP]; ring
  have hAmeas : MeasurableSet A := by rw [hA]; exact measurableSet_dlBox L d u
  have hind2 : A.indicator (fun _ => (1:ℝ)) w * A.indicator (fun _ => (1:ℝ)) w
      = A.indicator (fun _ => (1:ℝ)) w := by
    by_cases hw : w ∈ A
    · rw [Set.indicator_of_mem hw (fun _ => (1:ℝ))]; ring
    · rw [Set.indicator_of_notMem hw (fun _ => (1:ℝ))]; ring
  have hint : (∫ z in A, slotFibreState S e (slotPiece A S Φ) y (Function.update ζ j z))
      = η * ∫ z in A, Φ (Function.update x₀ i₀ z) := by
    have step1 : (∫ z in A, slotFibreState S e (slotPiece A S Φ) y (Function.update ζ j z))
        = ∫ z in A, η * Φ (Function.update x₀ i₀ z) := by
      refine MeasureTheory.setIntegral_congr_fun hAmeas (fun z hz => ?_)
      rw [hfib z, hpiece z, Set.indicator_of_mem hz (fun _ => (1:ℝ))]
      ring
    rw [step1, MeasureTheory.integral_const_mul]
  rw [show boxQInd (boxMass L d u) A j (slotFibreState S e (slotPiece A S Φ) y)
        (Function.update ζ j w)
      = A.indicator (fun _ => (1:ℝ)) w * slotFibreState S e (slotPiece A S Φ) y
          (Function.update ζ j w)
        - (1 / boxMass L d u)
          * (∫ z in A, slotFibreState S e (slotPiece A S Φ) y (Function.update ζ j z))
          * A.indicator (fun _ => (1:ℝ)) w by
        simp only [boxQInd, boxPInd, Function.update_idem, Function.update_self]]
  rw [show boxQ (boxMass L d u) A i₀ Φ (Function.update x₀ i₀ w)
      = Φ (Function.update x₀ i₀ w)
        - (1 / boxMass L d u) * ∫ z in A, Φ (Function.update x₀ i₀ z) by
        simp only [boxQ, boxP, Function.update_idem]]
  rw [hfib w, hpiece w, hint]
  rw [show A.indicator (fun _ => (1:ℝ)) w
        * (η * A.indicator (fun _ => (1:ℝ)) w * Φ (Function.update x₀ i₀ w))
      = (A.indicator (fun _ => (1:ℝ)) w * A.indicator (fun _ => (1:ℝ)) w)
        * (η * Φ (Function.update x₀ i₀ w)) by ring,
    hind2]
  ring

/-! ## 2. The windowed amplitude of the slot fibre at the delivered count -/

/-- **The windowed amplitude of the projected slot fibre.**  Since `χ_B` is carried by the box
`A = dlBox L d u` and the fibre's value at `ζ_{j←w}` is `η · 1_A(w)` times the fixed function
`boxQ volA A i₀ Φ` evaluated along the translate `x₀_{i₀←·}`, the `w`-integral defining
`tBamp` collapses to `η` times the amplitude of that fixed function. -/
theorem tBamp_slotFibreState_boxQInd {N : ℕ} (L d : ℝ) (hL : 0 < L) (hd : 0 < d)
    (u : ℝ³) (S : Finset (Fin N)) (Φ : X N → ℝ) (e : SlotIn N S ≃ Fin S.card)
    (j : Fin S.card) (p : ℝ³) (ζ : X S.card) (y : SlotOut N S → ℝ³)
    (hy : y ∈ slotOutside L (dlBox L d u) S) :
    tBamp (chiB L d u) p
        (boxQInd (boxMass L d u) (dlBox L d u) j
          (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y)) j ζ
      = (if ∀ i : SlotIn N S, e i ≠ j → ζ (e i) ∈ dlBox L d u then (1:ℂ) else 0)
        * tBamp (chiB L d u) p
            (boxQ (boxMass L d u) (dlBox L d u) ((e.symm j).1) Φ) ((e.symm j).1)
            (slotComb S (fun i : SlotIn N S => ζ (e i)) y) := by
  have hpt : ∀ z, boxQInd (boxMass L d u) (dlBox L d u) j
        (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y) (Function.update ζ j z)
      = (if ∀ i : SlotIn N S, e i ≠ j → ζ (e i) ∈ dlBox L d u then (1:ℝ) else 0)
        * (dlBox L d u).indicator (fun _ => (1:ℝ)) z
        * boxQ (boxMass L d u) (dlBox L d u) ((e.symm j).1) Φ
            (Function.update (slotComb S (fun i : SlotIn N S => ζ (e i)) y) ((e.symm j).1) z) :=
    fun z => slotFibreState_boxQInd_update_if L d u S Φ e j ζ y hy z
  have hχA : ∀ z, chiB L d u z * (dlBox L d u).indicator (fun _ => (1:ℝ)) z = chiB L d u z := by
    intro z
    by_cases hz : z ∈ dlBox L d u
    · rw [Set.indicator_of_mem hz, mul_one]
    · rw [Set.indicator_of_notMem hz, mul_zero]
      by_cases hcz : chiB L d u z = 0
      · rw [hcz]
      · exact absurd (chiB_support_mem hL hd u z hcz) hz
  have hχAc : ∀ z, (chiB L d u z : ℂ) * (((dlBox L d u).indicator (fun _ => (1:ℝ)) z : ℝ) : ℂ)
      = (chiB L d u z : ℂ) := by
    intro z
    rw [← Complex.ofReal_mul, hχA z]
  have hcast : (((if ∀ i : SlotIn N S, e i ≠ j → ζ (e i) ∈ dlBox L d u then (1:ℝ) else 0) : ℝ)
        : ℂ)
      = (if ∀ i : SlotIn N S, e i ≠ j → ζ (e i) ∈ dlBox L d u then (1:ℂ) else 0) := by
    split_ifs with h <;> norm_num
  rw [tBamp, tBamp]
  rw [show (if ∀ i : SlotIn N S, e i ≠ j → ζ (e i) ∈ dlBox L d u then (1:ℂ) else 0)
        * ∫ z, (chiB L d u z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
            (boxQ (boxMass L d u) (dlBox L d u) ((e.symm j).1) Φ
              (Function.update (slotComb S (fun i : SlotIn N S => ζ (e i)) y)
                ((e.symm j).1) z) : ℂ)
      = ∫ z, (if ∀ i : SlotIn N S, e i ≠ j → ζ (e i) ∈ dlBox L d u then (1:ℂ) else 0)
          * ((chiB L d u z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
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
  rw [show (chiB L d u z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
        ((if ∀ i : SlotIn N S, e i ≠ j → ζ (e i) ∈ dlBox L d u then (1:ℂ) else 0)
          * (((dlBox L d u).indicator (fun _ => (1:ℝ)) z : ℝ) : ℂ)
          * (boxQ (boxMass L d u) (dlBox L d u) ((e.symm j).1) Φ
              (Function.update (slotComb S (fun i : SlotIn N S => ζ (e i)) y)
                ((e.symm j).1) z) : ℂ))
      = ((chiB L d u z : ℂ) * (((dlBox L d u).indicator (fun _ => (1:ℝ)) z : ℝ) : ℂ))
        * ((if ∀ i : SlotIn N S, e i ≠ j → ζ (e i) ∈ dlBox L d u then (1:ℂ) else 0)
          * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
          * (boxQ (boxMass L d u) (dlBox L d u) ((e.symm j).1) Φ
              (Function.update (slotComb S (fun i : SlotIn N S => ζ (e i)) y)
                ((e.symm j).1) z) : ℂ)) by ring]
  rw [hχAc z]
  ring

/-! ## 3. The target -/

theorem fibreAmpDecay {N : ℕ} (L d : ℝ) (hL : 0 < L) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) (S : Finset (Fin N)) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (e : Work.PerSector.SlotIn N S ≃ Fin S.card) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (j : Fin S.card) (p : EuclideanSpace ℝ (Fin 3))
        (y : Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3)),
        y ∈ Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S →
        ∀ ζ ∈ Submission.BoseGases.abox S.card L,
        ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB L d u) p
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) j
              (Work.PerSector.slotFibreState S e
                (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) y)) j ζ‖
          ≤ C / (1 + ‖p‖) ^ 3 := by
  have hdec : ∀ i : Fin N, ∃ Ci : ℝ, 0 ≤ Ci ∧ ∀ x ∈ abox N L, ∀ i' : Fin N, ∀ p : ℝ³,
      ‖Work.SmallBoxTBWord.tBamp (chiB L d u) p (boxQ (boxMass L d u) (dlBox L d u) i Φ) i' x‖
        ≤ Ci / (1 + ‖p‖) ^ 3 :=
    fun i => Work.SmallBoxTBWord.tBamp_decay (N := N) (a := L) hL (contDiff_chiB hL hd u)
      (hasCompactSupport_chiB hL hd u)
      (boxQ_contDiff_of_compact (isCompact_dlBox hL hd u) (boxMass L d u) i hΦ)
  choose Cfun hCfun using hdec
  refine ⟨∑ i : Fin N, Cfun i, Finset.sum_nonneg (fun i _ => (hCfun i).1), ?_⟩
  intro j p y hy ζ hζ
  rw [tBamp_slotFibreState_boxQInd L d hL hd u S Φ e j p ζ y hy, norm_mul]
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
        * ‖Work.SmallBoxTBWord.tBamp (chiB L d u) p
            (boxQ (boxMass L d u) (dlBox L d u) ((e.symm j).1) Φ) ((e.symm j).1)
            (slotComb S (fun i : SlotIn N S => ζ (e i)) y)‖
      ≤ 1 * (Cfun ((e.symm j).1) / (1 + ‖p‖) ^ 3) :=
        mul_le_mul hη hb (norm_nonneg _) (by norm_num)
    _ = Cfun ((e.symm j).1) / (1 + ‖p‖) ^ 3 := one_mul _
    _ ≤ (∑ i : Fin N, Cfun i) / (1 + ‖p‖) ^ 3 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact Finset.single_le_sum (fun i _ => (hCfun i).1) (Finset.mem_univ _)

end

end Work.SlotWord
