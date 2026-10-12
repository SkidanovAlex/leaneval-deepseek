import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SlotWord.slotSplit_integral_slotBox
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.SlotWord.slotSplit_integral_fibre` — the slot splitting with the fibre reindexed

The companion of `Work.SlotWord.slotSplit_integral_slotBox` in which the in-box integral is
transported from the slot type `SlotIn N S` to the standard `S.card`-particle configuration space
`X S.card` along a bijection `e : SlotIn N S ≃ Fin S.card`, as required by the fibre
factorisation of the word (`Work.SlotWord.WordFibreFactorisation`).

**Statement.**  For a box `A ⊆ acube L`, a slot set `S`, a bijection `e` of the in-box slots with
`Fin S.card`, and an integrable real-valued `f : X N → ℝ` vanishing off the slot set
`slotSet A S` (i.e. the particles outside `S` lie outside `A` and the particles of `S` lie in
`A`), the `abox N L`-integral of `f` equals the iterated integral over the outside configurations
`y ∈ slotOutside L A S` and the in-box configurations `ζ ∈ abox S.card L` of
`f (slotComb S (ζ ∘ e) y)`.

**Proof.**  `Work.SlotWord.slotSplit_integral_slotBox` reduces the integral to the iterated
integral over `slotOutside L A S` and `slotBox (SlotIn N S) A`.  For fixed `y` the inner integral
is then (a) extended from the box `A` to the box `acube L` (the integrand vanishes off `slotBox A`
by the support hypothesis, and `A ⊆ acube L`), and (b) transported to `abox S.card L` along the
measure preserving reindexing `ζ ↦ ζ ∘ e` (`MeasurableEquiv.piCongrLeft`), which maps
`abox S.card L` onto `slotBox (acube L)`. -/

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

theorem slotSplit_integral_fibre {N : ℕ} (L : ℝ) (S : Finset (Fin N))
    (e : Work.PerSector.SlotIn N S ≃ Fin S.card) {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hAL : A ⊆ Submission.BoseGases.acube L)
    {f : Submission.BoseGases.X N → ℝ}
    (hint : MeasureTheory.IntegrableOn f (Submission.BoseGases.abox N L))
    (hsupp : ∀ x : Submission.BoseGases.X N, f x ≠ 0 → x ∈ Work.PerSector.slotSet A S) :
    ∫ x in Submission.BoseGases.abox N L, f x
      = ∫ y in Work.PerSector.slotOutside L A S,
          ∫ ζ in Submission.BoseGases.abox S.card L,
            f (Work.PerSector.slotComb S (fun k : Work.PerSector.SlotIn N S => ζ (e k)) y) := by
  classical
  -- The support hypothesis, split into the two halves used by the slot splitting.
  have hout : ∀ x : X N, f x ≠ 0 → ∀ j : SlotOut N S, x j ∉ A := by
    intro x hx j hc
    exact j.2 ((hsupp x hx j.1).mp hc)
  have hin : ∀ x : X N, f x ≠ 0 → ∀ i : SlotIn N S, x i ∈ A := by
    intro x hx i
    exact (hsupp x hx i.1).mpr i.2
  -- Step 1: the slot splitting over the slot type `SlotIn N S`.
  have hstep1 := slotSplit_integral_slotBox (N := N) L (B := A) S hAL
      hint.aestronglyMeasurable hint hout hin
  rw [hstep1]
  -- Step 2: the inner integral, pointwise in the outside configuration `y`.
  refine integral_congr_ae (Eventually.of_forall (fun y : SlotOut N S → ℝ³ => ?_))
  -- The reindexing `ζ ↦ ζ ∘ e`, mapping `abox S.card L` onto `slotBox (acube L)`.
  let T : (Fin S.card → ℝ³) ≃ᵐ (SlotIn N S → ℝ³) :=
    MeasurableEquiv.piCongrLeft (fun _ : SlotIn N S => ℝ³) e.symm
  have hmpT : MeasurePreserving (⇑T) volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : SlotIn N S => ℝ³) e.symm
  have hTapply : ∀ ζ : Fin S.card → ℝ³, ⇑T ζ = fun i : SlotIn N S => ζ (e i) := by
    intro ζ; funext i
    show (MeasurableEquiv.piCongrLeft (fun _ : SlotIn N S => ℝ³) e.symm) ζ i = ζ (e i)
    rw [MeasurableEquiv.coe_piCongrLeft]
    have key := Equiv.piCongrLeft_apply_apply
      (P := fun _ : SlotIn N S => ℝ³) (e := e.symm) ζ (e i)
    rw [Equiv.symm_apply_apply] at key
    exact key
  have hTimage : ⇑T '' (abox S.card L) = slotBox (ι := SlotIn N S) (acube L) := by
    ext z
    constructor
    · rintro ⟨ζ, hζ, rfl⟩
      rw [mem_abox_iff] at hζ
      rw [mem_slotBox_iff]
      intro i
      rw [hTapply ζ]
      exact hζ (e i)
    · intro hz
      refine ⟨fun k : Fin S.card => z (e.symm k), ?_, ?_⟩
      · rw [mem_abox_iff]
        intro k
        exact hz (e.symm k)
      · rw [hTapply]
        funext i
        simp only [Equiv.symm_apply_apply]
  -- (a) extend the inner integral from the box `A` to the box `acube L`.
  have h2a : ∫ z in slotBox (ι := SlotIn N S) (acube L), f (slotComb S z y)
      = ∫ z in slotBox (ι := SlotIn N S) A, f (slotComb S z y) := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (Work.PerSector.Work.PerSector.slotBox_measurable (ι := SlotIn N S) (acube_measurable L))
      (Work.PerSector.Work.PerSector.slotBox_mono (ι := SlotIn N S) hAL) ?_
    rintro z ⟨_, hzA⟩
    by_contra hne
    apply hzA
    rw [mem_slotBox_iff]
    intro i
    have hh := hsupp _ hne i.1
    rw [slotComb_apply, dif_pos i.2] at hh
    exact hh.mpr i.2
  -- (b) transport the inner integral along the reindexing `T`.
  have h2b : ∫ z in slotBox (ι := SlotIn N S) (acube L), f (slotComb S z y)
      = ∫ ζ in abox S.card L,
          f (slotComb S (fun k : SlotIn N S => ζ (e k)) y) := by
    have h := hmpT.setIntegral_image_emb T.measurableEmbedding
      (fun z => f (slotComb S z y)) (abox S.card L)
    rw [hTimage] at h
    rw [h]
    refine integral_congr_ae (Eventually.of_forall (fun ζ => ?_))
    simp only [hTapply ζ]
  show (∫ z in slotBox (ι := SlotIn N S) A, f (slotComb S z y))
      = ∫ ζ in abox S.card L, f (slotComb S (fun k : SlotIn N S => ζ (e k)) y)
  rw [← h2a, h2b]

end Work.SlotWord
