import Mathlib.CategoryTheory.Countable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SlotWord.Trial
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.SlotWord.centreFibre_norm_eq` — the normalisation of the centred fibre

This is item (ii) of the (R1)(b) ledger of `Trial.lean`: the `L²`-mass of the *centred* fibre
`centreFibre S e (dlBox L d u) Ψ ((L·d)•u) y` over the corpus box `abox S.card (L·d)` equals the
fibre mass `slotFibreMassReal (dlBox L d u) S (slotPiece (dlBox L d u) S Ψ) y` of the slot piece.

The content is a pure translation/reindexing bookkeeping identity.  Write `B = dlBox L d u`,
`w = (L·d)•u` and `Φ = slotPiece B S Ψ`.  Then

* `centreFibre … x = Φ (slotComb S (fun i => x (e i) + w) y)`, so the integrand is
  `G (T x)` for `G z = ofReal ((Φ (slotComb S z y))²)` and the affine (hence
  measure-preserving) bijection `T : X |S| → (SlotIn N S → ℝ³)`,
  `T x = fun i => x (e i) + w`, a translation composed with the reindexing along `e`;
* both sides are supported on their own boxes — `centreFibre` vanishes off `abox |S| (L·d)`
  (because `dlBox L d u ⊆ w + acube (L·d)`), and `Φ (slotComb S · y)` vanishes off
  `slotBox B` — so the box restrictions may be dropped;
* the Bochner integral is the `toReal` of the `ℝ≥0∞`-valued `ofReal`-lintegral of the nonnegative
  square.

Assembling the three gives the stated identity.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SlotWord

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open BoseGases
open Work.PerSector

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

variable {N : ℕ}

/-- **The normalisation of the centred fibre**: the `abox |S| (L·d)`-`L²`-mass of the centred
fibre of the slot piece equals the fibre mass of the slot piece. -/
theorem centreFibre_norm_eq {N : ℕ} {L d : ℝ} (hL : 0 < L) (hd : 0 < d) (u : EuclideanSpace ℝ (Fin 3))
    (S : Finset (Fin N)) (e : Work.PerSector.SlotIn N S ≃ Fin S.card)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨ : Measurable Ψ)
    (y : Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3)) :
    (∫ x in Submission.BoseGases.abox S.card (L * d),
        (Work.SlotWord.centreFibre S e (Submission.BoseGases.dlBox L d u) Ψ ((L * d) • u) y x) ^ 2)
      = Work.PerSector.slotFibreMassReal (Submission.BoseGases.dlBox L d u) S
          (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Ψ) y := by
  set B : Set ℝ³ := Submission.BoseGases.dlBox L d u with hBdef
  set w : ℝ³ := (L * d) • u with hwdef
  set Φ : Submission.BoseGases.X N → ℝ := Work.PerSector.slotPiece B S Ψ with hΦdef
  have hBmeas : MeasurableSet B := by
    rw [hBdef]; exact Work.SmallBoxSliding.measurableSet_dlBox L d u
  have hPhi : Measurable Φ := by
    rw [hΦdef]; exact Work.PerSector.slotPiece_measurable B hBmeas S hΨ
  -- (i) measurability of the centred fibre
  have hcen : Measurable (fun x : Submission.BoseGases.X S.card =>
      Work.SlotWord.centreFibre S e B Ψ w y x) := by
    have h1 : Measurable (fun x : Submission.BoseGases.X S.card =>
        (fun i : Work.PerSector.SlotIn N S => x (e i) + w)) := by
      rw [measurable_pi_iff]
      intro i
      exact (measurable_pi_apply (e i)).add measurable_const
    have h2 : Measurable (fun z : Work.PerSector.SlotIn N S → ℝ³ => (z, y)) :=
      Measurable.prod measurable_id measurable_const
    have h3 : Measurable (fun z : Work.PerSector.SlotIn N S → ℝ³ =>
        Work.PerSector.slotComb S z y) :=
      (Work.PerSector.Work.PerSector.measurable_slotComb S).comp h2
    exact hPhi.comp (h3.comp h1)
  have hf_meas : Measurable (fun x : Submission.BoseGases.X S.card =>
      (Work.SlotWord.centreFibre S e B Ψ w y x) ^ 2) := hcen.pow_const 2
  -- (ii) the centred fibre vanishes off `abox S.card (L·d)`
  have hcen_supp : ∀ x : Submission.BoseGases.X S.card,
      x ∉ Submission.BoseGases.abox S.card (L * d) →
      (Work.SlotWord.centreFibre S e B Ψ w y x) ^ 2 = 0 := by
    intro x hx
    have h0 : Work.SlotWord.centreFibre S e B Ψ w y x = 0 := by
      rw [Work.SlotWord.centreFibre_apply, Work.PerSector.slotPiece]
      refine Set.indicator_of_notMem ?_ Ψ
      intro hmem
      have hz : ∀ i : Work.PerSector.SlotIn N S, x (e i) + w ∈ B :=
        ((Work.PerSector.slotComb_mem_slotSet_iff B S _ y).mp hmem).1
      apply hx
      rw [Submission.BoseGases.mem_abox_iff]
      intro j
      have hj : x j + w ∈ B := by
        have h := hz (e.symm j)
        rwa [Equiv.apply_symm_apply] at h
      have hb : (x j + w) - (L * d) • u ∈ Submission.BoseGases.acube (L * d) :=
        ((Submission.BoseGases.mem_dlBox_iff L d u (x j + w)).mp (hBdef ▸ hj)).2
      rw [hwdef] at hb
      simpa using hb
    rw [h0, pow_two, mul_zero]
  -- (iii) the measure-preserving transport `x ↦ fun i => x (e i) + w`
  let τme : (Submission.BoseGases.X S.card) ≃ᵐ (Submission.BoseGases.X S.card) :=
    MeasurableEquiv.addRight (fun _ : Fin S.card => w)
  let Eme : (Submission.BoseGases.X S.card) ≃ᵐ (Work.PerSector.SlotIn N S → ℝ³) :=
    MeasurableEquiv.piCongrLeft (fun _ : Work.PerSector.SlotIn N S => ℝ³) e.symm
  let T : (Submission.BoseGases.X S.card) ≃ᵐ (Work.PerSector.SlotIn N S → ℝ³) := τme.trans Eme
  have hTmp : MeasurePreserving (⇑T) volume volume := by
    have hτ : MeasurePreserving (⇑τme) volume volume := measurePreserving_add_right volume _
    have hE : MeasurePreserving (⇑Eme) volume volume :=
      measurePreserving_piCongrLeft (fun _ : Work.PerSector.SlotIn N S => (volume : Measure ℝ³)) e.symm
    exact hE.comp hτ
  have hTapply : ∀ x : Submission.BoseGases.X S.card,
      ⇑T x = fun i : Work.PerSector.SlotIn N S => x (e i) + w := by
    intro x
    funext i
    show ⇑Eme (⇑τme x) i = x (e i) + w
    have hkey := MeasurableEquiv.piCongrLeft_apply_apply (e := e.symm)
      (β := fun _ : Work.PerSector.SlotIn N S => ℝ³) (x := ⇑τme x) (i := e i)
    rw [Equiv.symm_apply_apply] at hkey
    rw [hkey]
    rfl
  -- the box restriction on the outside of `abox` is empty
  have hsupp_int : (∫ x in Submission.BoseGases.abox S.card (L * d),
        (Work.SlotWord.centreFibre S e B Ψ w y x) ^ 2)
      = ∫ x : Submission.BoseGases.X S.card, (Work.SlotWord.centreFibre S e B Ψ w y x) ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hcen_supp
  -- Bochner → `ℝ≥0∞`-lintegral
  have hlin : (∫ x : Submission.BoseGases.X S.card,
        (Work.SlotWord.centreFibre S e B Ψ w y x) ^ 2)
      = (∫⁻ x : Submission.BoseGases.X S.card,
          ENNReal.ofReal ((Work.SlotWord.centreFibre S e B Ψ w y x) ^ 2)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => sq_nonneg _)
      hf_meas.aestronglyMeasurable
  -- the change of variables
  have hcv : (∫⁻ x : Submission.BoseGases.X S.card,
        ENNReal.ofReal ((Work.SlotWord.centreFibre S e B Ψ w y x) ^ 2))
      = ∫⁻ z : Work.PerSector.SlotIn N S → ℝ³,
          ENNReal.ofReal ((Φ (Work.PerSector.slotComb S z y)) ^ 2) := by
    have key := hTmp.lintegral_map_equiv
      (fun z : Work.PerSector.SlotIn N S → ℝ³ =>
        ENNReal.ofReal ((Φ (Work.PerSector.slotComb S z y)) ^ 2)) T
    rw [key]
    apply lintegral_congr
    intro x
    rw [hTapply x, Work.SlotWord.centreFibre_apply]
  -- the support of the fibre in the in-box variables
  have hz_supp : (∫⁻ z : Work.PerSector.SlotIn N S → ℝ³,
        ENNReal.ofReal ((Φ (Work.PerSector.slotComb S z y)) ^ 2))
      = ∫⁻ z in Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S) B,
          ENNReal.ofReal ((Φ (Work.PerSector.slotComb S z y)) ^ 2) := by
    have hslotBox : MeasurableSet
        (Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S) B) := by
      rw [show Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S) B =
          ⋂ i : Work.PerSector.SlotIn N S,
            (fun z : Work.PerSector.SlotIn N S → ℝ³ => z i) ⁻¹' B from by
        ext z; simp [Work.PerSector.slotBox]]
      exact MeasurableSet.iInter (fun i => (measurable_pi_apply i) hBmeas)
    rw [← lintegral_indicator hslotBox]
    apply lintegral_congr
    intro z
    by_cases hz : z ∈ Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S) B
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz]
      have h0 : Φ (Work.PerSector.slotComb S z y) = 0 := by
        rw [hΦdef, Work.PerSector.slotPiece]
        refine Set.indicator_of_notMem ?_ Ψ
        intro hmem
        exact hz ((Work.PerSector.mem_slotBox_iff).mpr
          (fun i => ((Work.PerSector.slotComb_mem_slotSet_iff B S z y).mp hmem).1 i))
      rw [h0]
      simp
  calc
    (∫ x in Submission.BoseGases.abox S.card (L * d),
        (Work.SlotWord.centreFibre S e B Ψ w y x) ^ 2)
        = ∫ x : Submission.BoseGases.X S.card, (Work.SlotWord.centreFibre S e B Ψ w y x) ^ 2 :=
            hsupp_int
    _ = (∫⁻ x : Submission.BoseGases.X S.card,
          ENNReal.ofReal ((Work.SlotWord.centreFibre S e B Ψ w y x) ^ 2)).toReal := hlin
    _ = (∫⁻ z : Work.PerSector.SlotIn N S → ℝ³,
          ENNReal.ofReal ((Φ (Work.PerSector.slotComb S z y)) ^ 2)).toReal := by rw [hcv]
    _ = (∫⁻ z in Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S) B,
          ENNReal.ofReal ((Φ (Work.PerSector.slotComb S z y)) ^ 2)).toReal := by rw [hz_supp]
    _ = Work.PerSector.slotFibreMassReal B S Φ y := by
          rw [Work.PerSector.slotFibreMassReal, Work.PerSector.slotFibreMass]

end Work.SlotWord
